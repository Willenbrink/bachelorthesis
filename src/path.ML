(*  Title:      Pure/net.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Discrimination nets: a data structure for indexing items

From the book
    E. Charniak, C. K. Riesbeck, D. V. McDermott.
    Artificial Intelligence Programming.
    (Lawrence Erlbaum Associates, 1980).  [Chapter 14]

match_term no longer treats abstractions as wildcards; instead they match
only wildcards in patterns.  Requires operands to be beta-eta-normal.
*)

signature EQ = sig
  type value
  val eq : (value * value) -> bool
end

functor Path (V : EQ) =
struct
(* TODO is_first_order function in term! *)

fun >>= (x,f) = Option.map f x
infix 1 >>=

fun eq (x,y) = if pointer_eq (x,y) then true else V.eq (x,y)


datatype symbol =
    VarS
  | AtomS of string
datatype key =
    End of symbol
  | Fun of symbol * int * key (* function,number of children, key from that child onwards *)

fun sym_ord (VarS, VarS) = EQUAL
  | sym_ord (VarS, _) = LESS
  | sym_ord (_, VarS) = GREATER
  | sym_ord ((AtomS n1), (AtomS n2)) = fast_string_ord (n1,n2)

structure Stab = Table(type key = symbol val ord = sym_ord);
type value = V.value
type 'a content = 'a list Stab.table
datatype 'a tree = Node of 'a content * 'a tree list Stab.table
type T = V.value list * V.value tree

fun symbol_of_term t = case t of
          Const (n,_) => AtomS n
        | Free (n,_) => AtomS n
        | Bound i => AtomS (Name.bound i)
        | Var _ => VarS
        | Abs _ => VarS
        | _$_ => raise Fail "Invalid use of symbol_of_term"

fun key_of_term t : key list =
  let val (func, args) = Term.strip_comb t
      val sym = symbol_of_term func
  in
  case args of
    [] => [End sym]
  | args =>
      args
      |> map key_of_term
      |> map_index (fn (i,keys) => map (fn k => Fun(sym,i,k)) keys)
      |> flat
      |> (fn x => key_of_term func @ x)
  end

(* Trees/Nets are indexed by keys. Each key represents a single node.
   Each node contains content as 'a list Symtab and a recursive tree.
   There is no leaf as the tree can be an empty table.
   There is no empty key.
   TODO Lookup functions preserve order in items stored at same level?
*)

val empty_node = Node (Stab.empty, Stab.empty)
val empty = ([],empty_node);
fun is_empty ([],_) = true
  | is_empty _ = false

(*** Insertion ***)

exception INSERT;       (*duplicate item in the net*)

fun append_sym eq (k,v) table =
  let fun update vs =
    if member eq vs v
    then raise INSERT
    else v::vs
  in Stab.map_default (k, []) update table end

fun nth_map_default (index : int) (f : 'a -> 'a) (default : 'a) (xs : 'a list) : 'a list =
     case (xs,index) of
      ([],0) => [f default]
    | ([],i) => default :: nth_map_default (i-1) f default []
    | (x::xs,0) => f x :: xs
    | (x::xs,i) => x :: nth_map_default (i-1) f default xs

(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for items.
  TODO inefficient approach: Insert each key independently.
  For e.g. f(g(h(x,y))) path from root to h is repeated thrice, for h,x,y
  TODO perhaps drop subkeys from keylist? For f(g(x)) only save <f,1,g,1> = x? Why doesn't that work?
*)
fun insert_one eq (key, v) (Node (con,tree)) = case key of
      End n => Node (append_sym eq (n,v) con, tree)
    | Fun (name,index,key) =>
        let fun ins tree = insert_one eq (key,v) tree
            fun ins_list xs = nth_map_default index ins empty_node xs
            fun ins_symtab f tree = Stab.map_default (name,[]) f tree
        in Node (con, ins_symtab ins_list tree) end

(* Insert a reference directly. Only internal usage *)
fun insert_ref_safe eq (keys,term_ref) net =
  Library.foldl (fn (acc,k) => insert_one eq (k, term_ref) acc) (net,keys)
  handle INSERT => net

fun insert eq (t,v) (values,tree) =
  let 
    val values = v :: values
    val tree = Library.foldl (fn (acc,k) => insert_one eq (k, v) acc) (tree, key_of_term t)
  in
  (values,tree)
  end

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;


(*** Deletion ***)

exception DELETE;       (*missing item in the net*)

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent. TODO Collapses the net if possible?
  eq is the equality test for items. *)
fun delete_one eq (key, v) (Node (con,tree)) =
  let fun rem content = if member eq content v then remove eq v content
                        else raise DELETE in
  case key of
      End n => Node (Stab.map_default (n,[]) rem con, tree)
    | Fun (name,index,key) =>
           delete_one eq (key,v)
        |> (fn f => nth_map index (fn xs => f xs))
        |> (fn x => Stab.map_default (name,[]) x tree)
        |> (fn x => Node (con, x))
   end

fun delete eq (t, v) (values, tree) =
  let
    (* TODO The value is saved at multiple locations. If some keys are removed from the list
      those will not be deleted from the tree but will be from the values *)
    val values = if member eq values v then remove eq v values else raise DELETE
    val tree = Library.foldl (fn (acc,k) => delete_one eq (k, v) acc) (tree, key_of_term t)
  in
  (values,tree)
  end

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;


(*** Retrieval functions ***)
fun content_node eq tree =
  let fun aux (Node (con,tree)) =
    let val con_fst =
          con |> Stab.dest 
              |> maps snd
        val con_snd =
          tree |> Stab.dest
               |> maps snd
               |> maps aux
    in con_fst @ con_snd end
  in
  aux tree
  |> distinct (op eq)
  end

fun content (values,_) = values

datatype query_type = Variants | Generalisations | Instances | Unifiables
datatype 'a term_set = List of 'a list
                     | Intersection of 'a term_set list
                     | Union of 'a term_set list
                     | NoConstraint
exception NoConstraint_exn

fun compute_set term_set = case term_set of
    List xs => xs
  | Intersection [] => raise Fail "Empty intersect is undefined"
  | Intersection (x::xs) =>
      let fun f x acc = inter eq (compute_set x) acc handle NoConstraint_exn => acc
      in fold f xs (compute_set x) end
  | Union xs => fold (fn x => fn acc => compute_set x @ acc) xs []
  | NoConstraint => raise NoConstraint_exn

fun query query_type term (values,(Node (con,tree))) =
  let
    fun symbols sym = Stab.lookup_list con sym |> List
    fun  handle_var () = case query_type of
        Variants => symbols VarS
      | Instances => NoConstraint
      | Generalisations => symbols VarS
      | Unifiables => NoConstraint
    fun handle_sym sym = case query_type of
        Variants => symbols sym
      | Instances => symbols sym
      | Generalisations => Union [symbols VarS, symbols sym]
      | Unifiables => Union [symbols VarS, symbols sym]
    fun query_args func args =
      let
        val list = Stab.lookup_list tree func
        fun arg_to_terms (index, arg) =
          query query_type arg (values, (nth list index))
          handle Subscript => List []
      in
      Intersection (map_index arg_to_terms args)
      end
    fun handle_func func args = case query_type of
        Variants => query_args func args
      | Instances => query_args func args
      | Generalisations => Union [symbols VarS, query_args func args]
      | Unifiables => Union [symbols VarS, query_args func args]
  in
  case strip_comb term of
    (Var _,_) => handle_var ()
  | (Abs _,_) => handle_var ()
  | (sym,[]) => handle_sym (symbol_of_term sym)
  | (func,args) => handle_func (symbol_of_term func) args
  end

fun query_wrapper query_type t (values,node) =
  query query_type t (values,node)
  |> compute_set
  |> distinct (op eq)
  handle NoConstraint_exn => values

fun lookup tree t = query_wrapper Variants t tree
fun instances tree t = query_wrapper Instances t tree
fun generalisations tree t = query_wrapper Generalisations t tree
fun unifiables tree t = query_wrapper Unifiables t tree

fun dest (Node (con,tree)) =
  let
    val content_alist =
      Stab.dest con
      |> maps (fn (k,vs) => map (fn v => (End k,v)) vs)
    val tree_alist =
      Stab.dest tree
      |> maps (fn (sym,vs) => map_index (fn (i,v) => (sym,i,v)) vs)
      |> maps (fn (sym,ind,value) => dest value |> map (fn (k,v) => (Fun (sym,ind,k),v)))
  in content_alist @ tree_alist end

(* FIXME non-canonical merge order!?! *)
fun merge eq (values1,tree1) (values2,tree2) =
  let
    val values = union (op eq) values1 values2
    val tree = fold (fn t => insert_ref_safe eq t) (dest tree2 |> map (fn (k,v) => ([k],v))) tree1
  in
  (values, tree)
  end

(* Useful for what exactly?
fun dot_of_node (node as Node(con,tree)) =
  let
    fun print_content i con =
    fun print_node prev_i curr_i (Node(con,tree)) =
      string_of_int prev_i ^ "->" ^ string_of_int curr_i ^ ";\n" ^
      fst (fold (fn x => fn (acc,i) => (acc ^ print_node curr_i i x,i+1))
        (Stab.dest tree |> maps snd) ("",curr_i+1))
  in
  "strict graph Pathindexing {" ^ print_node 0 0 node ^ "}"
  end
*)
end;

(* Checks if module is compatible with interface while still exposing internal functions *)
structure Eq = struct
  type value = term
  val eq = Term.aconv_untyped
end
structure PathInterfaceCheck = Path (Eq) : TERM_INDEX;
