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

functor Path (V : sig type value end) =
struct

fun ord ((x,_),(y,_)) = int_ord (x,y)

datatype symbol =
    VarS
  | AtomS of string

fun sym_ord (VarS, VarS) = EQUAL
  | sym_ord (VarS, _) = LESS
  | sym_ord (_, VarS) = GREATER
  | sym_ord ((AtomS n1), (AtomS n2)) = fast_string_ord (n1,n2)

structure Stab = Table(type key = symbol val ord = sym_ord);
type value = V.value
type 'a content = (int * 'a) Ord_List.T Stab.table
datatype 'a tree = Node of 'a content * 'a tree list Stab.table
type T = int * ((term * V.value) * int) list * V.value tree

fun symbol_of_term t = case t of
          Const (n,_) => AtomS n
        | Free (n,_) => AtomS n
        | Bound i => AtomS (Name.bound i)
        | Var _ => VarS
        | Abs _ => VarS
        | _$_ => raise Fail "Invalid use of symbol_of_term"

(* Trees/Nets are indexed by keys. Each key represents a single node.
   Each node contains content as 'a list Symtab and a recursive tree.
   There is no leaf as the tree can be an empty table.
   There is no empty key.
*)

val empty_node = Node (Stab.empty, Stab.empty)
val empty = (0, [], empty_node);

(*** Insertion ***)

exception INSERT;       (*duplicate (term * value) pair in the index*)

fun map_child f (sym,args) tree =
  let fun map_list args xs =
        case (args,xs) of
          ([],xs) => xs
        | (a :: args, x :: xs) => f a x :: map_list args xs
        | (a :: args, []) => f a empty_node :: map_list args []
  in
  Stab.map_default (sym,[]) (map_list args) tree
  end

(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for values. Terms must also be equal for INSERT to be raised.
*)
fun insert eq (t,v) (id, values, Node (con,tree)) =
  let
    fun append_sym sym table = Stab.map_default (sym, []) (Ord_List.insert ord (id,v)) table
    fun ins t (Node (con, tree)) = case strip_comb t of
        (Var _,_) => Node (append_sym VarS con, tree)
      | (Abs _,_) => Node (append_sym VarS con, tree)
      | (sym,[]) => Node (append_sym (symbol_of_term sym) con, tree)
      | (func,args) =>
          let
            val con = append_sym (symbol_of_term func) con
            val tree = map_child ins (symbol_of_term func,args) tree
          in Node (con, tree) end
    val values =
      case AList.lookup (fn ((t,v),(u,w)) => Term.aconv_untyped (t,u) andalso eq (v,w)) values (t,v) of
        NONE => ((t,v),id) :: values
      | SOME _ => raise INSERT (* term * value pair already exists *)
  in
  (id + 1, values, ins t (Node(con,tree)))
  end

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;


(*** Deletion ***)

exception DELETE;       (* (term * value) pair is not present *)

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent. Does not collapse the index if possible.
  eq is the equality test for values, term equality is also considered. *)

    
(* TODO The value is saved at multiple locations. If some keys are removed from the list
      those will not be deleted from the tree but will be from the values *)

fun delete eq (t,v) (id, values, Node (con,tree)) =
  let
    fun rem id' content =
      if member (fn (_,(x,_)) => x = id') content v
      then remove (fn (_,(x,_)) => x = id') v content
      else raise Fail "Error in delete!"
    fun del id' t (Node (con, tree)) = case strip_comb t of
        (Var _,_) => Node (Stab.map_default (VarS,[]) (rem id') con, tree)
      | (Abs _,_) => Node (Stab.map_default (VarS,[]) (rem id') con, tree)
      | (sym,[]) => Node (Stab.map_default (symbol_of_term sym,[]) (rem id') con, tree)
      | (func,args) =>
          let
            val con = Stab.map_default (symbol_of_term func,[]) (rem id') con
            val tree = map_child (del id') (symbol_of_term func, args) tree
          in Node (con, tree) end
    fun eq_alist ((t,v),(u,w)) = Term.aconv_untyped (t,u) andalso eq (v, w)
    val (id',values) =
      case AList.lookup eq_alist values (t,v) of
        NONE => raise DELETE (* term * value pair does not exist *)
      | SOME id => (id, AList.delete eq_alist (t,v) values)
  in
  (id, values, del id' t (Node(con,tree)))
  end

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;


(*** Retrieval functions ***)
datatype query_type = Lookup | Generalisations | Instances | Unifiables
datatype 'a term_set = List of 'a list
                     | Intersection of 'a term_set list
                     | Union of 'a term_set list
                     | NoConstraint
exception NoConstraint_exn

fun compute_set term_set = case term_set of
    List xs => xs
  | Intersection [] => raise Fail "Empty intersect is undefined"
  | Intersection (x::xs) =>
      let fun f x acc = Ord_List.inter ord (compute_set x) acc handle NoConstraint_exn => acc
      in fold f xs (compute_set x) end
  | Union xs => (*map compute_set xs |> Ord_List.unions ord*) fold (fn x => Ord_List.union ord (compute_set x)) xs []
  | NoConstraint => raise NoConstraint_exn

fun content (_, values, _) = map (fn ((_,v),_) => v) values

fun is_empty (_, values, _) = null values

fun query query_type term (Node (con,tree)) =
  let
    fun symbols sym = Stab.lookup_list con sym |> List
    fun  handle_var () = case query_type of
        Lookup => symbols VarS
      | Instances => NoConstraint
      | Generalisations => symbols VarS
      | Unifiables => NoConstraint
    fun handle_sym sym = case query_type of
        Lookup => symbols sym
      | Instances => symbols sym
      | Generalisations => Union [symbols VarS, symbols sym]
      | Unifiables => Union [symbols VarS, symbols sym]
    fun query_args func args =
      let
        val list = Stab.lookup_list tree func
        fun arg_to_terms (index, arg) =
          query query_type arg (nth list index)
          handle Subscript => List []
      in
      Intersection (map_index arg_to_terms args)
      end
    fun all_args_var args =
(*      fold (fn x => fn acc => case strip_comb x |> fst of (Var _) => acc | _ => false) args true *) false
    fun handle_func func args = case query_type of
        Lookup => query_args func args
      | Instances =>
          (* Shortcut if all args are variables *)
          if all_args_var args
          then symbols func
          else query_args func args
      | Generalisations => Union [symbols VarS, query_args func args]
      | Unifiables =>
          (* Shortcut if all args are variables *)
          if all_args_var args
          then symbols func
          else Union [symbols VarS, query_args func args]
  in
  case strip_comb term of
    (Var _,_) => handle_var ()
  | (Abs _,_) => handle_var ()
  | (sym,[]) => handle_sym (symbol_of_term sym)
  | (func,args) => handle_func (symbol_of_term func) args
  end

fun query_wrapper query_type t (_, values, node) =
  query query_type t node
  |> compute_set
  |> map snd
  handle NoConstraint_exn => map (fn ((_,v),_) => v) values

fun lookup tree t = query_wrapper Lookup t tree
fun instances tree t = query_wrapper Instances t tree
fun generalisations tree t = query_wrapper Generalisations t tree
fun unifiables tree t = query_wrapper Unifiables t tree

fun dest (Node (con,tree)) : ((symbol * int) list * 'a) list =
  let
    val content_alist =
      Stab.dest con
      |> maps (fn (k,vs) => map (fn v => ([(k,0)], snd v)) vs)
    val tree_alist =
      Stab.dest tree
      |> maps (fn (sym,vs) => map_index (fn (i,v) => (sym,i,v)) vs)
      |> maps (fn (sym,ind,value) => dest value |> map (fn (k,v) => ((sym,ind)::k,v)))
  in content_alist @ tree_alist end

fun insert_at_node eq (keys, v) id (Node (con,tree)) =
  let
    fun append_sym sym table = Stab.map_default (sym, []) (Ord_List.insert ord (id,v)) table
  in
    case keys of
      [] => raise Fail "Invalid key at insert_at_node"
    | [(sym,_)] => Node (append_sym sym con, tree)
    | (sym,ind) :: keys =>
      let fun update_single f (sym,ind) tree = Stab.map_default (sym,[]) (fn xs => take (ind-1) xs @ f (nth xs ind) :: drop ind xs) tree
      in
      Node (con, update_single (insert_at_node eq (keys,v) id) (sym,ind) tree)
      end
  end

(* FIXME non-canonical merge order!?! *)
fun merge eq (id1, values1, tree1) (_, values2, tree2) =
  fold (fn t => fn (id, tree) => (id+1, insert_at_node eq t id tree)) (dest tree2) (id1, tree1)
  |> (fn (id,tree) => (id, union (fn (((t,v),_),((u,w),_)) => Term.aconv_untyped (t,u) andalso eq (v,w)) values1 values2, tree))

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
structure PathInterfaceCheck = Path (struct type value = term end) : TERM_INDEX;
