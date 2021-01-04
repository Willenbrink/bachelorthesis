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

structure Path =
struct
(* TODO should an empty key be valid?
   TODO should a key list address one node or multiple?
   TODO is_first_order function in term!
 *)

fun >>= (x,f) = Option.map f x
infix 1 >>=

datatype symbol =
  VarS
| AtomS of string
datatype key =
  End of symbol
| Fun of symbol * int * key (* function,number of child, key from that child onwards *)

fun sym_ord (VarS, VarS) = EQUAL
  | sym_ord (VarS, _) = LESS
  | sym_ord (_, VarS) = GREATER
  | sym_ord ((AtomS n1), (AtomS n2)) = fast_string_ord (n1,n2)

structure Stab = Table(type key = symbol val ord = sym_ord);
type 'a content = 'a Unsynchronized.ref list Stab.table
datatype 'a net = Node of 'a content * 'a net list Stab.table

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

(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);

(* Trees/Nets are indexed by keys. Each key represents a single node.
   Each node contains content as 'a list Symtab and a recursive tree.
   There is no leaf as the tree can be an empty table.
   There is no empty key.
   TODO Lookup functions preserve order in items stored at same level?
*)

val empty = Node (Stab.empty, Stab.empty);
fun is_empty (Node (c,t)) = Stab.is_empty c andalso case Stab.dest t of
    [] => true
  | xs => fold (fn (_,[]) => I | (_,_) => K false) xs true

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
            fun ins_list xs = nth_map_default index ins empty xs
            fun ins_symtab f tree = Stab.map_default (name,[]) f tree
        in Node (con, ins_symtab ins_list tree) end

fun insert_ref_safe eq (keys,term_ref) net = (* Insert a reference directly. Only internal usage *)
  let fun eq' (x,y) = (x = y) orelse eq (!x,!y) in
  Library.foldl (fn (acc,k) => insert_one eq' (k, term_ref) acc) (net,keys)
  handle INSERT => net
  end

fun insert eq (keys,term) net =
  let fun eq' (x,y) = (x = y) orelse eq (!x,!y)
      val term = Unsynchronized.ref term
  in
  Library.foldl (fn (acc,k) => insert_one eq' (k, term) acc) (net,keys)
  end

fun insert_term eq (t, x) = insert eq (key_of_term t, x);

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;
fun insert_term_safe eq entry net = insert_term eq entry net handle INSERT => net;


(*** Deletion ***)

exception DELETE;       (*missing item in the net*)

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent. TODO Collapses the net if possible?
  eq is the equality test for items. *)
fun delete_one eq (key, v) (Node (con,tree)) =
  let fun eq' (x,y) = eq (!x,!y)
      fun rem content = if member eq' content v then remove eq' v content
                        else raise DELETE in
  case key of
      End n => Node (Stab.map_default (n,[]) rem con, tree)
    | Fun (name,index,key) =>
           delete_one eq (key,v)
        |> (fn f => nth_map index (fn xs => f xs))
        |> (fn x => Stab.map_default (name,[]) x tree)
        |> (fn x => Node (con, x))
   end

fun delete eq (keys, x) net =
  Library.foldl (fn (acc,k) => delete_one eq (k, Unsynchronized.ref x) acc) (net,keys)

fun delete_term eq (t, x) = delete eq (key_of_term t, x);

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;
fun delete_term_safe eq entry net = delete_term eq entry net handle DELETE => net;


(*** Retrieval functions ***)
fun content_ref n =
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
  aux n
  (*|> tap (fn x => x |> length |> @{make_string} |> writeln)*)
  |> distinct (op =)
(*  |> tap (fn x => x |> length |> @{make_string} |> writeln)*)
  end

fun content n = content_ref n |> map (op !)

(*Return the list of items at the given node, [] if no such node*)
fun lookup_one (Node (con,tree)) key = case key of
    End n => (case Stab.lookup con n of NONE => [] | SOME xs => xs)
  | Fun (name,index,key) =>
       Stab.lookup tree name
       >>= (fn xs => nth xs index)
       >>= (fn x => lookup_one x key)
       |> Option.valOf

fun lookup tree keys =
    let val acc = content_ref tree
        fun intersect (acc,k) = inter (op =) acc (lookup_one tree k)
    in Library.foldl intersect (acc,keys) |> map (op !) end (* TODO *)

fun match unif (node as Node (con,tree)) term =
  let
    val var_terms = Stab.lookup_list con VarS
    val handle_var = if unif then content_ref node else var_terms
    fun handle_sym sym = Stab.lookup_list con sym
    fun handle_func func args =
      let val list = Stab.lookup_list tree func
          fun arg_to_terms index arg = match unif (nth list index) arg handle Subscript => []
      in
      fold_index (fn (index,arg) => fn acc => inter (op =) (arg_to_terms index arg) acc)
        args (content_ref node)
      end
  in
  case strip_comb term of
  (* Ignore arguments and return
  Unif: every term at that path
  ~Unif: terms with Var/Abs at that path *)
    (Var _,_) => handle_var
  | (Abs _,_) => handle_var
  | (_$_,_) => raise Fail "Impossible"
  | (sym,[]) => (if unif then var_terms else []) @ (handle_sym (symbol_of_term sym))
  | (func,args) => (if unif then var_terms else []) @ (handle_func (symbol_of_term func) args)
  end

fun match_term n t = match false n t |> distinct (op =) |> map (op !)
fun unify_term n t = match true n t |> distinct (op =) |> map (op !)

val entries = content (* TODO are they really the same? *)

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

fun merge eq (tree1, tree2) =
  fold (fn t => insert_ref_safe eq t) (dest tree2 |> map (fn (k,v) => ([k],v))) tree1  (* FIXME non-canonical merge order!?! *)

fun subtract eq tree1 tree2 = Library.subtract (swap #> eq) (content tree1) (content tree2)

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
structure PathInterfaceCheck = Path : NET;
