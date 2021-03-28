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

structure PathIndex =
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
type 'a content = (int * 'a) Ord_List.T Stab.table
datatype 'a tree = Node of 'a content * 'a tree list Stab.table
type 'a T = int * (term * ('a * int) list) list * 'a tree

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


(*** Retrieval functions ***)
datatype query_type = Variants | Generalisations | Instances | Unifiables
datatype 'a term_set = List of 'a list
                     | Intersection of 'a term_set list
                     | Union of 'a term_set list
                     | NoConstraint
exception NoConstraint_exn

fun compute_set term_set = case term_set of
    List xs => xs
  | Intersection [] => raise Fail "Empty intersect is undefined"
  | Intersection xs =>
    let val xs = map_filter (fn x => compute_set x |> SOME handle NoConstraint_exn => NONE) xs
    in
    case xs of
      [] => raise NoConstraint_exn
    | xs => inters_orig ord xs
    end
  | Union xs =>
      map compute_set xs
      |> Ord_List.unions ord
  | NoConstraint => raise NoConstraint_exn

fun content ((_, values, _)) =
  values
  |> maps snd
  |> map fst

fun is_empty tree = null (content tree)

fun query query_type term (Node (con,tree)) =
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
          query query_type arg (nth list index)
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

fun query_wrapper query_type t (index as (_, _, node)) =
  query query_type t node
  |> compute_set
  |> map snd
  handle NoConstraint_exn => content index

fun variants tree t = query_wrapper Variants t tree
fun instances tree t = query_wrapper Instances t tree
fun generalisations tree t = query_wrapper Generalisations t tree
fun unifiables tree t = query_wrapper Unifiables t tree

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
fun insert eq_v (t,v) (index as (id, values, Node (con,tree)) : 'a T) =
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
      if member eq_v (variants index t) v
      then raise INSERT
      else 
      AList.map_default (Term.aconv_untyped) (t,[])
        (fn xs => (v,id) :: xs)
        values

  in
  (id + 1, values, ins t (Node(con,tree)))
  end

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;


(*** Deletion ***)

exception DELETE;

(*Deletes values from the path sets of term t.
  Raises DELETE if no value is deleted. Does not collapse the index if possible.
  test is the predicate for deletion on values, term equality is also considered. *)

fun delete test t ((id_max, values, Node (con,tree)) : 'a T) =
  let
    fun rem ids xs = filter_out (fn (id,_) => member (op =) ids id) xs

    fun del ids t (Node (con, tree)) = case strip_comb t of
        (Var _,_) => Node (Stab.map_default (VarS,[]) (rem ids) con, tree)
      | (Abs _,_) => Node (Stab.map_default (VarS,[]) (rem ids) con, tree)
      | (sym,[]) => Node (Stab.map_default (symbol_of_term sym,[]) (rem ids) con, tree)
      | (func,args) =>
          let
            val con = Stab.map_default (symbol_of_term func,[]) (rem ids) con
            val tree = map_child (del ids) (symbol_of_term func, args) tree
          in Node (con, tree) end

    val (to_delete, values) =
      AList.map_entry_yield Term.aconv_untyped t
        (fn xs => ((filter (test o fst) xs), (filter_out (test o fst) xs))) values

  in
  case to_delete of
    NONE => raise DELETE
  | SOME [] => raise DELETE (* No value was deleted. *)
  | SOME xs => (id_max, values, del (map snd xs) t (Node(con,tree)))
  end

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;

fun merge eq index1 (_, values2, _) =
  fold (insert_safe eq) (maps (fn (t,vs) => map (fn (v,_) => (t,v)) vs) values2) index1
end;

(* Checks if module is compatible with interface while still exposing internal functions *)
(*structure PathInterfaceCheck = Path : TERM_INDEX;*)
