structure PathTT =
struct

datatype symbol = VarS | AtomS of string

fun symbol_ord (VarS, VarS) = EQUAL
  | symbol_ord (VarS, _) = LESS
  | symbol_ord (_, VarS) = GREATER
  | symbol_ord ((AtomS n1), (AtomS n2)) = fast_string_ord (n1, n2)

structure Symboltab = Table(type key = symbol val ord = symbol_ord);

type 'a content = (int * 'a) Ord_List.T

fun content_ord ((x,_),(y,_)) = int_ord (x, y)

(*Each node contains a table mapping symbols to their content and list of recursive trees for their
  arguments.*)
datatype 'a node = Node of ('a content * ('a node) list) Symboltab.table

(*(max_index, term_to_content_table, path_index)*)
type 'a T = int * ('a content) Termtab.table * 'a node

fun symbol_of_term t = case t of
    Const (n, _) => AtomS n
  | Free (n, _) => AtomS n
  | Bound i => AtomS (Name.bound i)
  | Var _ => VarS
  | Abs _ => VarS (*Note: FOL-terms won't contain abstractions; however, we treat them as variables
                    here to be in line with net.ML*)
  | _ $ _ => raise Fail "Invalid use of symbol_of_term"

val empty_node = Node Symboltab.empty
val empty = (0, Termtab.empty, empty_node);

(*** Insertion ***)

(*duplicate (term * value) pair in the index*)
exception INSERT

fun map_args _ [] symboltabs = symboltabs
  | map_args f (a::args) [] = f a empty_node :: map_args f args []
  | map_args f (a::args) (symboltab::symboltabs) = f a symboltab :: map_args f args symboltabs

(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.                           
  eq is the equality test for values. Terms must also be equal for INSERT to be raised.*)
fun insert eq_v (t, v) (id, values, tree) =
  let
    fun ins t (Node symboltab) =
      let
        fun update_entry args = 
          Ord_List.insert content_ord (id, v)
          |> apfst
          #> apsnd (map_args ins args)
        fun update symbol args =
          Symboltab.map_default (symbol, ([], [])) (update_entry args) symboltab
          |> Node
      in case strip_comb t of
         (*arguments to higher-order variables are cut off*)
         (Var _, _) => update VarS []
       | (Abs _, _) => update VarS []
       | (t, args) => update (symbol_of_term t) args
      end
    val values =
      Termtab.map_default (t, [])
        (fn kvs =>
          if member (eq_v o apsnd snd) kvs v
          then raise INSERT          
          else Ord_List.insert content_ord (id, v) kvs)
        values
  in (id + 1, values, ins t tree) end

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;


(*** Deletion ***)

exception DELETE;

(*Deletes values from the path sets of a given term t.
  Raises DELETE if no value is deleted. Collapses the index if possible.
  test is the predicate checking if a value associated to t should be deleted.*)
fun delete test t (id_max, values, tree) =
  let
    fun del to_delete t (Node symboltab) =
      let
        fun update symbol args =
          let
            val (symbol_content, arg_symboltabs) =
              Symboltab.lookup symboltab symbol
              |> the
              |> apfst (Ord_List.subtract content_ord to_delete)
          in
            if null symbol_content
            then Symboltab.delete symbol symboltab |> Node
            else
              map_args (del to_delete) args arg_symboltabs
              |> (fn arg_tabs => Symboltab.update (symbol, (symbol_content, arg_tabs)) symboltab)
              |> Node
          end
      in
        case strip_comb t of
          (Var _, _) => update VarS []
        | (Abs _, _) => update VarS []
        | (t, args) => update (symbol_of_term t) args
      end
    val t_content = Termtab.lookup_list values t
    val to_delete = filter (test o snd) t_content
    fun comp_values () =
      let val t_content = Ord_List.subtract content_ord to_delete t_content
      in
        if null t_content
        then Termtab.delete t values
        else Termtab.update (t, t_content) values
      end
  in
    case to_delete of
      [] => raise DELETE (*No value to delete*)
    | _ => (id_max, comp_values (), del to_delete t tree)
  end

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;


(*** Retrieval functions ***)
datatype query_type = Variants | Generalisations | Instances | Unifiables
datatype 'a term_set =
  List of 'a list |
  Intersection of 'a term_set list |
  Union of 'a term_set list |
  NoConstraint

exception NO_CONSTRAINT

fun compute_set term_set = case term_set of
    List xs => xs
  | Intersection [] => raise Fail "Empty intersect is undefined"
  | Intersection xs =>
    let val xs = map_filter (fn x => compute_set x |> SOME handle NO_CONSTRAINT => NONE) xs
    in
      case xs of
        [] => raise NO_CONSTRAINT
      | xs => inters_orig content_ord xs
    end
  | Union xs =>
      map compute_set xs
      |> Ord_List.unions content_ord
  | NoConstraint => raise NO_CONSTRAINT

fun content (_, values, _) =
  Termtab.dest values
  |> maps (map snd o snd)

fun is_empty tree = null (content tree)
              
fun query query_type term (Node symboltab) =
  let
    fun content symbol = Symboltab.lookup symboltab symbol |> Option.map fst |> these |> List
    fun arg_symboltabs symbol = Symboltab.lookup symboltab symbol |> Option.map snd |> these
    fun handle_var () = case query_type of
        Variants => content VarS
      | Instances => NoConstraint
      | Generalisations => content VarS
      | Unifiables => NoConstraint
    fun handle_atom sym = case query_type of
        Variants => content sym
      | Instances => content sym
      | Generalisations => Union [content VarS, content sym]
      | Unifiables => Union [content VarS, content sym]
    fun query_args func args =
      case arg_symboltabs func of
        [] => List []
      | xs => map2 (query query_type) args xs
              |> Intersection
    fun handle_func func args = case query_type of
        Variants => query_args func args
      | Instances => query_args func args
      | Generalisations => Union [content VarS, query_args func args]
      | Unifiables => Union [content VarS, query_args func args]
  in
    case strip_comb term of            
        (Var _,_) => handle_var ()
      | (Abs _,_) => handle_var ()
      | (atom, []) => handle_atom (symbol_of_term atom)
      | (func, args) => handle_func (symbol_of_term func) args
  end

fun query_wrapper query_type t (index as (_, _, node)) =
  query query_type t node
  |> compute_set
  |> map snd
  handle NO_CONSTRAINT => content index

fun variants tree t = query_wrapper Variants t tree
fun instances tree t = query_wrapper Instances t tree
fun generalisations tree t = query_wrapper Generalisations t tree
fun unifiables tree t = query_wrapper Unifiables t tree

fun merge eq index1 (_, values2, _) =
  fold (insert_safe eq)
    (Termtab.fold (fn (t, kvs) => fn acc => map (fn (_,v) => (t,v)) kvs @ acc) values2 []) index1
end

(* Checks if module is compatible with interface while still exposing internal functions *)
(*structure PathInterfaceCheck = PathTT : TERM_INDEX;*)