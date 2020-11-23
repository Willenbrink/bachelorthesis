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

signature NET =
sig
  type key
  val key_of_term: term -> key list
  val encode_type: typ -> term

  type 'a net
  val empty: 'a net
  val is_empty: 'a net -> bool

  exception INSERT
  val insert: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_term: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_safe: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_term_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net

  exception DELETE
  val delete: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_term: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val delete_safe: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_term_safe: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net

  val lookup: 'a net -> key list -> 'a list
  val match_term: 'a net -> term -> 'a list
  val unify_term: 'a net -> term -> 'a list
  val entries: 'a net -> 'a list
  val subtract: ('b * 'a -> bool) -> 'a net -> 'b net -> 'b list
  val merge: ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
  val content: 'a net -> 'a list
end;

structure Path (*: NET*) =
struct
(* TODO should a empty key be valid?
   TODO should a key list address one node or multiple?
   TODO is_first_order function in term!
   TODO Var/Abs is sometimes encoded with an empty string. Problematic?

 *)

(* Fun(name,index,key_remainder) *)
datatype key = End of string | Fun of string * int * key | EndVar

(* Represent terms as trees with functions at their root instead of $ *)
datatype atom = AtomT of string | VarT
(* TT(name, args) is a constant when args = [], function elsewise *)
datatype term_tree = TT of atom * term_tree list
(* TODO Use strip-comb whenever $ is encountered instead! *)
fun rev_term term =
  let fun aux term args = case term of
      Const (n,_) => TT (AtomT n, args)
    | Free (n,_) => TT (AtomT n, args)
    | Bound i => TT (AtomT (Name.bound i), args)
    | Var _ => TT (VarT, args)
    | Abs _ => TT (VarT, args)
    | fst $ snd => aux fst (aux snd [] :: args)
  in aux term [] end

(*convert a term to a list of keys, one key for each {Var,Const,Func} in term*)
(* TODO implement in a more efficient way by not explicitly creating reversed terms *)
fun key_of_term (t : term) : key list =
  let fun aux term = case term of
      TT (VarT,[]) => [EndVar]
    | TT (VarT, args) =>
           map aux args
        |> map_index (fn (i,t) => map (fn t => (i,t)) t) (*Map every arg to correct index*)
        |> flat
        |> map (fn (i,t) => Fun ("",i,t))
        |> (fn ts => EndVar :: ts) (* Prepend current pos *)
    | TT (AtomT n, []) => [End n]
    | TT (AtomT n, args) =>
           map aux args
        |> map_index (fn (i,t) => map (fn t => (i,t)) t) (*Map every arg to correct index*)
        |> flat
        |> map (fn (i,t) => Fun (n,i,t))
        |> (fn ts => End n :: ts) (* Prepend current pos *)
  in rev_term t
  |> aux
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
type 'a content = 'a list Symtab.table
datatype 'a net = Node of 'a content * 'a net Inttab.table Symtab.table

val empty = Node (Symtab.empty, Symtab.empty);
fun is_empty (Node (c,t)) = Symtab.is_empty c andalso Symtab.is_empty t
(* TODO potentially, every subtable is empty *)

(*** Insertion into a path index tree ***)

exception INSERT;       (*duplicate item in the net*)

fun append_sym eq (k,v) table =
  let fun update vs =
    if member eq vs v
    then raise INSERT
    else v::vs
  in Symtab.map_default (k, []) update table end

fun append_int eq (k,v) table =
  let fun update vs =
    if member eq vs v
    then raise INSERT
    else v::vs
  in Inttab.map_default (k, []) update table end

(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for items.
  TODO inefficient approach: Insert each key independently.
  For e.g. f(g(h(x,y))) path from root to h is repeated thrice, for h,x,y
  TODO perhaps drop subkeys from keylist? For f(g(x)) only save <f,1,g,1> = x? Why doesn't that work?
*)
fun insert_one eq (key, v) (Node (con,tree)) = (case key of
      End n => Node (append_sym eq (n,v) con, tree)
    | EndVar => Node (append_sym eq ("",v) con, tree)
    | Fun (name,ind,key) =>
         insert_one eq (key,v)
      |> (fn x => Inttab.map_default (ind,empty) x)
      |> (fn x => Symtab.map_default (name,Inttab.empty) x tree)
      |> (fn x => Node (con, x)))

fun insert eq (keys,term) net =
  Library.foldl (fn (acc,k) => insert_one eq (k,term) acc) (net,keys)

fun insert_term eq (t, x) = insert eq (key_of_term t, x);

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;
fun insert_term_safe eq entry net = insert_term eq entry net handle INSERT => net;


(*** Deletion from a discrimination net ***)

exception DELETE;       (*missing item in the net*)

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent. TODO Collapses the net if possible?
  eq is the equality test for items. *)
fun delete_one eq (key, v) (Node (con,tree)) =
  let fun rem content = if member eq content v then remove eq v content
                        else raise DELETE in
  case key of
      End n => Node (Symtab.map_default (n,[]) rem con, tree)
    | EndVar => Node (Symtab.map_default ("",[]) rem con, tree)
    | Fun (n,i,k) =>
      delete_one eq (k,v)
        |> Inttab.map_default (i, empty)
        |> (fn x => Symtab.map_default (n,Inttab.empty) x tree)
        |> (fn x => Node (con, x))
   end

fun delete eq (keys, x) net =
  Library.foldl (fn (acc,k) => delete_one eq (k,x) acc) (net,keys)

fun delete_term eq (t, x) = delete eq (key_of_term t, x);

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;
fun delete_term_safe eq entry net = delete_term eq entry net handle DELETE => net;


(*** Retrieval functions for discrimination nets ***)
fun content (Node (con,tree)) =
  let val con_fst =
        con |> Symtab.dest 
            |> maps snd
      val con_snd =
        tree |> Symtab.dest
             |> maps (Inttab.dest o snd)
             |> maps (content o snd)
  in con_fst @ con_snd end

(*Return the list of items at the given node, [] if no such node*)
fun lookup_one (Node (con,tree)) key = case key of
    End n => (case Symtab.lookup con n of NONE => [] | SOME xs => xs)
  | EndVar => (case Symtab.lookup con "" of NONE => [] | SOME xs => xs)
  | Fun (n,i,k) => case Symtab.lookup tree n of
      NONE => []
    | SOME x => case Inttab.lookup x i of
        NONE => []
      | SOME x => lookup_one x k

fun lookup tree keys =
    let val acc = content tree
        fun intersect (acc,k) = inter Term.aconv_untyped acc (lookup_one tree k)
    in Library.foldl intersect (acc,keys) end

fun match unif node term =
  let
    fun name t = case t of
              Const (n,_) => n
            | Free (n,_) => n
            | Bound i => Name.bound i
            | Var _ => ""
            | Abs _ => ""
            | _$_ => raise Fail "Impossible"

    fun lookup_term table term = (* Replace var in term arbitrarily *)
      case term of
        Var _ => Symtab.dest table |> map snd |> flat
      | Abs _ => Symtab.dest table |> map snd |> flat
      | _$_ => raise INSERT
      | rest => Symtab.lookup_list table (name rest)

   fun lookup_unif table key =
     if unif
     then union Term.aconv_untyped (Symtab.lookup_list table "") (lookup_term table key)
     else lookup_term table key

   fun aux (node as Node(con,tree)) t = case t of
      _ $ _ =>
        let val (func, args) = strip_comb t
            val inttabs =
              case (unif, name func = "") of
                  (true, true) => Symtab.dest tree |> map snd
                | (true, false) => 
                    (case Symtab.lookup tree (name func) of NONE => [] | SOME x => [x])
                  @ (case Symtab.lookup tree "" of NONE => [] | SOME x => [x])
                | _ => case Symtab.lookup tree (name func) of NONE => [] | SOME x => [x]
            fun match (index,term) =
              maps (fn x => case Inttab.lookup x index of SOME x => aux x term | NONE => []) inttabs
        in
        Library.fold_index
          (fn arg => fn acc => inter Term.aconv_untyped acc (match arg))
          args (aux node func)
        end
    | rest => lookup_unif con rest
  in aux node term end

val match_term = match false
val unify_term = match true

val entries = content (* TODO are they really the same? *)

fun merge eq (tree1, tree2) =
  fold (fn t => insert_term_safe eq (t,t)) (content tree2) tree1  (* FIXME non-canonical merge order!?! *)

fun subtract eq tree1 tree2 = Library.subtract eq (content tree1) (content tree2)
end;
