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
(* TODO purpose of VarK, name of Var irrelevant? *)
(* TODO is an empty key valid? *)
(* TODO should a key list address one node or multiple? *)
(* TODO is_first_order function in term! *)

datatype key = End of string | Fun of string * int * key | EndVar

(* Represent terms as trees with functions at their root instead of $ *)
datatype atom = AtomT of string | VarT
datatype term_tree = TT of atom * term_tree list

fun rev_term term args = case term of
      Const (n,_) => TT (AtomT n, args)
    | Free (n,_) => TT (AtomT n, args)
    | Bound i => TT (AtomT (Name.bound i), args)
    | Var _ => TT (VarT, args)
    | Abs _ => TT (VarT, args)
    | fst $ snd => rev_term fst (rev_term snd [] :: args)

(* TODO implement in a more efficient way by e.g. not creating reversed terms *)
fun key_of_term_aux term : key list =
  case term of
      TT (VarT,_) => [EndVar]
    | TT (AtomT n, []) => [End n]
    | TT (AtomT n, args) =>
           map key_of_term_aux args
        |> map_index (fn (i,t) => map (fn t => (i,t)) t)
        |> flat
        |> map (fn (i,t) => Fun (n,i,t))
        |> (fn ts => End n :: ts)

(*convert a term to a list of keys*)
fun key_of_term (t : term) : key list = key_of_term_aux (rev_term t [])

(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);

(*Trees indexed by key lists: each arc is labelled by a key.
  Each node contains a list of items, and arcs to children.
  The empty key addresses the entire net.
  Lookup functions preserve order in items stored at same level.
*)
(* Trees are indexed by key lists.
   Each node contains a list of items.
   CompNodes take an int to determine which argument to choose.
   SymNode take a string to determine which symbol to choose.
 *)
type 'a content = 'a list Symtab.table
datatype 'a net = Node of 'a content * 'a net Inttab.table Symtab.table
                 | Leaf of 'a content

val empty_node = Node (Symtab.empty, Symtab.empty);

val empty = Leaf (Symtab.empty);
fun is_empty (Leaf x) = Symtab.is_empty x | is_empty _ = false; (* TODO is that always correct? *)

(*** Insertion into a path index tree ***)

exception INSERT;       (*duplicate item in the net*)

(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for items.
  The empty list of keys generates a Leaf node, others a Net node.
*)

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

(* TODO inefficient approach: Insert each key independently.
   For e.g. f(g(h(x,y))) path from root to h is repeated thrice, for h,x,y
   TODO perhaps drop subkeys from keylist? For f(g(x)) only save <f,1,g,1> = x? Why doesn't that work?

   TODO transition to Table(int*string) as in structure Symreltab = Table(type key = string * string
  val ord = prod_ord fast_string_ord fast_string_ord);

type 'a content = 'a list Symtab.table
datatype 'a tree = Node of 'a content * 'a tree Inttab.table Symtab.table
                 | Leaf of 'a content
*)
fun insert_one eq (key, v) tree  =
  let fun apps key table = append_sym eq (key,v) table in
  case (key, tree) of
      (End n, Leaf con) => Leaf (apps n con)
    | (End n, Node (con, rest)) => Node (apps n con, rest)
    | (Fun (n,i,k), Leaf con) =>
        let val tree = insert_one eq (k,v) empty
            val inttab = Inttab.update (i,tree) Inttab.empty
            val symtab = Symtab.update (n,inttab) Symtab.empty
        in Node (con, symtab) end
    | (Fun (n,i,k), Node (con, symtab)) =>
        let val inttab = case Symtab.lookup symtab n of
                NONE => Inttab.empty | SOME x => x
            val node = case Inttab.lookup inttab i of
                NONE => empty | SOME x => x
            val node = insert_one eq (k,v) node
            val inttab = Inttab.update (i,node) inttab
            val symtab = Symtab.update (n,inttab) symtab
        in Node (con, symtab) end
   end

fun insert eq (keys,x) net =
  Library.foldl (fn (acc,k) => insert_one eq (k,x) acc) (net,keys)

fun insert_term eq (t, x) = insert eq (key_of_term t, x);

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;
fun insert_term_safe eq entry net = insert_term eq entry net handle INSERT => net;


(*** Deletion from a discrimination net ***)

exception DELETE;       (*missing item in the net*)

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent.  Collapses the net if possible.
  eq is the equality test for items. *)
fun delete_one eq (key, v) tree =
  let fun rem content = if member eq content v then remove eq v content
                else raise DELETE in
  case (key, tree) of
      (End n, Leaf con) => Leaf (Symtab.map_entry n rem con)
    | (End n, Node (con, rest)) => Node (Symtab.map_entry n rem con, rest)
    | (Fun _, Leaf _) => raise DELETE
    | (Fun (n,i,k), Node (con, symtab)) =>
        let val inttab = case Symtab.lookup symtab n of
                NONE => Inttab.empty | SOME x => x
            val node = case Inttab.lookup inttab i of
                NONE => empty | SOME x => x
            val node = delete_one eq (k,v) node
            val inttab = Inttab.update (i,node) inttab
            val symtab = Symtab.update (n,inttab) symtab
        in Node (con, symtab) end
   end

fun delete eq (keys, x) net =
  Library.foldl (fn (acc,k) => delete_one eq (k,x) acc) (net,keys)

fun delete_term eq (t, x) = delete eq (key_of_term t, x);

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;
fun delete_term_safe eq entry net = delete_term eq entry net handle DELETE => net;


(*** Retrieval functions for discrimination nets ***)

(*Return the list of items at the given node, [] if no such node*)
fun lookup_one tree key = (case (key,tree) of
    (End n, Leaf con) => (case Symtab.lookup con n of NONE => [] | SOME xs => xs)
  | (End n, Node (con,_)) => (case Symtab.lookup con n of NONE => [] | SOME xs => xs)
  | (Fun _, Leaf _) => []
  | (Fun (n,i,k), Node(_,rest)) => (case Symtab.lookup rest n of
      NONE => []
    | SOME x => (case Inttab.lookup x i of
        NONE => []
      | SOME x => lookup_one x k )) )

fun lookup _ [] = []
  | lookup tree (k::keys) =
    let val acc = lookup_one tree k
        fun intersect (acc,k) = inter Term.aconv_untyped acc (lookup_one tree k)
    in Library.foldl intersect (acc,keys) end

(*
(*Skipping a term in a net.  Recursively skip 2 levels if a combination*)
fun net_skip (Leaf _) nets = nets
  | net_skip (Net{comb,var,atoms}) nets =
      fold_rev net_skip (net_skip comb []) (Symtab.fold (cons o #2) atoms (var::nets));


(** Matching and Unification **)

(*conses the linked net, if present, to nets*)
fun look1 (atoms, a) nets =
  (case Symtab.lookup atoms a of
    NONE => nets
  | SOME net => net :: nets);

(*Return the nodes accessible from the term (cons them before nets)
  "unif" signifies retrieval for unification rather than matching.
  Var in net matches any term.
  Abs or Var in object: if "unif", regarded as wildcard,
                                   else matches only a variable in net.
*)
fun matching unif t net nets =
  let fun rands _ (Leaf _, nets) = nets
        | rands t (Net{comb,atoms,...}, nets) =
            case t of
                f$t => fold_rev (matching unif t) (rands f (comb,[])) nets
              | Const(c,_) => look1 (atoms, c) nets
              | Free(c,_)  => look1 (atoms, c) nets
              | Bound i    => look1 (atoms, Name.bound i) nets
              | _          => nets
  in
     case net of
         Leaf _ => nets
       | Net{var,...} =>
             case head_of t of
                 Var _ => if unif then net_skip net nets
                          else var::nets           (*only matches Var in net*)
  (*If "unif" then a var instantiation in the abstraction could allow
    an eta-reduction, so regard the abstraction as a wildcard.*)
               | Abs _ => if unif then net_skip net nets
                          else var::nets           (*only a Var can match*)
               | _ => rands t (net, var::nets)  (*var could match also*)
  end;

fun extract_leaves l = maps (fn Leaf xs => xs) l;

(*return items whose key could match t, WHICH MUST BE BETA-ETA NORMAL*)
fun match_term net t =
    extract_leaves (matching false t net []);

(*return items whose key could unify with t*)
fun unify_term net t =
    extract_leaves (matching true t net []);


(** operations on nets **)

(*subtraction: collect entries of second net that are NOT present in first net*)
fun subtract eq net1 net2 =
  let
    fun subtr (Net _) (Leaf ys) = append ys
      | subtr (Leaf xs) (Leaf ys) =
          fold_rev (fn y => if member eq xs y then I else cons y) ys
      | subtr (Leaf _) (net as Net _) = subtr emptynet net
      | subtr (Net {comb = comb1, var = var1, atoms = atoms1})
            (Net {comb = comb2, var = var2, atoms = atoms2}) =
          subtr comb1 comb2
          #> subtr var1 var2
          #> Symtab.fold (fn (a, net) =>
            subtr (the_default emptynet (Symtab.lookup atoms1 a)) net) atoms2
  in subtr net1 net2 [] end;

fun entries net = subtract (K false) empty net;


(* merge *)

fun cons_fst x (xs, y) = (x :: xs, y);

fun dest (Leaf xs) = map (pair []) xs
  | dest (Net {comb, var, atoms}) =
      map (cons_fst CombK) (dest comb) @
      map (cons_fst VarK) (dest var) @
      maps (fn (a, net) => map (cons_fst (AtomK a)) (dest net)) (Symtab.dest atoms);

fun merge eq (net1, net2) =
  fold (insert_safe eq) (dest net2) net1;  (* FIXME non-canonical merge order!?! *)

fun content net = map #2 (dest net);
*)
end;
