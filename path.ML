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

(* Fun(name,index,key_rest) *)
datatype key = End of string | Fun of string * int * key | EndVar

(* Represent terms as trees with functions at their root instead of $ *)
datatype atom = AtomT of string | VarT
(* TT(name, args) is a constant when args = [] *)
datatype term_tree = TT of atom * term_tree list

fun rev_term term =
  let fun aux term args = case term of
      Const (n,_) => TT (AtomT n, args)
    | Free (n,_) => TT (AtomT n, args)
    | Bound i => TT (AtomT (Name.bound i), args)
    | Var _ => TT (VarT, args)
    | Abs _ => TT (VarT, args)
    | fst $ snd => aux fst (aux snd [] :: args)
  in aux term [] end

(*convert a term to a list of keys*)
(* TODO implement in a more efficient way by not explicitly creating reversed terms *)
fun key_of_term (t : term) : key list =
  let fun aux term = case term of
      TT (VarT,_) => [EndVar]
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
   Each node contains content as a' list Symtab and a recursive tree.
   There is no leaf as the tree can be an empty table.
   There is no empty key.
   TODO Lookup functions preserve order in items stored at same level?
*)
type 'a content = 'a list Symtab.table
datatype 'a net = Node of 'a content * 'a net Inttab.table Symtab.table

val empty = Node (Symtab.empty, Symtab.empty);
fun is_empty (Node (c,t)) = Symtab.is_empty c andalso Symtab.is_empty t

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

  TODO transition to Table(int*string) as in structure Symreltab = Table(type key = string * string
  val ord = prod_ord fast_string_ord fast_string_ord);
*)
fun insert_one eq (key, v) (Node (con,tree)) = case key of
      End n => Node (append_sym eq (n,v) con, tree)
    | Fun (n,i,k) =>
        let val inttab = case Symtab.lookup tree n of
                NONE => Inttab.empty | SOME x => x
            val node = case Inttab.lookup inttab i of
                NONE => empty | SOME x => x
            val node = insert_one eq (k,v) node
            val inttab = Inttab.update (i,node) inttab
            val symtab = Symtab.update (n,inttab) tree
        in Node (con, symtab)
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
fun delete_one eq (key, v) (Node (con,tree)) =
  let fun rem content = if member eq content v then remove eq v content
                else raise DELETE in
  case key of
      End n => Node (Symtab.map_entry n rem con, tree)
    | Fun (n,i,k) =>
        let val inttab = case Symtab.lookup tree n of
                NONE => Inttab.empty | SOME x => x
            val node = case Inttab.lookup inttab i of
                NONE => empty | SOME x => x
            val node = delete_one eq (k,v) node
            val inttab = Inttab.update (i,node) inttab
            val symtab = Symtab.update (n,inttab) tree
        in Node (con, symtab) end
   end

fun delete eq (keys, x) net =
  Library.foldl (fn (acc,k) => delete_one eq (k,x) acc) (net,keys)

fun delete_term eq (t, x) = delete eq (key_of_term t, x);

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;
fun delete_term_safe eq entry net = delete_term eq entry net handle DELETE => net;


(*** Retrieval functions for discrimination nets ***)

(*Return the list of items at the given node, [] if no such node*)
fun lookup_one (Node (con,tree)) key = case key of
    End n => (case Symtab.lookup con n of NONE => [] | SOME xs => xs)
  | Fun (n,i,k) => (case Symtab.lookup tree n of
      NONE => []
    | SOME x => (case Inttab.lookup x i of
        NONE => []
      | SOME x => lookup_one x k ))

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
