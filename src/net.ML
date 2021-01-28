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

functor Net (V : sig type value end) =
struct

fun >>= (x,f) = Option.map f x
infix 1 >>=

datatype key = CombK | VarK | AtomK of string;

(*Keys are preorder lists of symbols -- Combinations, Vars, Atoms.
    Any term whose head is a Var is regarded entirely as a Var.
    Abstractions are also regarded as Vars;  this covers eta-conversion
    and "near" eta-conversions such as %x.?P(?f(x)).
  As the terms must be eta-long beta-normal form every function f is wrapped into (\x. f x)
  Additionally no beta reduction is possible \<Rightarrow> Every function is missing its arguments
    (e.g. (\x. f x) (\x. g x) is not possible)
  \<Rightarrow> Every Abs occurence has no arguments. No HOL-symbols/terms can occur outside of an Abs
*)
fun add_key_of_terms (term, keys) : key list =
   let fun aux (term, keys) = case term of
           fst $ snd => CombK :: aux (fst, check_head (snd, keys))
         | Const (name,_) => AtomK name :: keys
         | Free (name,_) => AtomK name :: keys
         | Bound i => AtomK (Name.bound i) :: keys
         (* Other cases impossible. check_head ensured that no Var/Abs
            occurs before the next $ *)
       and check_head (term, keys) = case head_of term of
           Var _ => VarK :: keys
         | Abs _ => VarK :: keys
         | _ => aux (term, keys)
   in check_head (term, keys)
   end;

(*convert a term to a list of keys*)
fun key_of_term t = add_key_of_terms (t, []);

(*Trees indexed by key lists: each arc is labelled by a key.
    Each node contains a list of items, and arcs to children.
    The empty key addresses the entire net.
    Lookup functions preserve order in items stored at same level.
*)
type value = V.value
datatype T = Leaf of value list
            | Net of {comb: T,
                      var: T,
                      atoms: T Symtab.table};

val empty = Leaf[];
fun is_empty (Leaf []) = true | is_empty _ = false;
val emptynet = Net{comb=empty, var=empty, atoms=Symtab.empty};


(*** Insertion into a discrimination net ***)

exception INSERT;       (*duplicate item in the net*)


(*Adds item x to the list at the node addressed by the keys.
    Creates node if not already present.
    eq is the equality test for items.
    The empty list of keys generates a Leaf node, others a Net node.
*)
fun insert_key eq x (keys, net) = case (keys, net) of
    ([], Leaf xs) => if member eq xs x then  raise INSERT  else Leaf(x::xs)
  | (keys, Leaf[]) => insert_key eq x (keys, emptynet)   (*expand empty...*)
  | (CombK :: keys, Net{comb,var,atoms}) =>
      Net{comb=insert_key eq x (keys,comb), var=var, atoms=atoms}
  | (VarK :: keys, Net{comb,var,atoms}) =>
      Net{comb=comb, var=insert_key eq x (keys,var), atoms=atoms}
  | (AtomK a :: keys, Net{comb,var,atoms}) =>
      let val atoms' = Symtab.map_default (a, empty) (fn net' => insert_key eq x (keys, net')) atoms in
        Net{comb=comb, var=var, atoms=atoms'}
      end

fun insert eq (t,x) net = insert_key eq x (key_of_term t,net)

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;


(*** Deletion from a discrimination net ***)

exception DELETE;       (*missing item in the net*)

(*Create a new Net node if it would be nonempty*)
fun newnet (args as {comb,var,atoms}) =
    if is_empty comb andalso is_empty var andalso Symtab.is_empty atoms
    then empty else Net args;

(*Deletes item x from the list at the node addressed by the keys.
    Raises DELETE if absent.  Collapses the net if possible.
    eq is the equality test for items. *)
fun delete eq (t, x) net =
    let fun del1 ([], Leaf xs) =
            if member eq xs x then Leaf (remove eq x xs)
            else raise DELETE
        | del1 (keys, Leaf[]) = raise DELETE
        | del1 (CombK :: keys, Net{comb,var,atoms}) =
            newnet{comb=del1(keys,comb), var=var, atoms=atoms}
        | del1 (VarK :: keys, Net{comb,var,atoms}) =
            newnet{comb=comb, var=del1(keys,var), atoms=atoms}
        | del1 (AtomK a :: keys, Net{comb,var,atoms}) =
            let val atoms' =
                (case Symtab.lookup atoms a of
                NONE => raise DELETE
                | SOME net' =>
                    (case del1 (keys, net') of
                    Leaf [] => Symtab.delete a atoms
                    | net'' => Symtab.update (a, net'') atoms))
            in  newnet{comb=comb, var=var, atoms=atoms'}  end
    in  del1 (key_of_term t,net)  end;

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;


(*** Retrieval functions for discrimination nets ***)

fun lookup_aux net keys = case (net,keys) of
    (Leaf xs, []) => xs
  | (Leaf _, (_ :: _)) => [] (*non-empty keys and empty net*)
  | (Net {comb, ...}, (CombK :: keys)) => lookup_aux comb keys
  | (Net {var, ...}, (VarK :: keys)) => lookup_aux var keys
  | (Net {atoms, ...}, (AtomK a :: keys)) => (case Symtab.lookup atoms a of
        SOME net => lookup_aux net keys
        | NONE => [])
(*Return the list of items at the given node, [] if no such node*)
fun lookup net t = lookup_aux net (key_of_term t)


(*Skipping a term in a net.  Recursively skip 2 levels if a combination*)
fun net_skip (Leaf _) nets = nets
  | net_skip (Net{comb,var,atoms}) nets =
      var :: nets
      |> Symtab.fold (fn (k,v) => fn acc => v :: acc) atoms
(* net_skip comb [] only skipped combs so far so another skip is required *)
(* TODO why fold_rev? fold should be faster and we only concatenate nets *)
      |> fold_rev net_skip (net_skip comb [])


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
  let
    fun rands _ (Leaf _) nets = nets
      | rands t (Net{comb,atoms,...}) nets =
          case t of
            f$t => fold_rev (check_var t) (rands f comb []) nets
          | Const(c,_) => look1 (atoms, c) nets
          | Free(c,_)  => look1 (atoms, c) nets
          | Bound i    => look1 (atoms, Name.bound i) nets
          | _          => nets (* When does this occur? *)
    and
    check_var t net nets =
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
          | _ => rands t net (var::nets)  (*var could match also*)
  in
  check_var t net nets
  end;

fun extract_leaves l = maps (fn Leaf xs => xs) l;

(*return items whose key could match t, WHICH MUST BE BETA-ETA NORMAL*)
fun match_term net t =
    extract_leaves (matching false t net []);

(*return items whose key could unify with t*)
fun unify_term net t =
    extract_leaves (matching true t net []);

datatype query_type = Variants | Generalisations | Instances | Unifiables

fun string_of_term t = case t of
        Const (n,_) => n
      | Free (n,_) => n
      | Bound i => Name.bound i
      | _ => raise Fail "Invalid use of string_of_term"

fun strip_comb_key i ks = case (i,ks) of
    (0,ks) => ks
  | (_,[]) => raise Fail "Invalid strip_comb_key, too many combs"
  | (i, (CombK::ks)) => strip_comb_key (i+1) ks
  | (i, (_::ks)) => strip_comb_key (i-1) ks

fun query mode keys net =
  case net of
    (Leaf xs) => xs
  | (Net {comb, var, atoms}) =>
    let
      fun con net = case net of Leaf xs => xs | _ => []
      fun symbols sym = case Symtab.lookup atoms sym of NONE => emptynet | SOME net => net
      fun handle_var ks = case mode of
          Variants => query mode ks var
        | Instances => net_skip net [] |> maps (query mode ks)
        | Generalisations => query mode ks var
        | Unifiables => net_skip net [] |> maps (query mode ks)
      fun handle_sym ks sym = case mode of
          Variants => query mode ks (symbols sym)
        | Instances => query mode ks (symbols sym)
        | Generalisations => query mode ks var @ query mode ks (symbols sym)
        | Unifiables => query mode ks var @ query mode ks (symbols sym)
      fun handle_func ks = case mode of
          Variants => query mode ks comb
        | Instances => query mode ks comb
        | Generalisations => query mode (strip_comb_key 1 (tl ks)) var @ query mode ks comb
        | Unifiables => query mode (strip_comb_key 1 (tl ks)) var @ query mode ks comb
    in
      case keys of
        [] => con net
      | (VarK :: ks) => handle_var ks
      | (AtomK c :: ks) => handle_sym ks c
      | (CombK :: ks) => handle_func ks
    end

fun query_wrapper mode t net =
  query mode (key_of_term t) net

fun lookup net t = query_wrapper Variants t net
fun instances net t = query_wrapper Instances t net
fun generalisations net t = query_wrapper Generalisations t net
fun unifiables net t = query_wrapper Unifiables t net

fun generalisations' net t = matching false t net [] |> extract_leaves
fun unifiables' net t = matching true t net [] |> extract_leaves


(** operations on nets **)

(* merge *)

fun cons_fst x (xs, y) = (x :: xs, y);

fun dest (Leaf xs) = map (pair []) xs
    | dest (Net {comb, var, atoms}) =
        map (cons_fst CombK) (dest comb) @
        map (cons_fst VarK) (dest var) @
        maps (fn (a, net) => map (cons_fst (AtomK a)) (dest net)) (Symtab.dest atoms);

fun content net = map #2 (dest net);

fun merge eq net1 net2 =
  (* FIXME non-canonical merge order!?! *)
  fold (fn (k,v) => fn acc => insert_key eq v (k,acc)) (dest net2) (net1)

end;

(* Checks if module is compatible with interface while still exposing internal functions *)
structure NetInterfaceCheck = Net (struct type value = term end) : TERM_INDEX;