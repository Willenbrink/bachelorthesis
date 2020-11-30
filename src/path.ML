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

  val lookup: term net -> key list -> term list
  val match_term: term net -> term -> term list
  val unify_term: term net -> term -> term list
  val entries: 'a net -> 'a list
  val subtract: ('a * 'a -> bool) -> 'a net -> 'a net -> 'a list
  val merge: (term * term -> bool) -> term net * term net -> term net
  val content: 'a net -> 'a list
end;

structure Path (*: NET*) =
struct
(* TODO should an empty key be valid?
   TODO should a key list address one node or multiple?
   TODO is_first_order function in term!
 *)

fun >>= (x,f) = Option.map f x
infix 1 >>=

(* Fun(name,index,key_remainder) where key_remainder describes the path to the leaf *)
datatype symbol = VarS
                | AtomS of string
datatype key = End of symbol | Fun of symbol * int * key

fun sym_ord (VarS, VarS) = EQUAL
  | sym_ord (VarS, _) = LESS
  | sym_ord (_, VarS) = GREATER
  | sym_ord ((AtomS n1), (AtomS n2)) = fast_string_ord (n1,n2)

structure Stab = Table(type key = symbol val ord = sym_ord);
type 'a content = 'a list Stab.table
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
          val sym = symbol_of_term func in
      case args of
        [] => [End sym]
      | args => args
             |> map key_of_term
             |> Library.map_index (fn (i,keys) => map (fn k => Fun(sym,i,k)) keys)
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

(*** Insertion into a path index tree ***)

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
fun insert_one eq (key, v) (Node (con,tree)) : 'a net = case key of
      End n => Node (append_sym eq (n,v) con, tree)
    | Fun (name,index,key) =>
        let fun ins tree = insert_one eq (key,v) tree
            fun ins_list xs = nth_map_default index ins empty xs
            fun ins_symtab f tree = Stab.map_default (name,[]) f tree
        in Node (con, ins_symtab ins_list tree) end

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
      End n => Node (Stab.map_default (n,[]) rem con, tree)
    | Fun (name,index,key) =>
           delete_one eq (key,v)
        |> (fn f => Library.nth_map index (fn xs => f xs))
        |> (fn x => Stab.map_default (name,[]) x tree)
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
        con |> Stab.dest 
            |> maps snd
      val con_snd =
        tree |> Stab.dest
             |> maps snd
             |> maps content
  in con_fst @ con_snd end

(*Return the list of items at the given node, [] if no such node*)
fun lookup_one (Node (con,tree)) key = case key of
    End n => (case Stab.lookup con n of NONE => [] | SOME xs => xs)
  | Fun (name,index,key) =>
       Stab.lookup tree name
       >>= (fn xs => Library.nth xs index)
       >>= (fn x => lookup_one x key)
       |> Option.valOf

fun lookup tree keys =
    let val acc = content tree
        fun intersect (acc,k) = inter Term.aconv_untyped acc (lookup_one tree k)
    in Library.foldl intersect (acc,keys) end

fun match unif node term =
  let
    fun lookup_term table term =
      case term of
      (* Replace var in term arbitrarily TODO only for unif! *)
        Var _ => Stab.dest table |> maps snd
      | Abs _ => Stab.dest table |> maps snd
      | _$_ => raise Fail "Impossible"
      | rest => Stab.lookup_list table (symbol_of_term rest)

   fun aux (node as Node(con,tree)) t = case t of
      _ $ _ =>
        let val (func, args) = strip_comb t
            val inttabs =
              case (unif, symbol_of_term func) of
                  (true, VarS) => Stab.dest tree |> map snd
                | (true, atom) => 
                    (case Stab.lookup tree atom of NONE => [] | SOME x => [x])
                  @ (case Stab.lookup tree VarS of NONE => [] | SOME x => [x])
                | (false, symbol) => case Stab.lookup tree symbol of NONE => [] | SOME x => [x]
            fun match (index,term) =
              maps (fn x => Library.nth x index |> (fn x =>  aux x term)) inttabs
        in
        Library.fold_index
          (fn arg => fn acc => inter Term.aconv_untyped acc (match arg))
          args (aux node func)
        end
    | rest =>
      if unif
      then union Term.aconv_untyped (Stab.lookup_list con VarS) (lookup_term con rest)
      else lookup_term con rest
  in aux node term end

val match_term = match false
val unify_term = match true

val entries = content (* TODO are they really the same? *)

fun merge eq (tree1, tree2) =
  fold (fn t => insert_term_safe eq (t,t)) (content tree2) tree1  (* FIXME non-canonical merge order!?! *)

fun subtract eq tree1 tree2 = Library.subtract eq (content tree1) (content tree2)
end;
