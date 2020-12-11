(*  Title:      Tools/Spec_Check/generator.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Random generators for Isabelle/ML's types.
*)

signature GENERATOR = sig
  include BASE_GENERATOR
  (* text generators *)
  val char : char gen
  val charRange : char * char -> char gen
  val charFrom : string -> char gen
  val charByType : (char -> bool) -> char gen
  val string : (int gen * char gen) -> string gen
  val substring : string gen -> substring gen
  val cochar : (char, 'b) co
  val costring : (string, 'b) co
  val cosubstring : (substring, 'b) co
  (* integer generators *)
  val int : int gen
  val int_pos : int gen
  val int_neg : int gen
  val int_nonpos : int gen
  val int_nonneg : int gen
  val coint : (int, 'b) co
  (* real generators *)
  val real : real gen
  val real_frac : real gen
  val real_pos : real gen
  val real_neg : real gen
  val real_nonpos : real gen
  val real_nonneg : real gen
  val real_finite : real gen
  (* function generators *)
  val function_const : 'c * 'b gen -> ('a -> 'b) gen
  val function_strict : int -> ''a gen * 'b gen -> (''a -> 'b) gen
  val function_lazy : ''a gen * 'b gen -> (''a -> 'b) gen
  val unit : unit gen
  val ref' : 'a gen -> 'a Unsynchronized.ref gen
  (* more generators *)
  val term : int -> term gen
  val term_fol : real * real * real -> int -> int -> term gen
  val term_fol_structure : int -> int -> term gen
  val term_fol_map : real * real * real -> term -> term gen
  val term_det : (int * int * 'a -> term * int * 'a) -> 'a -> term
  val free : int -> term gen
  val var : int -> term gen
  val const : int -> term gen
  val typ : int -> typ gen

  val stream : stream
end

structure Generator : GENERATOR =
struct

open Base_Generator

val stream = start (Random.new())

(* text *)

type char = Char.char
type string = String.string
type substring = Substring.substring


fun charRange (lo, hi) = map Char.chr (Random.range_int (Char.ord lo, Char.ord hi))
val char = charRange (Char.minChar, Char.maxChar)

fun charFrom s =
  choose (Vector.tabulate (String.size s, fn i => lift (String.sub (s, i))))

fun charByType p = filter p char

val string = vector CharVector.tabulate

fun substring gen r =
  let
    val (s, r') = gen r
    val (i, r'') = Random.range_int (0, String.size s) r'
    val (j, r''') = Random.range_int (0, String.size s - i) r''
  in
    (Substring.substring (s, i, j), r''')
  end

fun cochar c =
  if Char.ord c = 0 then variant 0
  else variant 1 o cochar (Char.chr (Char.ord c div 2))

fun cosubstring s = Substring.foldr (fn (c,v) => cochar c o v) (variant 0) s

fun costring s = cosubstring (Substring.full s)

(* integers *)
val digit = charRange (#"0", #"9")
val nonzero = string (lift 1, charRange (#"1", #"9"))
fun digits' n = string (Random.range_int (0, n-1), digit)
fun digits n = map2 op^ (nonzero, digits' n)

val maxDigits = 64
val ratio = 49

fun pos_or_neg f r =
  let
    val (s, r') = digits maxDigits r
  in (f (the (Int.fromString s)), r') end

val int_pos = pos_or_neg I
val int_neg = pos_or_neg Int.~
val zero = lift 0

val int_nonneg = chooseL' [(1, zero), (ratio, int_pos)]
val int_nonpos = chooseL' [(1, zero), (ratio, int_neg)]
val int = chooseL [int_nonneg, int_nonpos]

fun coint n =
  if n = 0 then variant 0
  else if n < 0 then variant 1 o coint (~ n)
  else variant 2 o coint (n div 2)

(* reals *)
val digits = string (Random.range_int (1, Real.precision), charRange(#"0", #"9"))

fun real_frac r =
  let val (s, r') = digits r
  in (the (Real.fromString s), r') end

val {exp=minExp,...} = Real.toManExp Real.minPos
val {exp=maxExp,...} = Real.toManExp Real.posInf

val ratio = 99

fun mk r =
  let
    val (a, r') = digits r
    val (b, r'') = digits r'
    val (e, r''') = Random.range_int  (minExp div 4, maxExp div 4) r''
    val x = String.concat [a, ".", b, "E", Int.toString e]
  in
    (the (Real.fromString x), r''')
  end

val real_pos = chooseL' (List.map ((pair 1) o lift)
    [Real.posInf, Real.maxFinite, Real.minPos, Real.minNormalPos] @ [(ratio, mk)])

val real_neg = map Real.~ real_pos

val real_zero = Real.fromInt 0
val real_nonneg = chooseL' [(1, lift real_zero), (ratio, real_pos)]
val real_nonpos = chooseL' [(1, lift real_zero), (ratio, real_neg)]

val real = chooseL [real_nonneg, real_nonpos]

val real_finite = filter Real.isFinite real

(*alternate list generator - uses an integer generator to determine list length*)
fun list' int gen = vector List.tabulate (int, gen);

(* more function generators *)

fun function_const (_, gen2) r =
  let
    val (v, r') = gen2 r
  in (fn _ => v, r') end;

fun function_strict size (gen1, gen2) r =
  let
    val (def, r') = gen2 r
    val (table, r'') = list' (fn s => (size, s)) (zip (gen1, gen2)) r'
  in (fn v1 => the_default def (AList.lookup (op =) table v1), r'') end;

fun function_lazy (gen1, gen2) r =
  let
    val (initial1, r') = gen1 r
    val (initial2, internal) = gen2 r'
    val seed = Unsynchronized.ref internal
    val table = Unsynchronized.ref [(initial1, initial2)]
    fun new_entry k =
      let
        val (new_val, new_seed) = gen2 (!seed)
        val _ =  seed := new_seed
        val _ = table := AList.update (op =) (k, new_val) (!table)
      in new_val end
  in
    (fn v1 =>
      case AList.lookup (op =) (!table) v1 of
        NONE => new_entry v1
      | SOME v2 => v2, r')
  end;

(* unit *)

fun unit r = ((), r);

(* references *)

fun ref' gen r =
  let val (value, r') = gen r
  in (Unsynchronized.ref value, r') end;

(* types and terms *)

val sort_string = selectL ["sort1", "sort2", "sort3"];
val type_string = selectL ["TCon1", "TCon2", "TCon3"];
val tvar_string = selectL ["a", "b", "c"];

val func_string = selectL ((Char.ord #"f" upto Char.ord #"h") |> List.map (Char.chr #> Char.toString));
val const_string = selectL ((Char.ord #"a" upto Char.ord #"f" - 1) |> List.map (Char.chr #> Char.toString));
val var_string = selectL ((Char.ord #"x" upto Char.ord #"z") |> List.map (Char.chr #> Char.toString));
val index = selectL [0, 1, 2, 3];
val bound_index = selectL [0, 1, 2, 3];

val sort = list (flip (1.0/3.0)) sort_string;

fun typ n =
  let
    fun type' m = map Type (zip (type_string, list (flip 0.25) (typ m)))
    val tfree = map TFree (zip (tvar_string, sort))
    val tvar = map TVar (zip (zip (tvar_string, index), sort))
  in
    if n = 0 then chooseL [tfree, tvar]
    else chooseL [type' (n div 2), tfree, tvar]
  end;

fun term n =
  let
    val const = map Const (zip (const_string, typ 10))
    val free = map Free (zip (var_string, typ 10))
    val var = map Var (zip (zip (var_string, index), typ 10))
    val bound = map Bound bound_index
    fun abs m = map Abs (zip3 (var_string, typ 10, term m))
    fun app m = map (op $) (zip (term m, term m))
  in
    if n = 0 then chooseL [const, free, var, bound]
    else chooseL [const, free, var, bound, abs (n - 1), app (n div 2)]
  end;

datatype 'a node = Node of 'a * 'a node list

fun term_fol1 num_sym r =
  let
    fun ins target value (Node (node,children)) =
      if node = target
      then Node (node, Node (value, [])::children)
      else Node (node, List.map (ins target value) children)
    fun ins_at_random i (tree,r) =
      let val (target,r) = Random.range_int (0,i-1) r
      in
      (ins target i tree, r)
      end
    (* Abuse Bound to store the number of args without specifying a type *)
    fun conv_node (Node (_, [])) r = (Bound 0,r)
      | conv_node (Node (_, args)) r =
        (Bound (List.length args),r)
        |> fold (fn x => fn (acc,r) => conv_node x r |>> (fn x => acc $ x)) args 
  in
  fold ins_at_random (1 upto (num_sym - 1)) (Node (0,[]), r)
  |-> conv_node
  end

fun zip_list xs ys = case (xs,ys) of
     ([],_) => []
   | (_,[]) => []
   | (x::xs,y::ys) => (x,y) :: zip_list xs ys

fun clamp (lower,upper) x = if x < lower then lower else if x > upper then upper else x

fun get_num_args avg_args num_sym r =
  binom_dist 0.5 (avg_args * 2) r
  |>> clamp (0,num_sym)

fun distribute_num_sym num_args num_sym r =
  let fun f (acc,r) = Random.range_int (0,num_args) r |>> (fn x => x::acc)
      val (intervals,r) = fold (fn _ => f) (1 upto num_args - 1) ([],r) |>> Library.sort int_ord
      val intervals = 0::intervals @ [num_sym]
      val args_size = zip_list (tl intervals) intervals |> List.map (fn (x,y) => x - y)
  in (args_size,r) end

fun term_fol_structure avg_args num_sym r =
  if num_sym <= 1
  then (Bound 0, r)
  else let
    val num_sym = num_sym - 1 (* Function *)
    val (num_args,r) = get_num_args avg_args num_sym r
    (* Abuse Bound to store the number of args without specifying a type *)
    val (func,r) = (Bound num_args,r)
    val (args_size,r) =
      if num_args = 0
      then ([],r) (* This drops some symbols => lower total than requested by num_sym *)
      else distribute_num_sym num_args num_sym r
    val (args,r) =
      fold (fn x => fn (acc,r) => term_fol_structure avg_args x r |>> (fn y => y :: acc)) args_size ([],r)
  in (Term.list_comb (func,args),r) end

fun ifMult _ _ [] [x] = x
  | ifMult rand cumulativ (f::fs) (x::xs) =
    let val c = cumulativ + f in
    if rand < c then x
    else ifMult rand c fs xs
    end
  | ifMult _ _ _ _ = raise Fail "Invalid arguments to ifMult"

fun generic_type 0 = TVar (("'a", 0), [])
  | generic_type n =
      let val name = "'" ^ Char.toString (Char.chr (Char.ord #"a" + n)) in
      Type ("fun", [TVar ((name,0), []), generic_type (n-1)]) end

(* Implement more sophisticated selection. Remember already used variables and their types.
  Choose different names for free etc. *)
fun var 0 = map Var (zip (zip (var_string, index), lift (generic_type 0)))
  | var n = map Var (zip (zip (func_string, index), lift (generic_type n)))
fun const 0 = map Const (zip (const_string, lift (generic_type 0)))
  | const n = map Const (zip (func_string, lift (generic_type n)))
fun free 0 = map Free (zip (const_string, lift (generic_type 0)))
  | free n = map Free (zip (func_string, lift (generic_type n)))

fun term_fol_map (freq_bound, freq_free, freq_var) term r =
  let fun aux bounds types term r =
        let val (rand,r) = Random.real r
            val ifMult = ifMult rand 0.0 [freq_bound, freq_free, freq_var]
        in case term of
            Bound n =>
              ifMult [lift (Bound 0), free n, var n, const n] r
          | fst$snd =>
            let val (fst,r) = aux bounds types fst r
                val (snd,r) = aux bounds types snd r
            in (fst$snd, r) end
          | _ => raise Fail "Term must only consist of $ and Bounds where index = number of args"
        end
  in aux [] [] term r end

fun term_fol freq avg_args num_sym r =
  term_fol_structure avg_args num_sym r
  |-> term_fol_map freq

fun incr_nth (x::xs) 0 = x+1 :: xs
  | incr_nth [] n = incr_nth (0::[]) n
  | incr_nth (x::xs) n = x :: incr_nth xs (n-1)

fun term_det f init_acc =
  let fun aux indices height acc =
    let
      (* indices stores the amount of symbols so far at each height *)
      val indices = incr_nth indices height
      val index = nth indices height
      val (sym,num_args,acc) = f (height,index,acc)
      fun fold_aux (acc, indices, state) = aux indices (height + 1) state |> (fn (x,y,z) => (x :: acc,y,z))
      val () = writeln (@{make_string} sym ^ @{make_string} num_args ^ @{make_string} indices)
      val (args,indices,acc) = fold (fn _ => fold_aux) (1 upto num_args) ([],indices,acc)
      val () = writeln (@{make_string} args)
    in
    (fold (fn x => fn y => y $ x) (rev args) sym, indices, acc)
    end
  in
  aux [] 0 init_acc |> (fn (x,y,z) => x)
  end
end
