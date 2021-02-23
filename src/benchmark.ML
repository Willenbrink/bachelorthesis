datatype tag =
    Test of string
  | Input of string
  | Index of string

fun string_of_tag x = case x of
    Test x => x
  | Input x => x
  | Index x => x

fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6

fun compare tags tests (resultss : {cpu: Time.time, elapsed: Time.time, gc: Time.time} list list) =
    (fold (fn name => fn acc => StringCvt.padLeft #" " 6 name ^ "\t" ^ acc) tags "" |> writeln;
    map_index
      (fn (i,name) =>
        fold (fn timing => fn acc => (#elapsed timing |> Time.toReal |> print_real) ^ "\t" ^ acc)
          (map (fn el => nth el i) resultss) name)
      tests |> map writeln)

fun compare (benchmark : (tag list * Timing.timing) list) name
            (filter_x : tag -> bool) (filter_y : tag -> bool) (filter_v : tag -> bool) =
  let
    fun concat (tag::tags) = fold (fn x => fn y => string_of_tag x ^ "-" ^ y) tags (string_of_tag tag)
    val xlabels : tag list list =
      benchmark
      |> map fst
      |> map (filter filter_x)
      |> filter (not o null)
      |> distinct (op =)
    val ylabels : tag list list =
      benchmark
      |> map fst
      |> map (filter filter_y)
      |> filter (not o null)
      |> distinct (op =)
    val values : (tag list * Timing.timing option) list =
      benchmark
      (* Split tags for later *)
      |> map (fn (ts,v) => (filter (fn tag => filter_x tag orelse filter_y tag) ts, (ts,v)))
      (* Remove any value which is not addressed by both x and y labels *)
      |> filter_out (fn (ts,_) => null ts)
      (* Coalesce values addressed by same (x,y) pair *)
      |> AList.coalesce (eq_set (op =))
      |> map (apsnd (fn xs => (* (x,y) * (tags,value) list *)
                      (* Check if value is associated with all the tags we want *)
                      filter (fn (tags,_) => exists filter_x tags andalso exists filter_y tags andalso exists filter_v tags) xs
                      (* Raise warning if multiple values remain *)
                      |> (fn [] => NONE
                           | [(_,x)] => SOME x
                           | (_,x)::_ => (warning "Values left, taking first"; SOME x))))
    val matrix = map (fn x => map (fn y => (x,y)) ylabels) xlabels

    val xlabels' =
      map concat xlabels |> rev
    val xsize = 8
    fun pad x = StringCvt.padLeft #" " xsize ("  " ^ x)
    val () =
      fold (fn tag => fn acc => pad tag ^ acc) xlabels' ("    " ^ name)
      |> writeln
    fun write_row ylabel =
      values
      |> filter (fn (tags,_) => exists (fn tag => string_of_tag tag = ylabel) tags)
      |> sort (fn ((x,_),(y,_)) => string_ord (concat x, concat y))
      |> map snd
      |> (fn x => fold (fn timing => fn acc =>
                           (case timing of
                                 NONE => ""
                               | SOME timing => #elapsed (timing : Timing.timing) |> Time.toReal |> print_real |> pad)
                          ^ acc
                       )
                       x ("\t " ^ ylabel))
      |> writeln
    fun write_row ylabel =
      xlabels'
      (* Lookup associated values *)
      |> map (fn x => AList.lookup (fn (t1,t2) => eq_set (string_ord #> is_equal) (t1, map string_of_tag t2)) values [x,ylabel])
      |> map (fn NONE => NONE | SOME NONE => NONE | SOME (SOME xs) => SOME xs)
      |> (fn x => fold (fn timing => fn acc =>
                           (case timing of
                                 NONE => ""
                               | SOME timing => #elapsed (timing : Timing.timing) |> Time.toReal |> print_real |> pad)
                          ^ acc
                       )
                       x ("\t " ^ ylabel))
      |> writeln
  in
    ylabels
    |> map concat
    |> map write_row;
    writeln " "
  end


functor Benchmark (Index : TERM_INDEX) =
struct

structure Gen = Generator

val eq = Term.aconv_untyped

fun replace_subterm sym t r =
  let val (f,args) = Term.strip_comb t
      val (index,r) =  Gen_Base.range_int (~1,length args - 1) r
      (* Generate two random values, pass r1 to rec-call, ignore returned r and return r2 instead.
         This simply avoids some annoyance with passing values around. *)
      val (r1,r2) = Random.split r
  in
  if index = ~1
  then (Term.list_comb (sym r1 |> fst, args), r2)
  else (Term.list_comb (f,nth_map index (fn t => replace_subterm sym t r1 |> fst) args), r2)
  end

fun terms_not_in_net_gen amount net_gen r = (* Returns (term,net) where term is guaranteed to not be in the net *)
  let
    val (net,r) = Gen.filter (fn n => Index.content n <> []) net_gen r
    val (con,r) = Gen.shuffle (Index.content net) r
    val terms = take amount con
    val net = fold (fn t => Index.delete (curry eq t) t) (take (length con div 10) con) net
  in
  ((terms,net),r)
  end

fun terms_in_net_gen amount net_gen r = (* Returns (term,net) where term is guaranteed to be in the net *)
  let
    val (net,r) = net_gen r
    val (con,r) = Gen.shuffle (Index.content net) r
    val (terms,r) =
      if amount < length con
      then (take amount con,r)
      else
        let val ((con2,_),r) = terms_in_net_gen (amount - length con) (Gen.lift net) r
        in (con @ con2, r) end
        
  in
  ((terms,net),r)
  end

fun term_instance_gen term_gen r =
  let val (base_term,r) = term_gen r
      val (general_term,r) = replace_subterm (Gen.var (~1) 1 |> Gen.lift) base_term r
  in
  ((base_term,general_term),r)
  end

fun term_unif_gen term_gen r =
  let val (base_term,r) = term_gen r
      val (term1,r) = replace_subterm (Gen.var (~1) 1 |> Gen.lift) base_term r
      val (term2,r) = replace_subterm (Gen.var (~2) 1 |> Gen.lift) base_term r
  in
  ((term1,term2),r)
  end



fun net_gen num_term term_gen r =
  let
    fun aux num_term r =
      case num_term of
        0 => (Index.empty,r)
      | _ =>
        let val (term,r) = term_gen r
            val (base,r) = aux (num_term - 1) r
        in (Index.insert_safe eq (term,term) base,r) end
  in 
  Gen_Base.range_int (0,num_term) r
  |-> aux
  end

fun add_timings {elapsed = elapsed1, cpu = cpu1, gc = gc1} {elapsed = elapsed2, cpu = cpu2, gc = gc2} =
  {elapsed = elapsed1 + elapsed2,
   cpu = cpu1 + cpu2,
   gc = gc1 + gc2}

fun timer name f_test inputs =
  let
    val r = Random.new ()
    fun add_results test test_total =
      (add_timings test test_total)
  in
  writeln (name);
  inputs
  |> map_index (fn (i,input) => r
          |> funpow i Random.next
          |> input
          |> fst (* Discard returned random value *)
          |> Timing.timing f_test
          |> fst)
  |> (fn list => fold add_results list {elapsed = Time.fromSeconds 0, cpu = Time.fromSeconds 0, gc = Time.fromSeconds 0})
  |> (fn test => (Test name,test))
  end

fun benchmark_basic net_list =
  let val term_in_net = map (fn n => terms_in_net_gen (Int.min (1000, Index.content n |> length)) (Gen.lift n)) net_list
      val term_not_in_net = map (terms_not_in_net_gen 1000 o Gen.lift) net_list in [
timer "Content of net"
      (Index.content)
      (map Gen.lift net_list),
timer "Insert terms"
      (fn (terms,net) => fold (fn term => Index.insert_safe eq (term,term)) terms net)
      (term_not_in_net),
timer "Delete terms"
      (fn (terms,net) => fold (fn t => Index.delete (curry eq t) t) terms net)
      (term_in_net)
] end

fun benchmark_lookup net_list = 
  let val nets = map Gen.lift net_list
      val term_in_net = map (terms_in_net_gen 1000) nets
      val term_not_in_net = map (terms_not_in_net_gen 100) nets in [
timer "Q: lookup existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_in_net)
(*
timer "Q: lookup non-existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_not_in_net)
*)
] end

fun benchmark_queries net_list =
  let val nets = map Gen.lift net_list
      val term_in_net = map (terms_in_net_gen 1000) nets
      val term_not_in_net = map (terms_not_in_net_gen 100) nets in [
timer "Q: lookup existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_in_net),
timer "Q: instances existing term"
      (fn (t,n) => map (Index.instances n) t)
      (term_in_net),
timer "Q: generalisations existing term"
      (fn (t,n) => map (Index.generalisations n) t)
      (term_in_net),
timer "Q: unifiables existing term"
      (fn (t,n) => map (Index.unifiables n) t)
      (term_in_net)
(*,
timer "Q: lookup non-existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_not_in_net),
timer "Q: instances non-existing term"
      (fn (t,n) => map (Index.instances n) t)
      (term_not_in_net),
timer "Q: generalisations non-existing term"
      (fn (t,n) => map (Index.generalisations n) t)
      (term_not_in_net),
timer "Q: unifiables non-existing term"
      (fn (t,n) => map (Index.unifiables n) t)
      (term_not_in_net)*)
] end


fun create_indices group_size terms =
  let val termss = chop_groups group_size terms
      fun init [] = []
        | init [_] = []
        | init (x::xs) = x :: init xs
  in
  (* Start with empty index, insert first group of terms. Take copy of index, insert second group, etc.
    Return a list of indices each with a differing amount of terms in them. *)
  fold (fn ts => fn (index::indices) => (fold (fn t => Index.insert_safe eq (t,t)) ts index)::index::indices) termss [Index.empty]
  |> init
  end
end