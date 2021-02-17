functor Benchmark (Index : TERM_INDEX where type value = term) =
struct

structure Gen = Generator

val eq = Term.aconv_untyped

fun replace_subterm sym t r =
  let val (f,args) = Term.strip_comb t
      val (index,r) =  Random.range_int (~1,length args - 1) r
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
    val net = fold (fn t => Index.delete eq (t,t)) (take (length con div 10) con) net
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
  Random.range_int (0,num_term) r
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
  |> (fn test => (name,test))
  end

fun benchmark_basic net_list =
  let val nets = map Gen.lift net_list
      val term_in_net = map (terms_in_net_gen 1000) nets
      val term_not_in_net = map (terms_not_in_net_gen 1000) nets in [
timer "Content of net"
      (Index.content)
      (nets),
timer "Insert terms"
      (fn (terms,net) => fold (fn term => Index.insert_safe eq (term,term)) terms net)
      (term_not_in_net),
timer "Delete terms"
      (fn (terms,net) => fold (fn term => Index.delete eq (term,term)) terms net)
      (term_in_net),
timer "Lookup existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_in_net),
timer "Lookup non-existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_not_in_net),
timer "unifiables existing term"
      (fn (t,n) => map (Index.unifiables n) t)
      (term_in_net)
] end

fun benchmark_queries net_list =
  let val nets = map Gen.lift net_list
      val term_in_net = map (terms_in_net_gen 1000) nets
      val term_not_in_net = map (terms_not_in_net_gen 100) nets in [
timer "Lookup existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_in_net),
timer "instances existing term"
      (fn (t,n) => map (Index.instances n) t)
      (term_in_net),
timer "generalisations existing term"
      (fn (t,n) => map (Index.generalisations n) t)
      (term_in_net),
timer "unifiables existing term"
      (fn (t,n) => map (Index.unifiables n) t)
      (term_in_net)
(*,
timer "Lookup non-existing term"
      (fn (t,n) => map (Index.lookup n) t)
      (term_not_in_net),
timer "instances non-existing term"
      (fn (t,n) => map (Index.instances n) t)
      (term_not_in_net),
timer "generalisations non-existing term"
      (fn (t,n) => map (Index.generalisations n) t)
      (term_not_in_net),
timer "unifiables non-existing term"
      (fn (t,n) => map (Index.unifiables n) t)
      (term_not_in_net)*)
] end
end

fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6

fun compare categories tests (resultss : {cpu: Time.time, elapsed: Time.time, gc: Time.time} list list) =
    (fold (fn name => fn acc => StringCvt.padLeft #" " 6 name ^ "\t" ^ acc) categories "" |> writeln;
    map_index
      (fn (i,name) =>
        fold (fn timing => fn acc => (#elapsed timing |> Time.toReal |> print_real) ^ "\t" ^ acc)
          (map (fn el => nth el i) resultss) name)
      tests |> map writeln)