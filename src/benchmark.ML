functor Benchmark (Index : TERM_INDEX) =
struct

structure Gen = Generator
structure NG = Net_Gen(Index)

val eq = Term.aconv_untyped

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
  let val term_in_net = map (fn n => NG.terms_in_net_gen (Int.min (1000, Index.content n |> length)) (Gen.lift n)) net_list
      val term_not_in_net = map (NG.terms_not_in_net_gen 1000 o Gen.lift) net_list in [
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
      val term_in_net = map (NG.terms_in_net_gen 1000) nets
      val term_not_in_net = map (NG.terms_not_in_net_gen 100) nets in [
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
      val term_in_net = map (NG.terms_in_net_gen 1000) nets
      val term_not_in_net = map (NG.terms_not_in_net_gen 100) nets in [
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