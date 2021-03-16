functor Benchmark (Index : TERM_INDEX) =
struct

local
structure Gen = Generator
structure NG = Net_Gen(Index)

val eq = Term.aconv_untyped
in

fun timer name f_test inputs =
  let val r = Random.new ()
  in
    (*writeln (name);*)
    inputs
    |> map_index (fn (i,input) => r
            |> funpow i Random.next
            |> input
            |> fst (* Discard returned random value *)
            |> Timing.timing f_test
            |> fst)
    |> map (#cpu)
    |> (fn list => fold (curry op +) list (Time.fromSeconds 0))
    |> (fn test => (Test name,test))
  end

val reuse_factor = 1

fun benchmark_basic net_list =
  let
    val term_in_net = map (fn n => NG.terms_in_net_gen (reuse_factor * (Index.content n |> length)) (Gen.lift n)) net_list
    val term_not_in_net = map (fn n => NG.terms_in_net_gen (reuse_factor * (Index.content n |> length)) (Gen.lift n)) net_list
  in
    [
      timer "Content of net"
        (Index.content)
        (map Gen.lift net_list),
      timer "Insert terms"
        (fn (terms,net) => fold (fn term => Index.insert_safe eq (term,term)) terms net)
        (term_not_in_net),
      timer "Delete terms"
        (fn (terms,net) => fold (fn t => Index.delete (curry eq t) t) terms net)
        (map (fn n => Gen.lift (Index.content n, n)) net_list)
    ]
  end               

fun benchmark_lookup net_list = 
  let
    val term_in_net = map (fn n => NG.terms_in_net_gen (reuse_factor * (Index.content n |> length)) (Gen.lift n)) net_list
    val term_not_in_net = map (fn n => NG.terms_in_net_gen (reuse_factor * (Index.content n |> length)) (Gen.lift n)) net_list
  in
    [
      timer "Q: lookup existing term"
        (fn (t,n) => map (Index.lookup n) t)
        (term_in_net)
      (*
      timer "Q: lookup non-existing term"
        (fn (t,n) => map (Index.lookup n) t)
        (term_not_in_net)
      *)
    ]
  end

fun benchmark_queries net_list =
  let
    val term_in_net = map (fn n => NG.terms_in_net_gen (reuse_factor * (Index.content n |> length)) (Gen.lift n)) net_list
    val term_not_in_net = map (fn n => NG.terms_in_net_gen (reuse_factor * (Index.content n |> length)) (Gen.lift n)) net_list
  in
    [
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
        (term_not_in_net)
      *)
      ]
  end

val index_gen = NG.index_gen

fun create_indices group_size terms =
  let
    val termss = chop_groups group_size terms
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
end