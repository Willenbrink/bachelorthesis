functor Benchmark (Index : TERM_INDEX) =
struct

structure Gen = Generator
structure NG = Net_Gen(Index)
val index_gen = NG.index_gen

val eq = Term.aconv_untyped

fun benchmark_basic net_list =
  let
    val term_in_net = map (fn (n,t) => NG.terms_in_net_gen (Index.content n |> length) (Gen.lift n)) net_list
    val term_not_in_net = map (fn (n,t) => NG.terms_not_in_net_gen t (Index.content n |> length) (Gen.lift n)) net_list
  in
    [
      timer "Content of net"
        (Index.content)
        (map (fst #> Gen.lift) net_list),
      timer "Insert terms"
        (fn (terms,net) => fold (fn term => Index.insert_safe eq (term,term)) terms net) (* Only different in \<alpha>-equi ensured *)
        (term_not_in_net),
      timer "Delete terms"
        (fn (terms,net) => fold (fn t => Index.delete (curry eq t) t) terms net)
        (term_in_net)
    ]
  end               

fun benchmark_variants net_list = 
  let
    val term_in_net = map (fn (n,t) => NG.terms_in_net_gen (Index.content n |> length) (Gen.lift n)) net_list
    val term_not_in_net = map (fn (n,t) => NG.terms_not_in_net_gen t (Index.content n |> length) (Gen.lift n)) net_list
  in
    [
      timer "Q: variants existing term"
        (fn (t,n) => map (Index.variants n) t)
        (term_in_net),
      timer "Q: variants non-ex term"
        (fn (t,n) => map (Index.variants n) t)
        (term_not_in_net)
    ]
  end

fun benchmark_queries net_list =
  let
    val term_in_net = map (fn (n,t) => NG.terms_in_net_gen (Index.content n |> length) (Gen.lift n)) net_list
    val term_not_in_net = map (fn (n,t) => NG.terms_not_in_net_gen t (Index.content n |> length) (Gen.lift n)) net_list
  in
    [
      timer "Q: variants existing term"
        (fn (t,n) => map (Index.variants n) t)
        (term_in_net),
      timer "Q: instances existing term"
        (fn (t,n) => map (Index.instances n) t)
        (term_in_net),
      timer "Q: generalisations existing term"
        (fn (t,n) => map (Index.generalisations n) t)
        (term_in_net),
      timer "Q: unifiables existing term"
        (fn (t,n) => map (Index.unifiables n) t)
        (term_in_net),
      timer "Q: variants non-ex term"
        (fn (t,n) => map (Index.variants n) t)
        (term_not_in_net),
      timer "Q: instances non-ex term"
        (fn (t,n) => map (Index.instances n) t)
        (term_not_in_net),
      timer "Q: generalisations non-ex term"
        (fn (t,n) => map (Index.generalisations n) t)
        (term_not_in_net),
      timer "Q: unifiables non-ex term"
        (fn (t,n) => map (Index.unifiables n) t)
        (term_not_in_net)
      ]
  end
end