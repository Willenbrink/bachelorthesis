theory "Test"
imports
  Pure
  Spec_Check2.Spec_Check
begin
ML_file "util.ML"
ML_file "term_index.ML"
ML_file "net.ML"
ML_file "path.ML"
ML_file "path_termtab.ML"
ML_file "termtab.ML"
ML_file "pprinter.ML"
ML_file "term_gen.ML"
ML_file "net_gen.ML"
ML_file "tester.ML"
ML_file "benchmark_util.ML"
ML_file "benchmark.ML"

ML "open Pprinter Term_Gen"
setup "term_pat_setup"
setup "type_pat_setup"

(* Testing and Benchmarking *)

ML \<open>
val eq = Term.aconv_untyped
structure G = Generator
structure N = NetIndex
structure P = PathIndex
structure PTT = PathTT
structure TT = TT_Index
structure NetTest = Tester(N);
structure PathTest = Tester(P);
structure PathTTTest = Tester(PTT);
structure TTTest = Tester(TT);
structure NBench = Benchmark(N);
structure PBench = Benchmark(P);
structure PTTBench = Benchmark(PTT);
structure TTBench = Benchmark(TT);
\<close>
(*
ML \<open>ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ)\<close>
*)

declare [[spec_check_max_success = 1000]]
ML_command \<open>
(* Benchmark for Intersection on Lists *)
val sgen = G.list (G.range_int (10,50)) (G.pos 30)
val ssgen = G.list (G.lift 40) sgen
val inter2 = Spec_Check.check_base (fn r => ssgen r |-> G.shuffle) "" (Property.prop (fn xs => (inters_orig (int_ord) xs; true)) )
 @{context} (Random.deterministic_seed 1);
val inter1 = Spec_Check.check_base (fn r => ssgen r |-> G.shuffle) "" (Property.prop (fn xs => (inters' (int_ord) xs; true)) )
 @{context} (Random.deterministic_seed 1)
\<close>

declare [[spec_check_max_success = 100]]
ML_command \<open>
(* Index tests *)
val tests = [
  ("Path", PathTest.test_all),
  ("PathTT", PathTTTest.test_all),
  ("Net", NetTest.test_all),
  ("TT", TTTest.test (TTTest.test_util @ TTTest.test_modifying))
];

fold (fn (name,test) => fn r => (writeln name; test @{context} r)) tests (Random.new ())
\<close>

ML \<open>
fun gen_seeds seed sizes =
  fold (fn (repeats,n) => fn (r,acc) =>
    let val (rs,r) = funpow_yield repeats Random.split r
    in (r, (n,rs) :: acc) end
  ) sizes (seed,[])
  |> snd

val sizes =
  [(1000,10),(1000,20),(1000,30),(1000,40),(1000,50),(1000,70),(1000,100),(100,200),(100,500),(100,700),(10,1000),(10,3000),(10,5000)]
  (* For testing runtime before wasting an hour *)
  |> map (fn (x,y) => (x div 1000, y))
  (*
  *)
  |> gen_seeds (Random.deterministic_seed 1)

val depth = 6
val argr = (0,4)

fun test_single size = [
("TestName", term_with_var size 10 depth argr)
]

val gen_distinct =
  let fun gen reuse size = term_var_reuse (Real.floor (Real.fromInt size * reuse)) depth argr
  in
    [("NR", gen 10.0), ("LR", gen 1.0), ("MR", gen 0.1) , ("HR",gen 0.01)]
    |> map (apfst Gen)
  end

val gen_var =
  let fun gen var size = term_with_var size var depth argr
  in
    [("NV", gen 0), ("LV", gen 1), ("MV", gen 3), ("HV", gen 10)]
    |> map (apfst Gen)
  end

val gens = gen_var

fun bench tag_index (net_gen : int -> term Generator.gen -> 'a Generator.gen) benchmark gens sizes =
  cross gens sizes
  |> maps (fn ((tag_gen,term_gen),(size,seeds)) =>
      map (fn r => (net_gen size (term_gen size) r |> fst, term_gen size)) seeds
       |> benchmark
       |> map (fn (tag_test, res) => ([
              tag_test,
              tag_index,
              tag_gen,
              Size ("Terms:" ^ @{make_string} size ^ "-Runs:" ^ @{make_string} (length seeds))
            ], res)))
\<close>

ML \<open>
val dn_bench = bench (Index "DN") NBench.index_gen (NBench.benchmark [NBench.benchmark_basic, NBench.benchmark_queries])
val pi_bench = bench (Index "PI_") PBench.index_gen (PBench.benchmark [PBench.benchmark_basic, PBench.benchmark_queries])
val pitt_bench = bench (Index "PITT") PTTBench.index_gen (PTTBench.benchmark [PTTBench.benchmark_basic, PTTBench.benchmark_queries])
val tt_bench = bench (Index "TT_") TTBench.index_gen (TTBench.benchmark [TTBench.benchmark_basic, TTBench.benchmark_variants])

val benches = [
pi_bench,
pitt_bench,
dn_bench,
tt_bench
]

val _ =
  benches
  |> map (fn b => b gens (gen_seeds (Random.deterministic_seed 1) [(1,1)]))
  |> flat

fun gc () = ML_Heap.full_gc ()
;ML_Heap.share_common_data (); gc ();
val (timing, benchmarks) = Timing.timing (fn benches =>
  fold (fn b => fn acc => (gc (); b gens sizes :: acc)) benches []
  |> rev
  |> flat)
  benches
;fold (fn x => fn acc => x ^ "\n" ^ acc) (map (@{make_string}) benchmarks) ""
|> writeln
\<close>

ML \<open>
(* Include benchmark from test_data here to reproduce tables *)
\<close>

ML \<open>
val () = writeln (@{make_string} timing)
fun compare name x_label y_label selection =
  table benchmarks (print_values selection) name x_label y_label
\<close>

ML_command \<open>
(* To obtain .csvs of these tables:
- replace size:X-runs:Y with X
- remove spaces from test names
- If necessary, multiply by 10 or 100 for test sizes with less runs

Regexes are recommended for this
 *)
;compare "queries.csv" (Index "") (Test "") [Gen "", Size "200-"]

;compare "variants.csv" (Index "") (Size "") [Test "variants of existing", Gen ""]
;compare "generalisations.csv" (Index "") (Size "") [Test "generalisations of existing", Gen ""]
;compare "instances.csv" (Index "") (Size "") [Test "instances of generalised", Gen ""]
;compare "unifiables.csv" (Index "") (Size "") [Test "unifiables of generalised", Gen ""]
;compare "unifiables2.csv" (Index "") (Gen "") [Test "unifiables of generalised", Size "40-"]

;compare "ins.csv" (Index "") (Size "") [Test "Insert", Gen ""]
;compare "del.csv" (Index "") (Size "") [Test "Delete", Gen ""]
\<close>

end
