theory "Test"
  imports Main "../spec_check/src/Spec_Check"
begin
ML_file "term_index.ML"
ML_file "net.ML"
ML_file "path.ML"
ML_file "pprinter.ML"
ML_file "term_gen.ML"
ML_file "tester.ML"
ML_file "benchmark.ML"
ML "open Pprinter Term_Gen"
setup "term_pat_setup"
setup "type_pat_setup"

(* Testing and Benchmarking *)

ML \<open>
val eq = Term.aconv_untyped
structure V = struct type value = term val eq = Term.aconv_untyped end
structure N = Net(V)
structure P = Path(V)
structure NetTest = Tester(N);
structure PathTest = Tester(P);
structure NetBench = Benchmark(N);
structure PathBench = Benchmark(P);
\<close>

ML \<open>
(*
writeln "Path";
PathTest.test ();
*)

writeln "Net";
NetTest.test ();
\<close>

ML \<open>
val size = 1000
\<close>

ML \<open>
Timing.timing (fn () => Random.new () |> (term_ground 0.0 5 (0,10))) () |> fst;
Timing.timing (fn () => Random.new () |> PathBench.net_gen size (term_ground 0.0 5 (0,8))) () |> fst;
\<close>

ML \<open>
val term_gens = [
(* Reuse of symbols *)
("LR", term_ground 0.0 5 (2,6)),
("MR", term_ground 0.3 5 (2,6)),
("HR", term_ground 0.5 5 (2,6)),
("LV", term_with_var 0.5 5 (2,6)),
("MV", term_with_var 1.0 5 (2,6)),
("HV", term_with_var 2.0 5 (2,6))
]
val termss = map (fn (name,gen) => (name,funpow_yield size gen (Random.new ()) |> fst)) term_gens
val index_list = map (fn (name,terms) =>
  (name,
   fold (fn t => P.insert_safe eq (t,t)) terms P.empty,
   fold (fn t => N.insert_safe eq (t,t)) terms N.empty)) termss
\<close>
ML \<open>
val pathb = map (fn (name,path,_) => ("PI-" ^ name, PathBench.benchmark_queries [path])) index_list;
val netb = map (fn (name,_,net) => ("DN-" ^ name, NetBench.benchmark_queries [net])) index_list;
val names = pathb |> hd |> snd |> map fst
val (categories,results) = pathb @ netb |> map (fn (x,y) => (x,map snd y)) |> ListPair.unzip
\<close>
ML \<open>
compare categories names results
\<close>
(*
ML \<open>
val pathb = (writeln "Path"; PathTest.benchmark NONE NONE);
val netb = (writeln "Net"; NetTest.benchmark NONE NONE);

val res = map_index (fn (i,(name,reps,_,x)) => (name,reps,diff x (nth netb i |> (fn (_,_,_,x) => x)))) pathb;
\<close>*)

(* Deletion does not work for Path Indexing! Can't reproduce test input since different namegen *)

ML \<open>PathTest.print_distribution ()\<close>