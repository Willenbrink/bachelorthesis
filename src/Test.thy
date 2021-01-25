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
structure V = struct type value = term val eq = Term.aconv_untyped end
structure NetTest = Tester(Net(V));
structure PathTest = Tester(Path(V));
structure NetBench = Benchmark(Net(V));
structure PathBench = Benchmark(Path(V));
\<close>
(*
ML \<open>
writeln "Path";
PathTest.test ();

writeln "Net";
NetTest.test ();
\<close>
*)
ML \<open>
val size = 50
\<close>

ML \<open>
Timing.timing (fn () => Random.new () |> (term_ground 0.0 5 (0,10))) () |> fst;
Timing.timing (fn () => Random.new () |> PathBench.net_gen size (term_ground 0.0 5 (0,8))) () |> fst;
\<close>

ML \<open>
val path_gen = PathBench.net_gen size (term_ground 0.0 5 (0,6))
val net_gen = NetBench.net_gen size (term_ground 0.0 5 (0,6))
val paths = List.tabulate (2, fn i => Random.new () |> funpow i Random.next |> path_gen |> fst) handle exn => (@{make_string} exn; Exn.reraise exn)
val nets = List.tabulate (2, fn i => Random.new () |> funpow i Random.next |> net_gen |> fst) handle exn => (@{make_string} exn; Exn.reraise exn)
\<close> 
ML \<open>
val pathb = PathBench.benchmark_queries paths;
val netb = NetBench.benchmark_queries nets;
\<close>
ML \<open>
compare ["PI", "DN"] (ListPair.zip (pathb,netb))
\<close>
(*
ML \<open>
val pathb = (writeln "Path"; PathTest.benchmark NONE NONE);
val netb = (writeln "Net"; NetTest.benchmark NONE NONE);

val res = map_index (fn (i,(name,reps,_,x)) => (name,reps,diff x (nth netb i |> (fn (_,_,_,x) => x)))) pathb;
\<close>*)

(* Deletion does not work for Path Indexing! Can't reproduce test input since different namegen *)

ML \<open>PathTest.print_distribution ()\<close>