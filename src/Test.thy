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
(*
ML \<open>ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ)\<close>
*)
ML \<open>
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
val size = 5000;

profile_time (fn () => Random.new () |> term_with_var 0.2 5 (4,6)) ()
\<close>

ML \<open>
val term_gens_reuse = [
(* Reuse of symbols *)
("LR", term_ground 0.0 5 (2,6)),
("MR", term_ground 0.3 5 (2,6)),
("HR", term_ground 0.5 5 (2,6))
]
val term_gens_var = [
("LV", term_with_var 0.1 5 (2,6)),
("MV", term_with_var 0.2 5 (2,6)),
("HV", term_with_var 0.5 5 (2,6))
]
val index_list =
  term_gens_var
  |> map (fn (name,gen) => (name,funpow_yield size gen (Random.new ()) |> fst))
  |> map (fn (name,terms) =>
  (name,
   fold (fn t => P.insert_safe eq (t,t)) terms P.empty,
   fold (fn t => N.insert_safe eq (t,t)) terms N.empty))
\<close>
ML \<open>
ML_Heap.share_common_data ();
ML_Heap.gc_now ();
\<close>
(*
ML \<open>
map (fn (name,p,n) =>
      let val path = ML_Heap.obj_size p
          val net = ML_Heap.obj_size n
      in (name,
          "PI: " ^ (Real.fromInt path / 1000000.0 |> @{make_string}) ^ "MB", 
          "DN: " ^ (Real.fromInt net / 1000000.0 |> @{make_string}) ^ "MB",
          Real.fromInt path / Real.fromInt net) |> @{make_string} |> writeln end) index_list;
\<close>
*)
ML \<open>
val pathb = map (fn (name,path,_) => ("PI-" ^ name, PathBench.benchmark_queries [path])) index_list;
val netb = map (fn (name,_,net) => ("DN-" ^ name, NetBench.benchmark_queries [net])) index_list;
val names = pathb |> hd |> snd |> map fst
val (categories,results) = pathb @ netb |> map (fn (x,y) => (x,map snd y)) |> ListPair.unzip

\<close>
ML \<open>
compare categories names results
(* TODO Lookup can sometimes be really, really slow in PI, perhaps GC? *)
\<close>
(*

val index_list = map (fn (name,terms) =>
  (name,
   Timing.timing (fn () => fold (fn t => P.insert_safe eq (t,t)) terms P.empty) () |> fst |> @{make_string} |> writeln,
   Timing.timing (fn () => fold (fn t => N.insert_safe eq (t,t)) terms N.empty) () |> fst |> @{make_string} |> writeln)) termss
ML \<open>PathTest.print_distribution ()\<close>
*)
