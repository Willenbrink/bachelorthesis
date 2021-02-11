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
val x = @{term "f a"}
val y = @{term "f b"}
;
P.empty
|> P.insert (op =) (x,3)
|> P.insert (op =) (y,3)
\<close>
ML \<open>

writeln "Path";
PathTest.test ();


writeln "Net";
NetTest.test ();
\<close>

ML \<open>
val size = 300;
\<close>

ML \<open>
val term_gens_reuse = [
(* Reuse of symbols *)
("LR", term_var_reuse 0.0 5 (2,6)),
("MR", term_var_reuse 0.3 5 (2,6)),
("HR", term_var_reuse 0.5 5 (2,6))
]
val term_gens_var = [
("VLV", term_with_var 0.01 5 (2,6)),
("LV", term_with_var 0.1 5 (2,6)),
("MV", term_with_var 0.2 5 (2,6)),
("HV", term_with_var 0.5 5 (2,6)),
("TV", term_terminal_var 5 (2,6))
]
val index_list =
  term_gens_reuse
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
\<close>
(*
profile_time
        37 Net().add_key_of_terms(2)aux(2)
        45 Net().query(3)handle_func(1)

 DN-TV	 DN-HV	 DN-MV	 DN-LV	DN-VLV	 PI-TV	 PI-HV	 PI-MV	 PI-LV	PI-VLV	 
 0.369	 0.113	 0.277	 0.407	 0.563	 0.664	 0.191	 0.418	 0.623	 1.108	Lookup existing term 
 0.538	 7.414	 9.923	 8.129	 2.211	 0.460	 0.143	 0.353	 0.568	 0.915	instances existing term 
 1.134	 0.257	 0.599	 0.894	 1.307	 0.800	 0.264	 0.564	 0.812	 1.337	generalisations existing term 
 1.233	 8.208	10.889	 8.962	 2.973	 0.535	 0.188	 0.434	 0.717	 1.197	unifiables existing term

 DN-HR	 DN-MR	 DN-LR	 PI-HR	 PI-MR	 PI-LR	 
 0.686	 0.466	 0.389	 0.629	 0.656	 0.704	Lookup existing term 
11.101	 9.577	 9.746	 0.566	 0.601	 0.551	instances existing term 
 0.953	 1.079	 0.929	 0.854	 0.887	 0.936	generalisations existing term 
10.324	10.619	12.406	 0.728	 0.760	 0.717	unifiables existing term 

val index_list = map (fn (name,terms) =>
  (name,
   Timing.timing (fn () => fold (fn t => P.insert_safe eq (t,t)) terms P.empty) () |> fst |> @{make_string} |> writeln,
   Timing.timing (fn () => fold (fn t => N.insert_safe eq (t,t)) terms N.empty) () |> fst |> @{make_string} |> writeln)) termss
ML \<open>PathTest.print_distribution ()\<close>
*)
