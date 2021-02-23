theory "Test"
  imports Main "../spec_check/src/Spec_Check"
begin
ML_file "benchmark_util.ML"
ML_file "term_index.ML"
ML_file "net.ML"
ML_file "path.ML"
ML_file "path_termtab.ML"
ML_file "termtab.ML"
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
structure N = Net
structure P = Path
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
ML \<open>
val x = @{term "f a"}
val y = @{term "f b"}
;
TT.empty
|> TT.insert (op aconv) (x,x)
|> TT.delete (curry (op aconv) x) (x)
|> TT.content
\<close>
ML \<open>
val tests = [
(*
("Path", PathTest.test),
("PathTT", PathTTTest.test),
("Net", NetTest.test),
("TT", TTTest.test)
*)
];

fold (fn (name,test) => fn _ => (writeln name; test ())) tests ()
\<close>

ML \<open>
val size = 600;
\<close>

ML \<open>

val depth = 6
val argr = (0,4)

val test_single = [
("", term_with_var size 10 depth argr)
]

val test_distinct =
  let fun gen reuse = term_var_reuse (Real.floor (Real.fromInt size * reuse)) depth argr
  in [("LLR", gen 10.0), ("LR", gen 1.0), ("MR", gen 0.1) , ("HR",gen 0.01)] end

val test_var =
  let fun gen var = term_with_var size var depth argr
  in [("NV", gen 0), ("LV", gen 3), ("MV", gen 10), ("HV", gen 30)] end

val group_size = (size + 3 - 1) div 3 (* Integer ceiling *)
val termss =
  test_distinct @ test_var
  |> map (fn (name,gen) => (name,funpow_yield size gen (Random.new ()) |> fst))
\<close>
ML \<open>
val names = map fst termss
fun pi_indices () = map (PBench.create_indices size o snd) termss
fun pitt_indices () = map (PTTBench.create_indices size o snd) termss
fun dn_indices () = map (NBench.create_indices size o snd) termss
fun tt_indices () = map (TTBench.create_indices size o snd) termss
fun tt_indices2 () = map (TTBench.create_indices size o snd) (test_var
  |> map (fn (name,gen) => (name,funpow_yield (size*10) gen (Random.new ()) |> fst)))
\<close>
ML \<open>
ML_Heap.share_common_data ();
ML_Heap.gc_now ();
\<close>
(*
ML \<open>
map (fn (name,p,n,t,i) =>
      let val path = ML_Heap.obj_size p
          val net = ML_Heap.obj_size n
      in (name,
          "PI: " ^ (Real.fromInt path / 1000000.0 |> @{make_string}) ^ "MB", 
          "DN: " ^ (Real.fromInt net / 1000000.0 |> @{make_string}) ^ "MB",
          Real.fromInt path / Real.fromInt net) |> @{make_string} |> writeln end) index_list;
\<close>
*)
ML \<open>
fun run_bench tag benchmarks (name, input) =
  let val benchmarks = map (fn f => f input) benchmarks |> flat
  in map (fn (n,test) => ([Index tag, Input name, n],test)) benchmarks end

\<close>
ML \<open>
val pi_bench = maps (run_bench "PI" [PBench.benchmark_basic, PBench.benchmark_queries]) (ListPair.zip (names, pi_indices ()))
val pitt_bench = maps (run_bench "PT" [PTTBench.benchmark_basic, PTTBench.benchmark_queries]) (ListPair.zip (names, pitt_indices ()))
val dn_bench = maps (run_bench "DN" [NBench.benchmark_basic, NBench.benchmark_queries]) (ListPair.zip (names, dn_indices ()))
val tt_bench = maps (run_bench "TT" [TTBench.benchmark_basic, TTBench.benchmark_lookup]) (ListPair.zip (names, tt_indices ()))
val tt_bench2 = maps (run_bench "TT" [TTBench.benchmark_basic, TTBench.benchmark_lookup]) (ListPair.zip (names, tt_indices2 ()))
val benchmarks = [
(*
val test_names = benchmarks |> hd |> snd |> map fst;
val (tags,results) = benchmarks |> map (fn (x,y) => (x, map snd y)) |> ListPair.unzip;
val tags = map (fn ts => fold (curry op ^) ts "") tags
*)
pi_bench,
pitt_bench,
dn_bench,
tt_bench,
[]] |> flat;
\<close>
ML \<open>
;compare benchmarks "Path Indexing"
  (fn Input xs => String.isSubstring  "V" xs | _ => false)
  (fn Test _ => true | _ => false)
  (fn Index "PI" => true | _ => false)
;compare dn_bench "Discrimination Net" (* TODO dn_bench, error! *)
  (fn Input xs => String.isSubstring  "V" xs | _ => false)
  (fn Test _ => true | _ => false)
  (fn Index xs => String.isSubstring  "DN" xs | _ => false)
;compare tt_bench2 "Termtable"
  (fn Input xs => true | _ => false)
  (fn Test _ => true | _ => false)
  (fn _ => true | _ => false)
;compare benchmarks "Unifiables over Reuse"
  (fn Input xs => String.isSubstring  "R" xs | _ => false)
  (fn Index _ => true | _ => false)
  (fn Test xs => String.isSubstring  "unif" xs | _ => false)
;compare benchmarks "Unifiables over Vars"
  (fn Input xs => String.isSubstring  "V" xs | _ => false)
  (fn Index _ => true | _ => false)
  (fn Test xs => String.isSubstring  "unif" xs | _ => false)
;compare benchmarks "Lookup over Vars"
  (fn Input xs => String.isSubstring  "V" xs | _ => false)
  (fn Index _ => true | _ => false)
  (fn Test xs => String.isSubstring  "lookup" xs | _ => false)
;compare benchmarks "Instances"
  (fn Input xs => String.isSubstring  "V" xs | _ => false)
  (fn Index _ => true | _ => false)
  (fn Test xs => String.isSubstring  "instance" xs | _ => false)
;compare benchmarks "Generalisations"
  (fn Input xs => String.isSubstring  "V" xs | _ => false)
  (fn Index _ => true | _ => false)
  (fn Test xs => String.isSubstring  "general" xs | _ => false)
;compare benchmarks "All Indices"
  (fn Input xs => String.isSubstring  "MV" xs | Index _ => true | _ => false)
  (fn Test _ => true | _ => false)
  (fn _ => true | _ => false)


(* Expectation:
More Reuse \<rightarrow> Better DN, Worse PI
More Vars \<rightarrow> Better PI, Worse DN (for Instance and Unifiables)
Instance \<rightarrow> PI better than DN
Generalisations \<rightarrow> DN better than PI
PITT better than PI in everything except memory consumption
*)
\<close>
(*
   IN-	   TT-	   DN-	   PI-	 
 0.000	 0.000	 0.652	 0.001	Content of net 
 0.677	 0.077	 0.231	 0.581	Insert terms 
 0.785	 0.006	 0.123	 2.530	Delete terms 
 0.533	 0.005	 0.100	 0.164	Lookup existing term 
 0.350	 0.003	 0.105	 0.161	Lookup non-existing term 
 0.000	 1.324	29.402	 0.212	unifiables existing term 

Path Index without Check
        11 Path().map_child(4)map_list(2)
        18 Table().modify(3)modfy(1)
        21 Path().insert(7)ins(2)
total: 80

Path Index with Check
         4 Path().map_child(4)map_list(2)
        12 Table().modify(3)modfy(1)
        14 Path().insert(7)ins(2)
        77 Term.aconv_untyped(2)
total: 124


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
