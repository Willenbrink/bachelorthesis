theory "Test"
imports
  Pure
  Spec_Check2.Spec_Check
begin
ML_file "util.ML"
ML_file "benchmark_util.ML"
ML_file "term_index.ML"
ML_file "net.ML"
ML_file "path.ML"
ML_file "path_termtab.ML"
ML_file "termtab.ML"
ML_file "pprinter.ML"
ML_file "term_gen.ML"
ML_file "net_gen.ML"
ML_file "tester.ML"
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
ML \<open>
val n =
  fold (fn t => P.insert eq (t,t))
    [Free ("f3_0", Type ("dummy", [])) $ (Var (("v2_0", 0), Type ("dummy", [])))]
    P.empty
;

val sgen = G.list (G.range_int (2,10)) (G.pos 5)
val ssgen = G.list (G.lift 20) sgen
val ss =
ssgen (Random.deterministic_seed 1)
 |> fst
 |> map (Ord_List.make int_ord)
 |> (fn xs => G.shuffle xs (Random.new ()))
 |> fst;
\<close>
declare [[spec_check_num_tests = 1000]]
ML \<open>
val inter' = Spec_Check.check_base (fn r => ssgen r |-> G.shuffle) "" (Property.prop (fn xs => (inters' (int_ord) xs; true)) )
 @{context} (Random.new ())
\<close>

ML_command \<open>
val tests = [
  ("Path", PathTest.test),
  ("PathTT", PathTTTest.test),
  ("Net", NetTest.test),
  ("TT", TTTest.test)
];

fold (fn (name,test) => fn r => (writeln name; test @{context} r)) tests (Random.new ())
\<close>

ML \<open>
(*
val sizes = [(50,50),(50,100),(50,200),(50,500),(50,1000),(5,5000)]
*)
val sizes = [(3,50),(3,100),(3,200),(3,500),(3,1000)]

val seed = Random.new ()
val sizes =
  fold (fn (repeats,n) => fn (r,acc) =>
    let val (rs,r) = funpow_yield repeats Random.split r
    in (r, (n,rs) :: acc) end
  ) sizes (seed,[])
  |> snd
\<close>

ML \<open>
val depth = 6
val argr = (0,4)

fun test_single size = [
("TestName", term_with_var size 10 depth argr)
]

val gen_distinct =
  let fun gen reuse size = term_var_reuse (Real.floor (Real.fromInt size * reuse)) depth argr
  in
    [("NR", gen 10.0), ("LR", gen 1.0), ("MR", gen 0.1) , ("HR",gen 0.02)]
    |> map (apfst Gen)
  end

val gen_var =
  let fun gen var size = term_with_var size var depth argr
  in
    [("NV", gen 0), ("LV", gen 3), ("MV", gen 10), ("HV", gen 30)]
    |> map (apfst Gen)
  end

val gens = gen_distinct @ gen_var
\<close>

ML \<open>
ML_Heap.share_common_data ();
ML_Heap.gc_now ();
\<close>
ML \<open>
fun cross xs ys =
  maps (fn x => map (fn y => (x,y)) ys) xs

fun bench gens tag_index (net_gen : int -> term Generator.gen -> 'a Generator.gen) benchmark =
  cross gens sizes
  |> maps (fn ((tag_gen,term_gen),(size,seeds)) =>
      map (fst o net_gen size (term_gen size)) seeds
       |> benchmark
       |> map (fn (tag_test, res) => ([
              tag_test,
              tag_index,
              tag_gen,
              Size ("Size: " ^ @{make_string} size ^ " Runs: " ^ @{make_string} (length seeds))
            ], res)));
local
val r = Random.new ()
val p = PBench.index_gen 1000 ((hd gens |> snd) 10) r |> fst
val ptt = PTTBench.index_gen 1000 ((hd gens |> snd) 10) r |> fst
val x = (hd gens |> snd) 10 r |> fst
val g = (List.tabulate (10000, K x) |> map Generator.lift)
in
val _ = print_size "Path" p
val _ = print_size "PathTT" ptt
val a = PBench.timer "" (P.unifiables p) g;
val b = PTTBench.timer "" (PTT.unifiables ptt) g;
end
\<close>

ML\<open>
G.basic_name "c" (G.lift 0) (Random.deterministic_seed 1);
\<close>

ML\<open>
val dn_bench = bench gens (Index "DN") NBench.index_gen (fn ns => NBench.benchmark_basic ns @ NBench.benchmark_queries ns)
val pi_bench = bench gens (Index "PI_") PBench.index_gen (fn ns => PBench.benchmark_basic ns @ PBench.benchmark_queries ns)
val pitt_bench = bench gens (Index "PITT") PTTBench.index_gen (fn ns => PTTBench.benchmark_basic ns @ PTTBench.benchmark_queries ns)
val tt_bench = bench gens (Index "TT_") TTBench.index_gen (fn ns => TTBench.benchmark_basic ns @ TTBench.benchmark_lookup ns)

val benchmarks = [
pi_bench,
pitt_bench,
dn_bench,
tt_bench,
[]] |> flat
\<close>

ML \<open>
fun print_values filter_tags values =
  let
(*
    val filter_tags =
      if eq_tag (Size "", filter_tags)
      then filter_tags
      else (Size "") :: filter_tags
*)
    val values' =
      values
      |> filter (fn (t,_) => forall (fn filter_tag => eq_tag (filter_tag,t)) filter_tags)
    val () =
      values'
      |> map fst
      |> map (fn val_tags => filter_out (fn vt => exists (fn ft => tag_sub ft vt) filter_tags) val_tags)
      |> distinct (op =)
      |> (fn x => if length x > 1 then raise Fail ("Multiple values: " ^ @{make_string} x ^ "\n remaining of: " ^ @{make_string} values) else ())
  in
    values'
    |> map snd
    |> (fn [] => NONE | list => fold (curry op Time.+) list (Time.zeroTime) |> SOME)
    |> apply_def (@{make_string}) "N/A"
  end
val x = benchmarks
      |> filter (fn (t,_) => forall (fn filter_tag => eq_tag (filter_tag,t)) [Index "PI", Test "unif", Gen "", Size "1000"])
fun compare name x_label y_label selection =
  table benchmarks (print_values selection) name x_label y_label
\<close>
ML \<open>
;compare "Test" (Index "") (Size "") [Test "unif", Gen "LV"]
;compare "All Indices Size 100" (Index "") (Test "") [Gen "LV", Size "100 "]
;compare "All Indices Size 1000" (Index "") (Test "") [Gen "LV", Size "1000"]
;compare "All Indices sum of all sizes" (Index "") (Test "") [Gen "LV", Size ""]
;compare "Path Indexing" (Gen "V") (Test "Q:") [Index "PI_", Size ""]
;compare "Discrimination Net" (Gen "") (Test "") [Index "DN", Size ""]
;compare "Termtable" (Gen "") (Test "") [Index "TT_", Size ""]
;compare "Unifiables over Reuse" (Gen "R") (Index "") [Test "unif", Size ""]
;compare "Unifiables over Variables" (Gen "V") (Index "") [Test "unif", Size ""]
;compare "Lookup over Vars" (Gen "V") (Index "") [Test "lookup", Size ""]
;compare "Instances over Vars" (Gen "V") (Index "") [Test "instance", Size ""]
;compare "Generalisations over Vars" (Gen "V") (Index "") [Test "general", Size ""]
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
