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

ML \<open>
val f = @{term "\<lambda>x. x"}
val a = @{term "a (b c)"}
val b = @{term "b"}
val x = Var (("x",0), TFree ("'a", []))
val y = Var (("y",0), TFree ("'a", []))
;N.empty
|> N.insert (op =) (a,true)
|> N.insert (op =) (b,true)
|> N.content
\<close>

declare [[spec_check_max_success = 1000]]
ML_command \<open>
(* Intersection on Lists *)
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
  [(1000,10),(1000,30),(1000,50),(1000,100),(100,200),(100,500),(10,1000),(10,5000)]
  (*
  |> map (fn (x,y) => (x div 100, y))
  *) (* For testing runtime before wasting an hour *)
  |> gen_seeds (Random.deterministic_seed 1)

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

fun bench tag_index (net_gen : int -> term Generator.gen -> 'a Generator.gen) benchmark gens sizes =
  cross gens sizes
  |> maps (fn ((tag_gen,term_gen),(size,seeds)) =>
      map (fn r => (net_gen size (term_gen size) r |> fst, term_gen size)) seeds
       |> benchmark
       |> map (fn (tag_test, res) => ([
              tag_test,
              tag_index,
              tag_gen,
              Size ("S " ^ @{make_string} size ^ "-R " ^ @{make_string} (length seeds))
            ], res)))
\<close>

ML \<open>
val dn_bench = bench (Index "DN") NBench.index_gen (fn ns => NBench.benchmark_basic ns @ NBench.benchmark_queries ns)
val pi_bench = bench (Index "PI_") PBench.index_gen (fn ns => PBench.benchmark_basic ns @ PBench.benchmark_queries ns)
val pitt_bench = bench (Index "PITT") PTTBench.index_gen (fn ns => PTTBench.benchmark_basic ns @ PTTBench.benchmark_queries ns)
val tt_bench = bench (Index "TT_") TTBench.index_gen (fn ns => TTBench.benchmark_basic ns @ TTBench.benchmark_variants ns)

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
val () = writeln (@{make_string} timing)
fun compare name x_label y_label selection =
  table benchmarks (print_values selection) name x_label y_label
;
\<close>

ML_command \<open>
(* Table 1: Queries over Vars *)
;compare "Variants over Vars" (Index "") (Gen "V") [Test "variants", Size ""]
;compare "Instances over Vars" (Index "") (Gen "V") [Test "instance", Size ""]
;compare "Generalisations over Vars" (Index "") (Gen "V") [Test "generalisations", Size ""]
;compare "Unifiables over Vars" (Index "") (Gen "V") [Test "unifiables", Size ""]
\<close>

ML_command \<open>
(* Table 2: Queries over Reuse *)
;compare "Variants over Reuse" (Index "") (Gen "R") [Test "variants", Size ""]
;compare "Instances over Reuse" (Index "") (Gen "R") [Test "instance", Size ""]
;compare "Generalisations over Reuse" (Index "") (Gen "R") [Test "generalisations", Size ""]
;compare "Unifiables over Reuse" (Index "") (Gen "R") [Test "unifiables", Size ""]
\<close>

ML_command \<open>
(* Table 3: Queries and Gen MV over Size *)
;compare "Queries over Size" (Size "") (Index "") [Test "Q:", Gen "MV"]
(* Table 4: Insert *)
;compare "Insert over Size" (Size "") (Index "") [Test "Insert", Gen "MV"]
(* Table 5: Delete *)
;compare "Delete over Size" (Size "") (Index "") [Test "Delete", Gen "MV"]
(* Table 6: Content *)
;compare "Content over Size" (Size "") (Index "") [Test "Content", Gen "MV"]
\<close>

ML_command \<open>
(* Table 7: Queries: Contained, generalised vs noncontained *)
;compare "Variants: Contained, generalised vs noncontained" (Test "variants") (Index "") [Gen "MV", Size ""]
;compare "instances: Contained, generalised vs noncontained" (Test "instances") (Index "") [Gen "MV", Size ""]
;compare "general: Contained, generalised vs noncontained" (Test "generalisations") (Index "") [Gen "MV", Size ""]
;compare "unifiab: Contained, generalised vs noncontained" (Test "unifiables") (Index "") [Gen "MV", Size ""]
\<close>

ML_command \<open>
;compare "All Indices sum of all sizes" (Index "") (Test "") [Gen "LV", Size ""]
;compare "Path Indexing" (Gen "V") (Test "Q:") [Index "PI_", Size ""]
;compare "Discrimination Net" (Gen "") (Test "") [Index "DN", Size ""]
;compare "Termtable" (Gen "") (Test "") [Index "TT_", Size ""]
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

end
