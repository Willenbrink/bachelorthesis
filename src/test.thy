theory "test"
  imports Main "../spec_check/src/Spec_Check"
begin
ML_file "net_interface.ML"
ML_file "net.ML"
ML_file "path.ML"
ML_file "pprinter.ML"
ML_file "tester.ML"
ML "open Pprinter"
setup "term_pat_setup"
setup "type_pat_setup"
(*ML \<open>ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_ppatyp)\<close>*)
ML_val \<open>@{term_pat "f x y"}\<close>
ML_val \<open>@{typ_pat "'a \<Rightarrow> 'b \<Rightarrow> 'c"}\<close>

ML \<open>
val eq = Term.aconv_untyped
fun ins t tree = Path.insert_term eq (t,t) tree
fun del t tree = Path.delete_term eq (t,t) tree
val terms =
@{term "f"} ::
@{term "f x"} ::
@{term "f x y"} ::
@{term "f (g x)"} ::
@{term "f (g x) y"} ::
@{term "f (h x)"} ::
@{term "f (g x y z)"} ::
@{term "f (g y y z)"} ::
@{term "f (g (h a) y z)"} ::
[]

val pathl as Path.Node (con,rest) = fold ins terms Path.empty
fun match unif tree term = Path.match unif tree term |> map (pterm o op !)
\<close>

ML_val \<open>
fun f1 height index state =
  let val num_args = if index = 5 andalso height < 5 orelse height = 0 then 5 else 0
      val options = [(1,Gen_Term.const num_args), (3,Gen_Term.free num_args), (1,Gen_Term.var num_args)]
      val (sym,state) = Gen_Base.chooseL' options state
  in (sym, num_args, state) end
val t1 = Generator.term_det f1 (Random.new ());
t1 |> pterm;
\<close>

ML_val \<open>
fun f1 path state =
  let val height = length path
      val (prev_sym, index) = if height >= 1 then nth path 0 |>> SOME ||> SOME else (NONE,NONE)
      val num_args = if height = 0 orelse index = SOME 5 andalso height < 5 then 5 else 0
      val (sym,state) = Gen_Term.free num_args state
  in (sym, num_args, state) end
val t1 = Generator.term_det_path f1 (Random.new ());
t1 |> pterm;
\<close>

ML_val \<open>
@{term_pat "f (g x y) (h a b)"} |> ignore;
val x = Generator.term_det (fn height => fn index => fn state =>
  let val num_args = if height < 2 then 2 else 0
(*val sym = Free (Char.chr (Char.ord #"0" + state) |> Char.toString, TVar (("a",1),[]))*)
      val (sym,state) = Generator.free num_args state in
   (sym,num_args,state)
   end) (Random.new ());
x |> pterm
\<close>
ML_val \<open>
val r = Random.new ()
fun f r = Generator.term_fol_structure 3 10 r
|-> Generator.term_fol_map (0.0, 0.0, 0.0)
|> fst;
val x = f r |> pterm;
val y = f r;
\<close>

ML_val \<open>@{term_pat "ALL x. f x y"}\<close>

ML "fun ins t n = Net.insert_term eq (t,t) n"
ML \<open>val net = Net.empty
 |> ins @{term "f x"}
 |> ins @{term "f (x y)"}
 |> ins @{term "f x y"}
 |> ins @{term "f (g x y)"}
 |> ins @{term "f (g x y z)"}
 |> ins @{term "f (g y y z)"}
 |> ins @{term "f (g (h a) y z)"}
 |> ins @{term "f"}
\<close>

ML \<open>
structure NetTest = Tester(Net);
structure PathTest = Tester(Path);
\<close>

ML \<open>
val x = Unsynchronized.ref (Generator.term_fol)
val y = Unsynchronized.ref (!x)
val z = x
val a = (x = y)
val b = (z = x)
val c = Unsynchronized.ref 0
val d = Unsynchronized.ref (!c)
val e = (c = d)
\<close>

ML_command \<open>
val pathb = (writeln "Path"; PathTest.benchmark ());
val netb = (writeln "Net"; NetTest.benchmark ());
fun diff {elapsed = _, cpu = c1, gc = _} {elapsed = _, cpu = c2, gc = _} =
  (c1 - c2, (Time.toReal c1) / (Time.toReal c2))
val res = map_index (fn (i,(name,_,x)) => (name,diff x (nth netb i |> (fn (_,_,x) => x)))) pathb;
writeln ("\nAbsolute\tRelative\tName");
map (fn (name,(abs,rel)) => (@{make_string} abs ^ "\t\t" ^ @{make_string} rel ^ "\t" ^ name) |> writeln) res
\<close>

ML \<open>
writeln "Path";
PathTest.test ();
writeln "Net";
NetTest.test ();
\<close>
(* Deletion does not work for Path Indexing! Can't reproduce test input since different namegen *)

ML \<open>PathTest.print_distribution ()\<close>