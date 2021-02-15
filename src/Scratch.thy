theory "Scratch"
imports Main "../spec_check/src/Spec_Check"
begin
ML_file "term_index.ML"
ML_file "net.ML"
ML_file "path.ML"
ML_file "pprinter.ML"
ML_file "tester.ML"
ML "open Pprinter"
setup "term_pat_setup"
setup "type_pat_setup"
(*ML \<open>ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ)\<close>*)

ML_val \<open>
@{term_pat "f x y"};
@{typ_pat "'a \<Rightarrow> 'a"};
TFree ("'a",["'a", "'b"]);
@{term "(\<lambda> x. x)"};
Spec_Check.check_gen @{context} "Name" (Generator.int) NONE (K (Property.Result false)) (Random.new ());
Generator.var 10 10
\<close>

ML \<open>
structure V = struct type value = term val eq = Term.aconv_untyped end
structure Net = Net(V);
structure Path = Path(V);
\<close>

ML \<open>
Generator.fold_seq 20 (curry op ::) (Generator.free' 0.9 0 (Random.new ())) []
|> map pterm;
local
fun term_gen height index (seq,r) =
  let
    val (symbol,seq) = Seq.pull seq |> (fn SOME x => x)
    val (num_args,r) = Random.range_int (2,10) r
    val state' = (seq,r)
  in
  if height >= 5 orelse (index <> 2 andalso height <> 0)
  then (symbol,0,state')
  else (symbol,num_args,state')
  end
val (r1,r2) = Random.new () |> Random.split
in
val term = Generator.term_det term_gen (Generator.def_sym_seq (1.0,0.0,0.0) 0.1 1 r1, r2) |>> pterm
end
\<close>

ML \<open>
val eq = Term.aconv_untyped
fun ins t tree = Path.insert eq (t,t) tree
fun del t tree = Path.delete eq (t,t) tree
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

val pathl = fold (fn t => fn net => Path.insert eq (t,t) net) terms Path.empty
fun match unif (values,tree) term = Path.generalisations tree term |> map (pterm)
\<close>

ML_val \<open>
fun f1 height index state =
  let val num_args = if index = 5 andalso height < 5 orelse height = 0 then 5 else 0
      val options = [(1,Gen_Term.const num_args), (3,Gen_Term.free num_args), (1,Gen_Term.var num_args)]
      val (sym,state) = Gen_Base.chooseL' options state
  in (sym, num_args, state) end
val t1 = Generator.term_det f1 (Random.new ());
t1 |>> pterm;
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
x |>> pterm
\<close>

(*
  val variant_frees: Proof.context -> term list -> (string * 'a) list -> (string * 'a) list
  val variant_fixes: string list -> Proof.context -> string list * Proof.context
*)
ML \<open>
val ctxt = @{context};
val ctxt = Variable.declare_const ("x","nat") ctxt;

let
val ctxt0 = ctxt
val (_, ctxt1) = Variable.add_fixes ["x"] ctxt0
val frees = replicate 2 ("x", @{typ nat})
in
(Variable.variant_frees ctxt0 [] frees,
Variable.variant_frees ctxt1 [] frees)
end
\<close>

ML \<open>
local
val a = Var (("x",0),@{typ "'a"}) (* @{term "?x"} *)
val b = @{term "\<lambda>x. g (f x)"}
val c = @{term "c"}
val net  = Net.empty  |> Net.insert eq (a,a)  |> Net.insert eq (b,b) |> Net.insert eq (c,c)
val path = Path.empty |> Path.insert eq (a,a) |> Path.insert eq (b,b) |> Path.insert eq (c,c)
in
val net = Net.generalisations net a |> map pterm
val path = Path.generalisations path a |> map pterm
end
\<close>





















