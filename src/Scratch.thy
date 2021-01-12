theory "Scratch"
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
ML \<open>ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ)\<close>

ML_val \<open>
@{term_pat "f x y"};
@{typ_pat "'a \<Rightarrow> 'a"};
TFree ("'a",["'a", "'b"]);
@{term "(\<lambda> x. x)"};
\<close>


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

val pathl = fold (fn t => fn net => Path.insert_term eq (t,t) net) terms Path.empty
fun match unif (values,tree) term = Path.match unif values tree term |> map (pterm o op !)
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
|-> Generator.term_fol_map (Generator.def_sym_gen (1.0,1.0,1.0,1.0))
|> fst;
val x = f r |> pterm;
val y = f r;
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
Net.empty
|> Net.insert (op =) (Net.key_of_term @{term "f x"}, 1)
|> Net.insert (op =) (Net.key_of_term @{term "f x"}, 2)
|> Net.insert (op =) (Net.key_of_term @{term "g y"}, 1)
|> Net.delete (op =) (Net.key_of_term @{term "f x"}, 1)
|> Net.content
\<close>

ML \<open>
fun ins' (k,v) n = Net.insert_term_safe eq (k,v) n
fun ins t n = Net.insert_term eq (t,t) n
val x = Const ("x",TFree ("'a",[]))
val y = Free ("a", TVar (("'a", 0), []))
val z = Var (("b", 3), TVar (("'a", 0), []))
val net = Net.empty |> ins y |> ins z
val net_con = Net.content net
val net' = net |> ins' (x,z) |> Net.delete_term eq (x,z) |> Net.content
(*Net {atoms = {("a", Leaf [Free ("a", TVar (("'a", 0), []))])}, comb = Leaf [], var =
      Leaf [Var (("b", 3), TVar (("'a", 0), []))]})*)
\<close>
