theory "test"
  imports Main
begin

ML_file "/opt/Isabelle2020/src/Pure/net.ML"
ML_file "path.ML"
ML_file "pprinter.ML"
setup "term_pat_setup"
setup "type_pat_setup"
ML_val \<open>@{term_pat "Suc (?x::nat)"}\<close>
ML_val \<open>@{typ_pat "int \<Rightarrow> int"}\<close>

ML \<open>
exception TEST
val eq = Term.aconv_untyped
(* Non-standard foldl for better waterfall/pipelining
   E.g. replacing "a |> f b1 |> f b2" with "foldl f a b" or "b |> foldl f a" *)
fun foldl f acc args = Library.foldl (fn (a,b) => f b a) (acc,args)
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

val (pathl as Path.Node (con,rest)) = foldl ins Path.empty terms
fun pterm term = Syntax.pretty_term @{context} term
fun match unif tree term = Path.match unif tree term |> map pterm
\<close>

ML_val \<open> (* Duplicate *)
let val _ = ins @{term "f"} pathl in raise TEST end handle Path.INSERT => "Success"\<close>
(* TODO equality type for net? table is insert-order dependent *)
ML_val \<open>pathl |> del @{term "f x"} |> ins @{term "f x "}\<close>

ML \<open>val ks = Path.key_of_term @{term "f (g x y)"}\<close>

ML \<open>val t = @{term_pat "?f ?g y"}\<close>
ML \<open>val (tree as Path.Node (con,tree')) = Path.empty |> ins t\<close>
ML_val \<open>
match true tree @{term "f x"};
match false pathl @{term "f (g x)"};
match true pathl t;
Path.empty |> ins @{term "(a b) (c d)"};
@{term "(a b) (c d)"} |> pterm

\<close>

ML_val "head_of"


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

ML \<open>val Net.Net{atoms,comb,var} = net\<close>
ML_val \<open>let val Net.Net{atoms,...} = net in Net.look1 (atoms,"f") [] end\<close>
ML_val \<open>Net.rands false @{term "f"} (net,[])\<close>











