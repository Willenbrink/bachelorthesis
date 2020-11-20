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

ML_val \<open>@{term_pat "(\<lambda>x. x 1) f"}\<close>
ML_val \<open>@{term_pat "(f x) y"}\<close>

ML "val eq = Term.aconv_untyped"
ML "fun dup t = (t,t)"
ML "fun ins t tree = Path.insert_term eq (t,t) tree"
ML_val \<open>Net.insert_term eq (@{term "f x"},@{term "f x"}) Net.empty\<close>
ML \<open>val ex = Path.empty
 |> ins @{term "f x"}
 |> ins @{term "f (g x)"}
 |> ins @{term "f x y"}
 |> ins @{term "f (g x y)"}
 |> ins @{term "f (g x y z)"}
 |> ins @{term "f (g y y z)"}
 |> ins @{term "f (g (h a) y z)"}
 |> ins @{term "f"}
\<close>

ML_val \<open>ins @{term "f"} ex handle Path.INSERT => Path.empty\<close> (* Duplicate *)
ML \<open>val ex2 =
     ex
  |> Path.delete_term eq (dup @{term "f x"})
\<close>
(* TODO == for trees?
*)
ML_val \<open>ins @{term "f x"} ex2\<close>

ML \<open>val ks = Path.key_of_term @{term "f (g x y)"}\<close>
ML \<open>val (Path.Node (con,tree)) = ex\<close>
ML \<open>val test = Path.SItab.lookup tree ("f",0)\<close>
ML_val \<open>Path.SItab.dest tree\<close>
ML_val \<open>Path.lookup ex ks\<close>
ML_val \<open>Path.lookup_one ex (ks |> rev |> hd)\<close>

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











