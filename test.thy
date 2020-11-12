theory "test"
  imports Main
begin

ML_file "path.ML"
ML_file "pprinter.ML"
setup "term_pat_setup"
setup "type_pat_setup"
ML_val \<open>@{term_pat "Suc (?x::nat)"}\<close>
ML_val \<open>@{typ_pat "int \<Rightarrow> int"}\<close>

ML_val \<open>@{term_pat "(\<lambda>x. x 1) f"}\<close>

ML_val "Path.empty"
ML "fun taut (x,y) = true"
ML_val \<open>Net.insert_term taut (@{term "f x"},true) Net.empty\<close>
ML_val \<open>Path.insert_term taut (@{term "f x"},true) Path.empty\<close>

ML_val "head_of"
