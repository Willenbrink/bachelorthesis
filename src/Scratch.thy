theory "Scratch"
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
ML "open Pprinter"
setup "term_pat_setup"
setup "type_pat_setup"

ML \<open>
open Property
val ==> = Property.==>
infix ==>
open Spec_Check
structure G = Generator
\<close>
ML_command \<open>
;check
  (Show.list (Show.int))
  (G.list (G.nonneg 5) (G.pos 10))
  "Test Name"
  (prop (fn xs => (xs = hd xs :: tl xs)))
  @{context}
  (Random.new ())

;check (Show.list (Show.char)) (G.list (G.nonneg 5) (G.char)) "Test Name"
  ((not o null) ==> (fn xs => (xs = hd xs :: tl xs))) @{context} (Random.new ())

\<close>






























