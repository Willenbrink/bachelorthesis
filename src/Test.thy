theory "Test"
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

(* Testing and Benchmarking *)

ML \<open>
structure V = struct type value = term val eq = Term.aconv_untyped end
structure NetTest = Tester(Net(V));
structure PathTest = Tester(Path(V));
\<close>

ML_command \<open>
fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6
fun diff {elapsed = _, cpu = c1, gc = _} {elapsed = _, cpu = c2, gc = _} =
  (Time.toReal c1 - Time.toReal c2, (Time.toReal c1) / (Time.toReal c2))

val pathb = (writeln "Path"; PathTest.benchmark ());
val netb = (writeln "Net"; NetTest.benchmark ());
val res = map_index (fn (i,(name,reps,_,x)) => (name,reps,diff x (nth netb i |> (fn (_,_,_,x) => x)))) pathb;
writeln ("Path indexing (PI) vs discrimination net (DN)\nAbs. (PI - DN)\tRel. (PI/DN)\tRepetitions\tName");
map (fn (name,reps,(abs,rel)) => (print_real abs ^ "s\t\t"
                                  ^ print_real rel ^ "\t\t"
                                  ^ @{make_string} reps ^ "\t\t"
                                  ^ name)
                                  |> writeln) res
\<close>

ML \<open>
writeln "Path";
PathTest.test ();

writeln "Net";
NetTest.test ();
\<close>
(* Deletion does not work for Path Indexing! Can't reproduce test input since different namegen *)

ML \<open>PathTest.print_distribution ()\<close>