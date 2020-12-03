functor Tester (Net : NET) = 
struct
val eq = Term.aconv_untyped
fun netgen _ 0 = Generator.lift Net.empty
  | netgen term_size num_term : term Net.net Generator.gen =
  let
    val t = Generator.term term_size
    val base = netgen term_size (num_term - 1)
  in
  Generator.map2 (fn (t,base) => Net.insert_term_safe eq (t,t) base) (t,base)
  end

fun check name f = Spec_Check.checkGen @{context}
 (netgen 20 20, NONE)
 (name, Property.pred f)

fun checks msg prop = (writeln msg; check_property prop)

fun checkb msg bool = (writeln msg; if not bool then raise Fail "" else writeln "Check OK")

fun test () = (
check "Empty net is empty" (fn _ => Net.content Net.empty = []);
checks "Insertion adds value to content:"
"ALL term. Library.eq_set Term.aconv_untyped\
\ ([term], Net.insert_term Term.aconv_untyped (term,term) Net.empty |> Net.content)";
check "content = entries" (fn net => Library.eq_set eq (Net.entries net, Net.content net));
check "Match (f x)"
  (fn net => let val t = @{term "f x"} in
             if member eq (Net.content net) t
             then member eq (Net.match_term net t) t else true end);
())
end;