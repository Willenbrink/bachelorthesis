functor Tester (Net : NET) = 
struct
val empty = Net.empty
val _ = (writeln "Insertion adds value to content:";
 check_property "ALL term. Library.eq_set Term.aconv_untyped (term :: Net.content Net.empty, Net.insert_term Term.aconv_untyped (term,term) Net.empty |> Net.content)")


val _ = (writeln "Trivially true test:"; check_property "ALL xs. xs = xs")
val _ = (writeln "Trivially wrong test:"; check_property "ALL xs. not (xs = xs)")
end;