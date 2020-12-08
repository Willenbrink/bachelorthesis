functor Tester (Net : NET) = 
struct
val eq = Term.aconv_untyped
fun set_eq fst snd = eq_set eq (fst,snd)
fun termgen n r =
  let val (num,r) = Random.range (0,n) r (* TODO find better solution for spread *)
  in Generator.term_fol (0.0, 0.3, 0.3) 5 num r end
fun netgen term_size num_term r =
  let fun aux term_size num_term r = case num_term of
            0 => (Net.empty,r)
          | _ => let
            val (term,r) = termgen term_size r
            val (base,r) = aux term_size (num_term - 1) r
          in (Net.insert_term_safe eq (term,term) base,r) end
      val (num_term,r) = Random.range (0,num_term) r (* TODO find better solution for spread *)
  in aux term_size num_term r end

fun check_pred gen name pred = Spec_Check.checkGen @{context} (gen, NONE) (name, pred)
fun check gen name prop = check_pred gen name (Property.pred prop)

fun ins t n = Net.insert_term_safe eq (t,t) n

val () = (
check (Generator.unit) "Empty net is empty" (fn _ => Net.content Net.empty = []);
check (Generator.zip (termgen 10, netgen 10 30)) "Insertion adds value to content"
      (fn (t,n) => set_eq (t :: Net.content n) (ins t n |> Net.content));
check (netgen 10 30) "content = entries" (fn n => set_eq (Net.entries n) (Net.content n));
let fun net_size n = Net.content n |> List.length in
check_pred (Generator.zip (termgen 10, netgen 10 30)) "Deletion removes term"
      (Property.==> (fn (t,n) => member eq (Net.content n) t,
                     fn (t,n) => ((Net.delete_term eq (t,t) n) |> net_size) = (net_size n - 1)))
end;
())

fun print_spread () = (
check (termgen 20) "Termsize spread"
      (fn t => (writeln (@{make_string} (Term.size_of_term t)); true));
check (netgen 10 30) "Netsize spread"
      (fn n => (writeln (@{make_string} (Net.content n |> List.length)); true)))

end;