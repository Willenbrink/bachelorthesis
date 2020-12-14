functor Tester (Net : NET) = 
struct
val eq = Term.aconv_untyped
fun set_eq fst snd = eq_set eq (fst,snd)
fun termgen n r =
  let val (num,r) = Random.range_int (0,n) r (* TODO find better solution for spread *)
  in Gen_Term.term_fol (0.0, 0.3, 0.3) 5 num r end
fun netgen term_size num_term r =
  let fun aux term_size num_term r = case num_term of
            0 => (Net.empty,r)
          | _ =>
            let val (term,r) = termgen term_size r
                val (base,r) = aux term_size (num_term - 1) r
            in (Net.insert_term_safe eq (term,term) base,r) end
      val (num_term,r) = Random.range_int (0,num_term) r (* TODO find better solution for spread *)
  in aux term_size num_term r end

fun check_pred gen printer name pred = Spec_Check.checkGen @{context} (gen, printer) (name, pred)
fun check gen printer name prop = check_pred gen printer name (Property.pred prop)

fun ins t n = Net.insert_term_safe eq (t,t) n
fun con t n = member eq (Net.content n) t
fun replace_subterm t r =
  let val (f,args) = Term.strip_comb t
      val (index,r) =  Random.range_int (~1,length args - 1) r
      (* Generate two random values, pass r1 to rec-call, ignore returned r and return r2 instead *)
      val (r1,r2) = Random.split r
  in
  if index = ~1
  then (Term.list_comb (Gen_Term.var 1 r1 |> fst, args), r2)
  else (Term.list_comb (f,nth_map index (fn t => replace_subterm t r1 |> fst) args), r2)
  end

val () = (
check (Gen_Datatypes.unit) NONE
      "Empty net is empty"
      (fn _ => Net.content Net.empty = []);
check (Gen_Base.zip (termgen 10, netgen 10 30)) NONE
      "Insertion adds value to content"
      (fn (t,n) => set_eq (t :: Net.content n) (ins t n |> Net.content));
check (netgen 10 30) NONE
      "content = entries"
      (fn n => set_eq (Net.entries n) (Net.content n));
let fun net_size n = Net.content n |> List.length in
check_pred (Gen_Base.zip (termgen 10, netgen 10 30)) NONE
      "Deletion removes term"
      (Property.==> (fn (t,n) => con t n,
                     fn (t,n) => ((Net.delete_term eq (t,t) n) |> net_size) = (net_size n - 1)))
end;
check_pred (Gen_Base.zip3 (termgen 5, netgen 5 20, Random.split))
      (SOME (fn (t,n,r) => @{make_string} (t, replace_subterm t r, n)))
      "Subterm -> Var still matches"
      (Property.==> (fn (t,n,_) => con t n,
        fn (t,n,r) =>
          let val unifs = Net.unify_term n (replace_subterm t r |> fst)
          in member eq unifs t end)
      );
())

fun print_spread () = (
check (termgen 20) NONE
      "Termsize spread"
      (fn t => (writeln (@{make_string} (Term.size_of_term t)); true));
check (netgen 10 30) NONE
      "Netsize spread"
      (fn n => (writeln (@{make_string} (Net.content n |> List.length)); true)))

end;