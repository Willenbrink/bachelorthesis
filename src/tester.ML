functor Tester (Net : NET) = 
struct
structure Gen = Generator

val eq = Term.aconv_untyped
fun set_eq fst snd = eq_set eq (fst,snd)
fun termgen n r =
  let val (num,r) = Random.range_int (0,n) r (* TODO find better solution for spread *)
  in Gen.term_fol (0.0, 0.3, 0.3) 5 num r end
fun netgen term_size num_term r1 =
  let fun aux term_size num_term r1 = case num_term of
            0 => (Net.empty,r1)
          | _ =>
            let val (r1,r2) = Random.split r1 (* Parallelize *)
                val (term,_) = termgen term_size r1
                val (base,r2) = aux term_size (num_term - 1) r2
            in (Net.insert_term_safe eq (term,term) base,r2) end
      val (num_term,r1) = Random.range_int (0,num_term) r1 (* TODO find better solution for spread *)
  in aux term_size num_term r1 end

fun check_prop gen printer name prop = Spec_Check.checkGen @{context} (gen, printer) (name, prop)
fun check gen printer name pred = check_prop gen printer name (Property.pred pred)

fun ins t n = Net.insert_term_safe eq (t,t) n
fun con t n = member eq (Net.content n) t
fun replace_subterm t r =
  let val (f,args) = Term.strip_comb t
      val (index,r) =  Random.range_int (~1,length args - 1) r
      (* Generate two random values, pass r1 to rec-call, ignore returned r and return r2 instead *)
      val (r1,r2) = Random.split r
  in
  if index = ~1
  then (Term.list_comb (Gen.var 1 r1 |> fst, args), r2)
  else (Term.list_comb (f,nth_map index (fn t => replace_subterm t r1 |> fst) args), r2)
  end

val () = (
check (Gen.unit) NONE
      "Empty net is empty"
      (fn _ => Net.content Net.empty = []);
check (Gen.zip (termgen 10, netgen 10 30)) NONE
      "Insertion adds value to content"
      (fn (t,n) => set_eq (t :: Net.content n) (ins t n |> Net.content));
check (netgen 10 30) NONE
      "content = entries"
      (fn n => set_eq (Net.entries n) (Net.content n));
check_prop (Gen.zip (termgen 5, netgen 5 20)) (SOME @{make_string})
      "Duplicate detection on insert"
      (Property.==> (fn (t,n) => con t n,
        fn (t,n) => (Net.insert_term eq (t,t) n; false) handle Net.INSERT => true)
      );
let fun net_size n = Net.content n |> List.length in
check_prop (Gen.zip (termgen 10, netgen 10 50)) (SOME @{make_string})
      "Deletion removes term"
      (Property.==> (fn (t,n) => con t n,
                     fn (t,n) => ((Net.delete_term eq (t,t) n) |> net_size) = (net_size n - 1)))
end;
check_prop (Gen.zip3 (termgen 5, netgen 5 20, Random.split))
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