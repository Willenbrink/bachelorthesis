functor Tester (Net : NET) = 
struct
structure Gen = Generator

val eq = Term.aconv_untyped
fun set_eq fst snd = eq_set eq (fst,snd)
fun term_gen n r =
  let val (num,r) = Random.range_int (0,n) r (* TODO find better solution for spread *)
  in Gen.term_fol (0.0, 0.3, 0.3) 5 num r end

fun net_gen num_term term_gen r =
  let fun aux num_term r =
        case num_term of
          0 => (Net.empty,r)
        | _ =>
          let val (term,r) = term_gen r
              val (base,r) = aux (num_term - 1) r
          in (Net.insert_term_safe eq (term,term) base,r) end
      val (num_term,r) = Random.range_int (0,num_term) r (* TODO find better solution for spread *)
  in aux num_term r end

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

val def_term_gen = term_gen 10
val def_net_gen = net_gen 30 def_term_gen

fun test () = (
check (Gen.unit) NONE
      "Empty net is empty"
      (fn _ => Net.content Net.empty = []);
check (Gen.zip (def_term_gen, def_net_gen)) NONE
      "Insertion adds value to content"
      (fn (t,n) => set_eq (t :: Net.content n) (ins t n |> Net.content));
check (def_net_gen) NONE
      "content = entries"
      (fn n => set_eq (Net.entries n) (Net.content n)
               andalso length (Net.entries n) = length (Net.content n));
check_prop (Gen.zip (def_term_gen, def_net_gen)) (SOME @{make_string})
      "Duplicate detection on insert"
      (Property.==> (fn (t,n) => con t n,
        fn (t,n) => (Net.insert_term eq (t,t) n; false) handle Net.INSERT => true)
      );
let fun net_size n = Net.content n |> List.length in
check_prop (Gen.zip (def_term_gen, def_net_gen)) (SOME @{make_string})
      "Deletion removes term"
      (Property.==> (fn (t,n) => con t n,
                     fn (t,n) => ((Net.delete_term eq (t,t) n) |> net_size) = (net_size n - 1)))
end;
check_prop (Gen.zip3 (def_term_gen, def_net_gen, Random.split))
      (SOME (fn (t,n,r) => @{make_string} (t, replace_subterm t r, n)))
      "Replacing Subterm with Var still matches"
      (Property.==> (fn (t,n,_) => con t n,
        fn (t,n,r) =>
          let val unifs = Net.unify_term n (replace_subterm t r |> fst)
          in member eq unifs t end)
      );
())


(* Benchmarking *)

fun add_timings {elapsed = elapsed1, cpu = cpu1, gc = gc1} {elapsed = elapsed2, cpu = cpu2, gc = gc2} =
  {elapsed = elapsed1 + elapsed2,
   cpu = cpu1 + cpu2,
   gc = gc1 + gc2}

fun timer name repetitions f_test f_input =
  (writeln name;
  1 upto repetitions
  |> map (fn _ => Random.new ()
          |> Timing.timing (f_input)
          |>> (fn {elapsed,...} => elapsed)
          ||> Timing.timing f_test)
  |> (fn list => fold (fn (prep_time,(test_time,result)) => fn (prep_total, test_total, results) =>
                            (prep_time + prep_total, add_timings test_time test_total, result :: results))
        list (Time.fromSeconds 0, {elapsed = Time.fromSeconds 0, cpu = Time.fromSeconds 0, gc = Time.fromSeconds 0},[]))
  |> (fn (prep,test,result) => (writeln ("Prep: " ^ @{make_string} prep ^ "s - Test: " ^ Timing.message test); result)))

(* Significantly larger for benchmarks than tests *)
val def_term_gen = term_gen 100
val def_net_gen = net_gen 1000 def_term_gen
fun benchmark () = (
timer "Creation of net" 10
      def_net_gen
      I;
timer "Content of net" 10
      (Net.content)
      (def_net_gen #> fst);
timer "Entries of net" 10
      (Net.entries)
      (def_net_gen #> fst);
timer "Get 10% of terms in net" 3
      (fn (n,r) => (n, Gen.shuffle (Net.content n) r
                       |> fst
                       |> take (length (Net.content n) div 10)))
      def_net_gen;
timer "Remove 10% of terms in net" 3
      (fn (net,terms) => fold (fn x => fn net => Net.delete_term_safe eq (x,x) net) terms net)
      (def_net_gen
       #> (fn (n,r) => (n, Gen.shuffle (Net.content n) r |> fst
           |> take (length (Net.content n) div 10)))
      );
timer "Replace Subterm with Var and retrieve matching terms" 100
      (fn (t,n,r) => Net.unify_term n (replace_subterm t r |> fst))      
      (fn r => Gen.zip3 (def_term_gen, def_net_gen, Random.split) r |> fst);
())

fun print_distribution () = (
check (def_term_gen) NONE
      "Termsize distribution"
      (fn t => (writeln (@{make_string} (Term.size_of_term t)); true));
check (def_net_gen) NONE
      "Netsize distribution"
      (fn n => (writeln (@{make_string} (Net.content n |> List.length)); true)))

end;