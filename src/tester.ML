functor Tester (Net : NET) = 
struct
structure Gen = Generator

val eq = Term.aconv_untyped
fun set_eq fst snd = eq_set eq (fst,snd)
fun def_sym_gen n = Gen.def_sym_gen (1.0,2.0,1.0,5.0) n
fun term_gen n r =
  let
    val (num,r) = Random.range_int (0,n) r (* TODO find better solution for spread *)
  in
  Gen.term_fol def_sym_gen 5 num r
  end

fun net_gen num_term term_gen r =
  let
    fun aux num_term r =
      case num_term of
        0 => (Net.empty,r)
      | _ =>
        let val (term,r) = term_gen r
            val (base,r) = aux (num_term - 1) r
        in (Net.insert_safe eq (term,term) base,r) end
  in 
  Random.range_int (0,num_term) r
  |-> aux
  end

val ctxt = Config.put Spec_Check.examples 1 @{context};
val ctxt = Config.put Spec_Check.gen_target 100 ctxt;
fun check_prop gen printer name prop = Spec_Check.check_gen ctxt name gen printer prop (Random.deterministic_seed 1)
fun check gen printer name pred = check_prop gen printer name (Property.pred pred)

fun ins t n = Net.insert_safe eq (t,t) n
fun con t n = member eq (Net.content eq n) t
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

val def_term_gen = term_gen 30
val def_net_gen = net_gen 1 def_term_gen
fun term_in_net_gen r = (* Returns (term,net) where term is guaranteed to be in the net *)
  let
    val (net,r) = Gen.gen_prop (fn n => Net.content eq n <> []) def_net_gen r
    val (term,r) = Gen.selectL (Net.content eq net ) r
  in
  ((term,net),r)
  end
fun id_term term =
  let val id_type = Type ("fun", [TFree ("'a", ["HOL.type"]), TFree ("'a", ["HOL.type"])])
  in (Abs ("x", id_type,(Bound 0))) $ term end

fun test () = (
check (Gen.unit) NONE
      "Empty net is empty"
      (fn _ => Net.content eq Net.empty = []);
check (Gen.zip (def_term_gen, def_net_gen)) NONE
      "Insertion adds value to content"
      (fn (t,n) => set_eq (t :: Net.content eq n) (ins t n |> Net.content eq));
check (term_in_net_gen) (SOME @{make_string})
      "Duplicate detection on insert"
      (fn (t,n) => (Net.insert eq (t,t) n; false) handle Net.INSERT => true);
check (term_in_net_gen) (SOME @{make_string})
      "Deletion removes term"
      (fn (t,n) => ((Net.delete eq (t,t) n) |> Net.content eq |> List.length)
                   = (List.length (Net.content eq n) - 1));
check (Gen.zip (term_in_net_gen, Random.split))
      (SOME (fn ((t,n),r) => @{make_string} (t, replace_subterm t r, n)))
      "Replacing Subterm with Var still matches"
      (fn ((t,n),r) =>
          let val unifs = Net.unify eq (replace_subterm t r |> fst) n
          in member eq unifs t end
      );
check (term_in_net_gen) (SOME @{make_string})
      "match net t \<subseteq> unify net t"
      (fn (t,n) => subset eq ((Net.match eq t n),(Net.unify eq t n)));
check (term_in_net_gen) (SOME @{make_string})
      "1. delete works correctly when values are saved under multiple keys"
      (fn (t,n) =>
        set_eq (Net.content eq n)
               (Net.content eq (n |> Net.insert_safe eq (Const ("x",TFree ("'a",[])), t)
                               |> Net.delete eq (Const ("x",TFree ("'a",[])), t))));
check (term_in_net_gen) (SOME @{make_string})
      "2. delete works correctly when values are saved under multiple keys"
      (fn (t,n) =>
        set_eq (Net.content eq n)
          (Net.content eq (n |> Net.insert_safe eq (Const ("x",TFree ("'a",[])), t)
                          |> Net.delete eq (t, t))));

(* HOL *)
check (Gen.unit) (NONE)
      "HOL: Distinction between Var x and \\x. f x"
      (fn () =>
        let val t = @{term "x"}
            val net = Net.empty |> ins t |> ins @{term "\<lambda>x. f x"} in
        Net.match eq t net = [t]
        end);
(*
check (term_in_net_gen) (SOME @{make_string})
      "HOL: unify net (id t) == unify net t"
      (fn (t,n) => Net.unify_term n (id_term t) = Net.unify_term n t);
check (term_in_net_gen) (SOME @{make_string})
      "HOL: match net (id t) == match net t"
      (fn (t,n) => Net.match_term n (id_term t) = Net.match_term n t);
*)
())


(* Benchmarking *)

fun add_timings {elapsed = elapsed1, cpu = cpu1, gc = gc1} {elapsed = elapsed2, cpu = cpu2, gc = gc2} =
  {elapsed = elapsed1 + elapsed2,
   cpu = cpu1 + cpu2,
   gc = gc1 + gc2}

fun timer name repetitions f_test f_input =
  let
    val r = Random.new ()
    fun add_results (prep,test) (prep_total, test_total) =
      (prep + prep_total,
       add_timings test test_total)
  in
  writeln (name ^ ":");
  1 upto repetitions
  |> map (fn i => r
          |> funpow i Random.next
          |> Timing.timing f_input
          |>> (fn {elapsed,...} => elapsed)
          ||> Timing.timing f_test
          |> (fn (prep,(test,result)) => (ignore result; (prep,test)) ))
  |> (fn list => fold add_results list
      (Time.fromSeconds 0, {elapsed = Time.fromSeconds 0, cpu = Time.fromSeconds 0, gc = Time.fromSeconds 0}))
  |> tap (fn (prep,test) => writeln ("  Prep: " ^ @{make_string} prep ^ "s - Test: " ^ Timing.message test))
  |> (fn (prep,test) => (name,repetitions,prep,test))
  end

(* Significantly larger for benchmarks than tests *)
val def_term_gen = term_gen 1
val def_net_gen = net_gen 10 def_term_gen
fun benchmark () = [
timer "Creation of net" 10
      def_net_gen
      I,
timer "Content of net" 10
      (Net.content eq)
      (def_net_gen #> fst),
timer "Insert one term" 30
      (fn (net,term) => Net.insert_safe eq (term,term) net)
      (fn r => Gen.zip (def_net_gen, def_term_gen) r
               |> fst),
timer "Delete one term" 30
      (fn (net,term) => Net.delete eq (term,term) net)
      (fn r => Gen.zip (def_net_gen, def_term_gen) r
               |> fst
               |> (fn (n,t) => (Net.insert_safe eq (t,t) n,t))),
timer "Get 10% of terms in net" 3
      (fn (n,r) => (n, Gen.shuffle (Net.content eq n) r
                       |> fst
                       |> take (length (Net.content eq n) div 10)))
      def_net_gen,
timer "Delete 10% of terms in net" 3
      (fn (net,terms) => fold (fn x => fn net => Net.delete_safe eq (x,x) net) terms net)
      (def_net_gen
       #> (fn (n,r) => (n, Gen.shuffle (Net.content eq n) r |> fst
           |> take (length (Net.content eq n) div 10)))
      ),
timer "Replace part of term with Var and retrieve matching terms from net" 30
      (fn (t,n,r) => Net.unify eq (replace_subterm t r |> fst) n)
      (fn r => Gen.zip3 (def_term_gen, def_net_gen, Random.split) r |> fst)
]

fun print_distribution () = (
check (def_term_gen) NONE
      "Termsize distribution"
      (fn t => (writeln (@{make_string} (Term.size_of_term t)); true));
check (def_net_gen) NONE
      "Netsize distribution"
      (fn n => (writeln (@{make_string} (Net.content eq n |> List.length)); true)))

end;