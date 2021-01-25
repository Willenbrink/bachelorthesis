functor Benchmark (Index : TERM_INDEX where type value = term) =
struct

structure Gen = Generator

val eq = Term.aconv_untyped

fun replace_subterm sym t r =
  let val (f,args) = Term.strip_comb t
      val (index,r) =  Random.range_int (~1,length args - 1) r
      (* Generate two random values, pass r1 to rec-call, ignore returned r and return r2 instead.
         This simply avoids some annoyance with passing values around. *)
      val (r1,r2) = Random.split r
  in
  if index = ~1
  then (Term.list_comb (sym r1 |> fst, args), r2)
  else (Term.list_comb (f,nth_map index (fn t => replace_subterm sym t r1 |> fst) args), r2)
  end

fun term_in_net_gen net_gen r = (* Returns (term,net) where term is guaranteed to be in the net *)
  let
    val (net,r) = Gen.gen_prop (fn n => Index.content n <> []) net_gen r
    val (term,r) = Gen.selectL (Index.content net ) r
  in
  ((term,net),r)
  end
fun term_instance_gen term_gen r =
  let val (base_term,r) = term_gen r
      val (general_term,r) = replace_subterm (Gen.var 1) base_term r
  in
  ((base_term,general_term),r)
  end
fun term_unif_gen term_gen r =
  let val (base_term,r) = term_gen r
      val (term1,r) = replace_subterm (Gen.var 1) base_term r
      val (term2,r) = replace_subterm (Gen.var 1) base_term r
  in
  ((term1,term2),r)
  end



fun net_gen num_term term_gen r =
  let
    fun aux num_term r =
      case num_term of
        0 => (Index.empty,r)
      | _ =>
        let val (term,r) = term_gen r
            val (base,r) = aux (num_term - 1) r
        in (Index.insert_safe eq (term,term) base,r) end
  in 
  Random.range_int (0,num_term) r
  |-> aux
  end


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
          |> Timing.timing (f_input #> fst)
          |>> (fn {elapsed,...} => elapsed)
          ||> Timing.timing f_test
          |> (fn (prep,(test,result)) => (ignore result; (prep,test)) ))
  |> (fn list => fold add_results list
      (Time.fromSeconds 0, {elapsed = Time.fromSeconds 0, cpu = Time.fromSeconds 0, gc = Time.fromSeconds 0}))
  (*|> tap (fn (prep,test) => writeln ("  Prep: " ^ @{make_string} prep ^ "s - Test: " ^ Timing.message test))*)
  |> (fn (prep,test) => (name,prep,test))
  end

(* Significantly larger for benchmarks than tests *)
fun benchmark term_gen net_gen = [
timer "Creation of net" 10
      net_gen
      (fn x => (x, Random.new ())),
timer "Content of net" 10
      (Index.content)
      (net_gen),
timer "Insert one term" 30
      (fn (net,term) => Index.insert_safe eq (term,term) net)
      (fn r => Gen.zip (net_gen, term_gen) r),
timer "Delete one term" 30
      (fn (net,term) => Index.delete eq (term,term) net)
      (fn r => Gen.zip (net_gen, term_gen) r
               |>> (fn (n,t) => (Index.insert_safe eq (t,t) n,t))),
timer "Get 10% of terms in net" 3
      (fn (n,r) => (n, Gen.shuffle (Index.content n) r
                       |> fst
                       |> take (length (Index.content n) div 10)))
      (Gen.zip (net_gen, Random.split)),
timer "Delete 10% of terms in net" 3
      (fn (net,terms) => fold (fn x => fn net => Index.delete_safe eq (x,x) net) terms net)
      (net_gen
       #> (fn (n,r) => (n, Gen.shuffle (Index.content n) r
                           |>> take (length (Index.content n) div 10)))
       #> (fn (n,(c,r)) => ((n,c),r))
      )
]

fun benchmark_queries term_gen net_size repetitions =
  let val timer = (fn name => timer name repetitions)
      val net_gen = net_gen net_size term_gen
      val term_in_net_gen = term_in_net_gen net_gen in [
timer "Lookup existing term"
      (fn (t,n) => Index.lookup n t)
      (term_in_net_gen),
timer "Lookup non-existing term"
      (fn (t,n) => Index.lookup n t)
      (Gen.zip (term_gen,net_gen)), (* TODO use precondition when using quichcheck *)
timer "instances existing term"
      (fn (t,n) => Index.instances n t)
      (term_in_net_gen),
timer "instances non-existing term"
      (fn (t,n) => Index.instances n t)
      (Gen.zip (term_gen,net_gen)),
timer "generalisations existing term"
      (fn (t,n) => Index.generalisations n t)
      (term_in_net_gen),
timer "generalisations non-existing term"
      (fn (t,n) => Index.generalisations n t)
      (Gen.zip (term_gen,net_gen)),
timer "unifiables existing term"
      (fn (t,n) => Index.unifiables n t)
      (term_in_net_gen),
timer "unifiables non-existing term"
      (fn (t,n) => Index.unifiables n t)
      (Gen.zip (term_gen,net_gen))
] end
end

fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6
fun diff {elapsed = _, cpu = c1, gc = _} {elapsed = _, cpu = c2, gc = _} =
  (Time.toReal c1 - Time.toReal c2, (Time.toReal c1) / (Time.toReal c2))

fun compare name1 name2 res1 res2 =
  let val res =
    map_index (fn (i,(name,_,x)) => (name,diff x (nth res2 i |> (fn (_,_,x) => x)))) res1
  in
  (writeln (name1 ^ " vs " ^ name2 ^ 
            "\nAbs. (" ^ name1 ^" - " ^ name2 ^ ")\tRel. (" ^ name1 ^ "/" ^ name2 ^ ")\tName");
   map (fn (name,(abs,rel)) => (print_real abs ^ "s\t\t"
                                  ^ print_real rel ^ "\t\t"
                                  ^ name)
                                  |> writeln) res)
  end