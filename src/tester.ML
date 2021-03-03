functor Tester (Index : TERM_INDEX) = 
struct
structure Gen = Generator
open Term_Gen
structure NG = Net_Gen(Index)
open NG
val eq = Term.aconv_untyped

val ==> = Property.==>
infix ==>

val ctxt = Config.put Configuration.num_counterexamples 1 @{context};
val ctxt = Config.put Configuration.max_success 100 ctxt;
fun check_prop_base gen name prop () = Spec_Check.check_base gen name prop ctxt (Random.new ())
fun check_base gen name pred () = check_prop_base gen name (Property.property pred) ()
fun check_prop show gen name prop () = Spec_Check.check show gen name prop ctxt (Random.new ())
fun check show gen name pred () = check_prop show gen name (Property.property pred) ()

fun ins t n = Index.insert eq (t,t) n
fun ins' t n = Index.insert_safe eq (t,t) n
fun del t n = Index.delete (curry eq t) t n
fun del' t n = Index.delete_safe (curry eq t) t n
fun con n = Index.content n
fun mem t n = member eq (con n) t
fun set_eq fst snd = eq_set eq (fst,snd)
fun con_eq fst snd = set_eq (Index.content fst) (Index.content snd)

val def_term_gen = term_gen_def 6
val def_net_gen = net_gen 5 def_term_gen

fun term_in_net_gen net_gen r =
  terms_in_net_gen 1 net_gen r
  |> (fn ((ts,n),r) => ((if null ts then @{term "x"} else hd ts, n), r))

val test_util = [ (* Tests utilities like empty, is_empty and content *)
check_base (Gen.unit)
      "Content of empty net is empty list"
      (fn () => Index.content Index.empty = []),
check_base (Gen.unit)
      "Empty net is empty"
      (fn () => Index.is_empty Index.empty),
check (fn n => @{make_string} (Index.content n)) (def_net_gen)
      "Deleting all terms returns empty net"
      (fn n => fold (fn t => Index.delete (curry eq t) t) (Index.content n) n |> Index.is_empty)
]

val test_modifying = [ (* Tests functions that modify the net: insert and delete *)
(* Insert *)
check_prop_base (Gen.zip def_term_gen def_net_gen)
      "Insertion adds value to content"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => set_eq (t :: Index.content n) (ins t n |> Index.content))),
check_prop_base (Gen.zip def_term_gen def_net_gen)
      "Insertion of new term increases size"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => length (ins t n |> con) = length (con n) + 1)),
check_base (term_in_net_gen def_net_gen)
      "Duplicate exception on insert"
      (fn (t,n) => (ins t n; false) handle Index.INSERT => true),
check_base (term_in_net_gen def_net_gen)
      "Safe insert raises no exception"
      (fn (t,n) => (ins' t n; true) handle Index.INSERT => false),

(* Delete *)
check_base (term_in_net_gen def_net_gen)
      "Deletion removes value from content"
      ((fn (t,n) => set_eq (Index.content n |> remove eq t) (Index.content (del t n)))),
check_base (term_in_net_gen def_net_gen)
      "Deletion of contained term decreases size"
      ((fn (t,n) => length (del t n |> con) = length (con n) - 1)),
check_base (term_in_net_gen def_net_gen)
      "Deleting twice raises exception"
      (fn (t,n) => (del t n |> del t; false) handle Index.DELETE => true),
check_base (term_in_net_gen def_net_gen)
      "Safe delete raises no exception"
      (fn (t,n) => (del t n |> del' t; true) handle Index.DELETE => false),
check @{make_string} (term_in_net_gen def_net_gen)
      "Value saved under multiple keys gets deleted correctly"
      (fn (t,n) =>
        let val snd_term = Const ("x", dummyT)
        in
        con_eq n (n |> Index.insert_safe eq (snd_term, t)
                    |> Index.delete (curry eq t) (snd_term))
        andalso
        con_eq n (n |> Index.insert_safe eq (snd_term, t)
                    |> Index.delete (curry eq t) t)
        end),

(* Combination *)
check_prop_base (Gen.zip def_term_gen def_net_gen)
      "Insertion and deletion of new term returns identical net"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => con n = con (ins t n |> del t))),
check_prop_base (term_in_net_gen def_net_gen)
      "Deletion and insertion of contained term returns identical net"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => con n = con (ins t n |> del t)))
]

val test_queries = [
check (fn (t,n) => @{make_string} (t, con n)) (term_in_net_gen def_net_gen)
      "variants includes the queried term"
      (fn (t,n) => member eq (Index.lookup n t) t),
(* variants argument-term being included together with the subset condition implies
 that the other queries include the passed term too *)
check (fn (t,n) => @{make_string} (t, con n)) (term_in_net_gen def_net_gen)
      "lookup \<subseteq> generalisations, instances and unifiables"
      (fn (t,n) => subset eq (Index.lookup n t, Index.generalisations n t)
           andalso subset eq (Index.lookup n t, Index.instances n t)
           andalso subset eq (Index.lookup n t, Index.unifiables n t)),
check (fn (t,n) => @{make_string} (t, con n)) (term_in_net_gen def_net_gen)
      "generalisation \<subseteq> unifiables"
      (fn (t,n) => subset eq (Index.generalisations n t, Index.unifiables n t)),
check (fn (t,n) => @{make_string} (t, con n)) (term_in_net_gen def_net_gen)
      "instances \<subseteq> unifiables"
      (fn (t,n) => subset eq (Index.instances n t, Index.unifiables n t)),
check (fn ((t,u),n) => @{make_string} (t, u, con (ins' u n |> ins' t)))
      (Gen.zip (Term_Gen.term_instance_gen def_term_gen) def_net_gen)
      "generalisation returns itself and generalisation"
      (fn ((t,u),n) => subset eq ([t,u],Index.generalisations (ins' u n |> ins' t) t)),
check (fn ((t,u),n) => @{make_string} (t, u, n))
      (Gen.zip (Term_Gen.term_instance_gen def_term_gen) def_net_gen)
      "instances returns itself and instance"
      (fn ((t,u),n) => subset eq ([t,u],Index.instances (ins' t n |> ins' u) u)),
check (fn ((t,u),n) => @{make_string} (t, u, con (ins' u n |> ins' t)))
      (Gen.zip (Term_Gen.term_unif_gen def_term_gen) def_net_gen)
      "unifiables returns itself and unifiable"
      (fn ((t,u),n) => subset eq ([t,u],Index.unifiables (ins' u n |> ins' t) t))
]

val test_hol = [
check_base Gen.unit
      "HOL: Distinction between Var x and \\x. f x"
      (fn () =>
        let val t = @{term "x"}
            val net = Index.empty |> ins t |> ins @{term "\<lambda>x. f x"} in
        Index.generalisations net t = [t]
        end)
]
  
val tests = test_util @ test_modifying @ test_queries (* @ test_hol *)
fun test () = fold I tests ()

fun print_distribution term_gen net_gen () = (
check_base term_gen
      "Termsize distribution"
      (fn t => (writeln (@{make_string} (Term.size_of_term t)); true)) ();
check_base (net_gen term_gen)
      "Netsize distribution"
      (fn n => (writeln (@{make_string} (Index.content n |> List.length)); true)) ())

end;