functor Tester (Index : TERM_INDEX where type value = term) = 
struct
structure Gen = Generator

val ==> = Property.==>
infix 1 ==>

val eq = Term.aconv_untyped
fun def_sym_gen n = Gen.def_sym_gen (2.0,1.0,5.0) n
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
        0 => (Index.empty,r)
      | _ =>
        let val (term,r) = term_gen r
            val (base,r) = aux (num_term - 1) r
        in (Index.insert_safe eq (term,term) base,r) end
  in 
  Random.range_int (0,num_term) r
  |-> aux
  end

val ctxt = Config.put Spec_Check.examples 1 @{context};
val ctxt = Config.put Spec_Check.gen_target 100 ctxt;
fun check_prop gen printer name prop () = Spec_Check.check_gen ctxt name gen printer prop (Random.deterministic_seed 1)
fun check gen printer name pred () = check_prop gen printer name (Property.pred pred) ()

fun ins t n = Index.insert eq (t,t) n
fun ins' t n = Index.insert_safe eq (t,t) n
fun del t n = Index.delete eq (t,t) n
fun del' t n = Index.delete_safe eq (t,t) n
fun con n = Index.content n
fun mem t n = member eq (con n) t
fun set_eq fst snd = eq_set eq (fst,snd)
fun con_eq fst snd = set_eq (Index.content fst) (Index.content snd)
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

val def_term_gen = term_gen 6
val def_net_gen = net_gen 100 def_term_gen
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

val test_util = [ (* Tests utilities like empty, is_empty and content *)
check (Gen.unit) NONE
      "Content of empty net is empty list"
      (fn () => Index.content Index.empty = []),
check (Gen.unit) NONE
      "Empty net is empty"
      (fn () => Index.is_empty Index.empty),
check (def_net_gen) (SOME (fn n => @{make_string} (Index.content n)))
      "Deleting all terms returns empty net"
      (fn n => fold (fn t => Index.delete eq (t,t)) (Index.content n) n |> Index.is_empty)
]

val test_modifying = [ (* Tests functions that modify the net: insert and delete *)
(* Insert *)
check_prop (Gen.zip (def_term_gen, def_net_gen)) NONE
      "Insertion adds value to content"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => set_eq (t :: Index.content n) (ins t n |> Index.content))),
check_prop (Gen.zip (def_term_gen, def_net_gen)) NONE
      "Insertion of new term increases size"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => length (ins t n |> con) = length (con n) + 1)),
check (term_in_net_gen def_net_gen) NONE
      "Duplicate exception on insert"
      (fn (t,n) => (ins t n; false) handle Index.INSERT => true),
check (term_in_net_gen def_net_gen) NONE
      "Safe insert raises no exception"
      (fn (t,n) => (ins' t n; true) handle Index.INSERT => false),

(* Delete *)
check (term_in_net_gen def_net_gen) NONE
      "Deletion removes value from content"
      ((fn (t,n) => set_eq (Index.content n |> remove eq t) (Index.content (del t n)))),
check (term_in_net_gen def_net_gen) NONE
      "Deletion of contained term decreases size"
      ((fn (t,n) => length (del t n |> con) = length (con n) - 1)),
check (term_in_net_gen def_net_gen) NONE
      "Duplicate exception on delete"
      (fn (t,n) => (del t n |> del t; false) handle Index.DELETE => true),
check (term_in_net_gen def_net_gen) NONE
      "Safe delete raises no exception"
      (fn (t,n) => (del t n |> del' t; true) handle Index.DELETE => false),
check (term_in_net_gen def_net_gen) (SOME @{make_string})
      "Value saved under multiple keys gets deleted correctly"
      (fn (t,n) =>
        let val snd_term = Const ("x", dummyT)
        in
        con_eq n (n |> Index.insert_safe eq (snd_term, t)
                    |> Index.delete eq (snd_term, t))
        andalso
        con_eq n (n |> Index.insert_safe eq (snd_term, t)
                    |> Index.delete eq (t, t))
        end),

(* Combination *)
check_prop (Gen.zip (def_term_gen, def_net_gen)) NONE
      "Insertion and deletion of new term returns identical net"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => con n = con (ins t n |> del t))),
check_prop (term_in_net_gen def_net_gen) NONE
      "Deletion and insertion of contained term returns identical net"
      ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => con n = con (ins t n |> del t)))
]

val test_queries = [
check (term_in_net_gen def_net_gen) (SOME @{make_string})
      "variants includes the queried term"
      (fn (t,n) => member eq (Index.lookup n t) t),
(* variants argument-term being included together with the subset condition implies
 that the other queries include the passed term too *)
check (term_in_net_gen def_net_gen) (SOME @{make_string})
      "lookup \<subseteq> generalisations, instances and unifiables"
      (fn (t,n) => subset eq (Index.lookup n t, Index.generalisations n t)
           andalso subset eq (Index.lookup n t, Index.instances n t)
           andalso subset eq (Index.lookup n t, Index.unifiables n t)),
check (term_in_net_gen def_net_gen) (SOME @{make_string})
      "generalisation \<subseteq> unifiables"
      (fn (t,n) => subset eq (Index.generalisations n t, Index.unifiables n t)),
check (term_in_net_gen def_net_gen) (SOME @{make_string})
      "instances \<subseteq> unifiables"
      (fn (t,n) => subset eq (Index.instances n t, Index.unifiables n t)),
check (Gen.zip (term_instance_gen def_term_gen, def_net_gen))
      (SOME (fn ((t,u),n) => @{make_string} (t, u, con (ins' u n |> ins' t))))
      "generalisation returns itself and generalisation"
      (fn ((t,u),n) => subset eq ([t,u],Index.generalisations (ins' u n |> ins' t) t)),
check (Gen.zip (term_instance_gen def_term_gen, def_net_gen))
      (SOME (fn ((t,u),n) => @{make_string} (t, u, n)))
      "instances returns itself and instance"
      (fn ((t,u),n) => subset eq ([t,u],Index.instances (ins' t n |> ins' u) u)),
check (Gen.zip (term_unif_gen def_term_gen, def_net_gen))
      (SOME (fn ((t,u),n) => @{make_string} (t, u, con (ins' u n |> ins' t))))
      "unifiables returns itself and unifiable"
      (fn ((t,u),n) => subset eq ([t,u],Index.unifiables (ins' u n |> ins' t) t))
]

val test_hol = [
check (Gen.unit) (NONE)
      "HOL: Distinction between Var x and \\x. f x"
      (fn () =>
        let val t = @{term "x"}
            val net = Index.empty |> ins t |> ins @{term "\<lambda>x. f x"} in
        Index.generalisations net t = [t]
        end)
]
  
val tests = test_util @ test_modifying @ test_queries @ test_hol
fun test () = fold I tests ()

fun print_distribution term_gen net_gen () = (
check (term_gen) NONE
      "Termsize distribution"
      (fn t => (writeln (@{make_string} (Term.size_of_term t)); true)) ();
check (net_gen term_gen) NONE
      "Netsize distribution"
      (fn n => (writeln (@{make_string} (Index.content n |> List.length)); true)) ())

end;