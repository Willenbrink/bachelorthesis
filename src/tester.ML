functor Tester (Index : TERM_INDEX) = 
struct
structure Gen = Generator
open Term_Gen
structure NG = Net_Gen(Index)
open NG
val eq = Term.aconv_untyped

val ==> = Property.==>
infix ==>

fun check_prop_base gen name prop = Spec_Check.check_base gen name prop
fun check_base gen name pred = check_prop_base gen name (Property.prop pred)
fun check_prop show gen name prop = Spec_Check.check show gen name prop
fun check show gen name pred = check_prop show gen name (Property.prop pred)
            
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

fun term_not_in_net_gen net_gen r = (* Returns (term,net) where term is guaranteed to not be in the net *)
  let
    val (net,r) = Gen.filter_bounded 100 (fn n => Index.content n <> []) net_gen r
    val (con,r) = Gen.shuffle (Index.content net) r
    val t = hd con
    val net = Index.delete (curry eq t) t net
  in ((t,net),r) end

val test_util = [ (* Tests utilities like empty, is_empty and content *)
  check_base (Gen.unit)
    "Content of empty net is empty list"
    (fn () => Index.content Index.empty = []),
  check_base (Gen.unit)
    "Empty net is empty"                                          
    (fn () => Index.is_empty Index.empty),
  check (Pretty.str o @{make_string} o Index.content) (def_net_gen)
    "Deleting all terms returns empty net"
    (fn n => fold (fn t => Index.delete (curry eq t) t) (Index.content n) n |> Index.is_empty)
]

val test_modifying = [ (* Tests functions that modify the net: insert and delete *)
  (* Insert *)
  check_prop_base (Gen.zip def_term_gen def_net_gen)
    "Insertion adds value to content"
    ((fn (t,n) => not (mem t n)) ==>
      (fn (t,n) => set_eq (t :: Index.content n) (ins t n |> Index.content))),
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
  check (Pretty.str o @{make_string}) (term_in_net_gen def_net_gen)
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
  
  (* Various *)
  check_prop_base (term_not_in_net_gen def_net_gen)
    "Insertion and deletion of new term returns identical net"
    ((fn (t,n) => not (mem t n)) ==> (fn (t,n) => con n = con (ins t n |> del t))),
  check_prop_base (term_in_net_gen def_net_gen)
    "Deletion and insertion of contained term returns identical net"
    ((fn (t,n) => mem t n) ==> (fn (t,n) => con n = con (del t n |> ins t))),
  check_base (Gen.unit)
    "Inserting terms x and y raises INSERT"
    (fn () => Index.empty
              |> Index.insert (op =) (Var (("x",0), TFree ("'a", [])), true)
              |> Index.insert (op =) (Var (("y",0), TFree ("'a", [])), true)
              |> K false
              handle Index.INSERT => true)
]

val test_queries = [
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str) (term_in_net_gen def_net_gen)
    "variants includes the queried term"
    (fn (t,n) => member eq (Index.variants n t) t),
  (* variants argument-term being included together with the subset condition implies
   that the other queries include the passed term too *)
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str) (term_in_net_gen def_net_gen)
    "lookup \<subseteq> generalisations, instances and unifiables"
    (fn (t,n) => subset eq (Index.variants n t, Index.generalisations n t)
         andalso subset eq (Index.variants n t, Index.instances n t)
         andalso subset eq (Index.variants n t, Index.unifiables n t)),
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str) (term_in_net_gen def_net_gen)
    "generalisation \<subseteq> unifiables"
    (fn (t,n) => subset eq (Index.generalisations n t, Index.unifiables n t)),
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str) (term_in_net_gen def_net_gen)
    "instances \<subseteq> unifiables"
    (fn (t,n) => subset eq (Index.instances n t, Index.unifiables n t)),
  check (fn ((t,u),n) => @{make_string} (t, u, con (ins' u n |> ins' t)) |> Pretty.str)
    (Gen.zip (Term_Gen.term_instance_gen def_term_gen) def_net_gen)
    "generalisation returns itself and generalisation"
    (fn ((t,u),n) => subset eq ([t,u],Index.generalisations (ins' u n |> ins' t) t)),
  check (fn ((t,u),n) => @{make_string} (t, u, n) |> Pretty.str)
    (Gen.zip (Term_Gen.term_instance_gen def_term_gen) def_net_gen)
    "instances returns itself and instance"
    (fn ((t,u),n) => subset eq ([t,u],Index.instances (ins' t n |> ins' u) u)),
  check (fn ((t,u),n) => @{make_string} (t, u, con (ins' u n |> ins' t)) |> Pretty.str)
    (Gen.zip (Term_Gen.term_unif_gen def_term_gen) def_net_gen)
    "unifiables returns itself and unifiable"
    (fn ((t,u),n) => subset eq ([t,u],Index.unifiables (ins' u n |> ins' t) t))
]

val test_queries_non_existing = [
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str)
    (term_not_in_net_gen def_net_gen)
    "variants of nonexisting term succeeds"
    (fn (t,n) => (
      Index.variants n t;
      true)),
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str)
    (term_not_in_net_gen def_net_gen)
    "instances of nonexisting term succeeds"
    (fn (t,n) => (
      Index.instances n t;
      true)),
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str)
    (term_not_in_net_gen def_net_gen)
    "generalisations of nonexisting term succeeds"
    (fn (t,n) => (
      Index.generalisations n t;
      true)),
  check (fn (t,n) => @{make_string} (t, con n) |> Pretty.str)
    (term_not_in_net_gen def_net_gen)
    "unifiables of nonexisting term succeeds"
    (fn (t,n) => (
      Index.unifiables n t;
      true))
]

val test_hol = [
  check_base Gen.unit
    "HOL: Distinction between Var x and \\x. f x"
    (fn () =>
      let
        val t = @{term "x"}
        val net = Index.empty |> ins t |> ins @{term "\<lambda>x. f x"}
      in Index.generalisations net t = [t] end)
]
  
val tests = test_util @ test_modifying @ test_queries @ test_queries_non_existing (* @ test_hol *)
fun test tests ctxt r = Lecker.test_group ctxt r tests
fun test_all ctxt r = test tests ctxt r

fun print_distribution term_gen net_gen ctxt r = Lecker.test_group ctxt r [
  check_base term_gen
    "Termsize distribution"
    (fn t => (writeln (@{make_string} (Term.size_of_term t)); true)),
  check_base (net_gen term_gen)
    "Netsize distribution"
    (fn n => (writeln (@{make_string} (Index.content n |> List.length)); true))
]

end