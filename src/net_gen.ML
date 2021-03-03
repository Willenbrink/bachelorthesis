functor Net_Gen (Index : TERM_INDEX) =
struct

structure G = Generator
val eq = Term.aconv_untyped

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
  Gen_Base.range_int (0,num_term) r
  |-> aux
  end

fun terms_not_in_net_gen amount net_gen r = (* Returns (term,net) where term is guaranteed to not be in the net *)
  let
    val (net,r) = G.filter (fn n => Index.content n <> []) net_gen r
    val (con,r) = G.shuffle (Index.content net) r
    val terms = take amount con
    val net = fold (fn t => Index.delete (curry eq t) t) (take (length con div 10) con) net
  in
  ((terms,net),r)
  end

fun terms_in_net_gen amount net_gen r = (* Returns (term,net) where term is guaranteed to be in the net *)
  let
    val (net,r) = G.filter (fn n => Index.content n <> []) net_gen r
    val (con,r) = G.shuffle (Index.content net) r
    val (terms,r) =
      if amount <= length con
      then (take amount con,r)
      else
        let val ((con2,_),r) = terms_in_net_gen (amount - length con) (G.lift net) r
        in (con @ con2, r) end
        
  in
  ((terms,net),r)
  end
end