structure Term_Gen =
struct

local
structure G = Generator
in

fun add_aterm_name_suffix suffix (Const (n, t)) = Const (n ^ "_" ^ suffix, t)
  | add_aterm_name_suffix suffix (Free (n, t)) = Free (n ^ "_" ^ suffix, t)
  | add_aterm_name_suffix suffix (Var ((n, i), t)) = Var ((n ^ "_" ^ suffix, i), t)
  | add_aterm_name_suffix _ t = t

fun symbol_gen _ arg_range gen 0 _ r = 
  let
    val (num_args, r) = G.range_int arg_range r
    (* Top-Level symbol must not be a Var as that would be pointless to store that term in an index. *)
    val (symbol, r) = G.filter (fn sym => case sym of Var _ => false | _ => true) (gen num_args) r
    val symbol = add_aterm_name_suffix (string_of_int num_args) symbol
  in ((symbol, num_args), r) end
  | symbol_gen cut_off arg_range gen height index r =
  let
    val (num_args, r) = G.range_int arg_range r
    val (symbol, r) = G.map (add_aterm_name_suffix (string_of_int num_args)) (gen num_args) r
  in
    if cut_off (height, index)
    then ((symbol, 0), r)
    else ((symbol, num_args), r)
  end

fun aterm num_ids (wc,wf,wv) = G.aterm' (G.lift num_ids) (G.nonneg 3) (wc,wf,wv,0)

fun term_gen freq num_ids cut_off arg_range =
  G.term_tree (symbol_gen cut_off arg_range (fn _ => aterm num_ids freq))

fun term_gen_def size r =                 
  let
    val (reuse, r) = Random.real r
    val (size, r) = G.range_int (1, size) r
    val (depth, r) = G.range_int (0, size div 2) r
    val depth = depth + 1 (* Every term has at least one symbol *)
    val branching_factor = 
      if depth = 1
      then size
      else (Math.ln (real size) / Math.ln (real depth)) |> Real.ceil
  in
    G.term_tree (symbol_gen (fn (h,_) => h >= depth) (0, branching_factor)
      (fn _ => aterm (reuse * real size |> Real.ceil) (9,1,0))) r
  end

fun term_ground num_ids depth argr =
  term_gen (1,0,0) num_ids (fn (h,i) => h >= depth) argr
fun term_var_reuse num_ids depth argr =
  term_gen (0,10,1) num_ids (fn (h,i) => h >= depth) argr
fun term_with_var num_ids var depth argr =
  term_gen (0,100,var) num_ids (fn (h,i) => h >= depth) argr

(*fun term_terminal_var depth argr r =
  let fun sym_gen height (index, (state, r)) =
    let
      val (num_args, r) = G.range_int argr r
      val (symbol, (state, r)) = G.def_sym_genS (1,0,0) 0.3 num_args (state, r)
    in
      if height >= depth
      then (G.var 0 0, (0, (state,r)))
      else (symbol, (num_args, (state,r)))
    end
  in G.term_det sym_gen (([],[],[]), r) ||> snd end*)

fun replace_subterm sym t r =
  let val (f,args) = Term.strip_comb t
      val (index,r) =  G.range_int (~1,length args - 1) r
      (* Generate two random values, pass r1 to rec-call, ignore returned r and return r2 instead.
         This simply avoids some annoyance with passing values around. *)
      val (r1, r2) = Random.split r
  in
  if index = ~1
  then (Term.list_comb (sym r1 |> fst, args), r2)
  else (Term.list_comb (f,nth_map index (fn t => replace_subterm sym t r1 |> fst) args), r2)
  end

fun term_instance_gen term_gen r =
  let
    val (base_term,r) = term_gen r
    val (general_term,r) =
      let val var_gen = G.map (add_aterm_name_suffix (string_of_int ~1)) (aterm 1 (0,0,1))
      in replace_subterm var_gen base_term r end
  in ((base_term, general_term), r) end

fun term_unif_gen term_gen r =
  let
    val (base_term,r) = term_gen r
    fun var_gen suffix = G.map (add_aterm_name_suffix (string_of_int suffix)) (aterm 1 (0,0,1))
    val (term1,r) = replace_subterm (var_gen ~1) base_term r
    val (term2,r) = replace_subterm (var_gen ~2) base_term r
  in ((term1, term2) ,r) end

end

end