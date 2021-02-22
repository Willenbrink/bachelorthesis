structure Term_Gen =
struct
local
fun symbol_gen cut_off arg_range gen height index r =
  let
    val (num_args,r) = Random.range_int arg_range r
    val (symbol,r) = gen num_args r
  in
  if cut_off (height, index)
  then (symbol,0,r)
  else (symbol,num_args,r)
  end
fun term_gen freq num_ids cut_off arg_range r =
  r
  |> Generator.term_det (symbol_gen cut_off arg_range (Generator.def_sym_gen freq num_ids))
in
fun term_ground num_ids depth argr =
  term_gen (1,0,0) num_ids (fn (h,i) => h >= depth) argr
fun term_var_reuse num_ids depth argr =
  term_gen (10,1,0) num_ids (fn (h,i) => h >= depth) argr
fun term_with_var num_ids var depth argr =
  term_gen (100,var,0) num_ids (fn (h,i) => h >= depth) argr

fun term_terminal_var depth argr r =
  let fun sym_gen height index (state,r) =
    let
      val (num_args,r) = Random.range_int argr r
    val (symbol,(state,r)) = Generator.def_sym_genS (1,0,0) 0.3 num_args (state,r)
    in
    if height >= depth
    then (Generator.var 0 0,0,(state,r))
    else (symbol,num_args,(state,r))
    end
  in
  Generator.term_det (sym_gen) (([],[],[]),r) ||> snd
  end

end
end