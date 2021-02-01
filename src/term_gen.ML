structure Term_Gen =
struct
local
fun symbol_gen cut_off arg_range genS height index (state,r) =
  let
    val (num_args,r) = Random.range_int arg_range r
    val (symbol,(state,r)) = genS num_args (state,r)
  in
  if cut_off (height, index)
  then (symbol,0,(state,r))
  else (symbol,num_args,(state,r))
  end
fun term_gen freq reuse cut_off arg_range r =
  (([],[],[]),r)
  |> Generator.term_det (symbol_gen cut_off arg_range (Generator.def_sym_genS freq reuse))
  ||> snd                                                           
in
fun term_ground reuse depth argr =
  term_gen (1.0,0.0,0.0) reuse (fn (h,i) => h >= depth) argr
fun term_with_var var depth argr =
  term_gen (1.0,var,0.0) 0.3 (fn (h,i) => h >= depth) argr
end
end