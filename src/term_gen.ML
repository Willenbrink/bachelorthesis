structure Term_Gen =
struct
local
fun symbol_gen cut_off arg_range height index (seq,r) =
  let
    val (symbol,seq) = Seq.pull seq |> (fn SOME x => x)
    val (num_args,r) = Random.range_int arg_range r
    val state' = (seq,r)
  in
  if cut_off (height, index)
  then (symbol,0,state')
  else (symbol,num_args,state')
  end
fun term_gen freq reuse cut_off arg_range r =
  Random.split r
  |>> Generator.def_sym_seq freq reuse 1
  |> Generator.term_det (symbol_gen cut_off arg_range)
  ||> snd
in
fun term_ground reuse depth argr =
  term_gen (1.0,0.0,0.1) reuse (fn (h,i) => h >= depth) argr
end
end