datatype tag =
    Test of string
  | Gen of string
  | Size of string
  | Index of string

fun string_of_tag x = case x of
    Test x => x
  | Gen x => x
  | Size x => x
  | Index x => x

fun tag_sub tag_sub tag_super =
  (case (tag_sub, tag_super) of
      (Test sub,Test super) => String.isSubstring sub super
    | (Gen sub,Gen super) => String.isSubstring sub super
    | (Index sub,Index super) => String.isSubstring sub super
    | (Size sub, Size super) => String.isSubstring sub super
    | (_, _) => false
  )

fun eq_tag (sub,supers) = exists (tag_sub sub) supers

fun add_timings ({elapsed = elapsed1, cpu = cpu1, gc = gc1} : Timing.timing) {elapsed = elapsed2, cpu = cpu2, gc = gc2} =
  {elapsed = elapsed1 + elapsed2,
   cpu = cpu1 + cpu2,
   gc = gc1 + gc2}

fun sum_timings [] = NONE
  | sum_timings (t::timings) = fold add_timings timings t |> SOME

fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6

fun get_table benchmark (x : tag) (y : tag) =
  let
    fun filter_labels tag =
      benchmark
      |> map fst
      |> map (filter (tag_sub tag))
      |> filter_out null
      |> distinct (op =)
    val xlabels : tag list list = filter_labels x
    val ylabels : tag list list = filter_labels y
    val matrix =
      map (fn y =>
        (y,maps (fn x =>
          benchmark
          |> filter (fn (vt,_) => forall (fn t => eq_tag (t,vt)) (x@y))
          |> map (fn (t,v) => ((x@y), (filter_out (fn t => exists (tag_sub t) (x@y)) t,v)))
          |> AList.coalesce (eq_set (op =))
          |> map (fn (_,v) => (x,v))
          )
        xlabels))
      ylabels
  in
  (xlabels,ylabels,matrix)
  end

fun print_table name show_values ((xlabels, ylabels, table)) =
  let
    fun concat (tag::tags) = fold (fn x => fn y => string_of_tag x ^ "-" ^ y) tags (string_of_tag tag)
    val xlabels' = map concat xlabels
    val xsize = 8
    fun pad x = StringCvt.padLeft #" " xsize ("  " ^ x)
    fun write_cell (xlabel, values) acc = (show_values values |> pad) ^ acc
    fun write_row (ylabel,row) =
      fold_rev write_cell row ("\t " ^ concat ylabel)
      |> writeln
  in
  fold_rev (fn tag => fn acc => pad tag ^ acc) xlabels' ("    " ^ name)
  |> warning;
  map write_row table;
  ()
  end

fun table benchmark show name x y =
  get_table benchmark x y
  |> print_table name show

fun print_timing timing = #elapsed (timing : Timing.timing) |> Time.toReal |> print_real
