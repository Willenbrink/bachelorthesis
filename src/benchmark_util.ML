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
      fold write_cell row ("\t " ^ concat ylabel)
      |> writeln
  in
  fold_rev (fn tag => fn acc => pad tag ^ acc) xlabels' ("    " ^ name)
  |> writeln;
  map write_row table;
  ()
  end

fun table benchmark show name x y =
  get_table benchmark x y
  |> print_table name show

fun print_timing timing = #elapsed (timing : Timing.timing) |> Time.toReal |> print_real

fun compare (benchmark : (tag list * Timing.timing) list) name
            (x : tag) (y : tag) (v : tag) =
  let
    fun concat (tag::tags) = fold (fn x => fn y => string_of_tag x ^ "-" ^ y) tags (string_of_tag tag)
    fun filter_labels tag =
      benchmark
      |> map fst
      |> map (filter (tag_sub tag))
      |> filter_out null
      |> distinct (op =)
    val xlabels : tag list list = filter_labels x
    val ylabels : tag list list = filter_labels y
    val matrix =
      maps (fn x =>
        map (fn y =>
          (*AList.coalesce (fn (t1,t2) =>
            subset (uncurry tag_sub) ((x@y),t1)
            andalso
            subset (uncurry tag_sub) ((x@y),t2)
            )*)
          filter (fn (t,_) => subset (uncurry tag_sub) ((x@y),t)) benchmark
          |> map (fn (t,v) => ((x@y), (filter_out (fn t => exists (tag_sub t) (x@y)) t,v)))
          |> AList.coalesce (eq_set (op =))
          )
        ylabels)
      xlabels
    val values : (tag list * Timing.timing option) list =
      benchmark
      (* Split tags for later *)
      |> map (fn (ts,v) => (ts,(ts,v)))
      (* Remove any value which is not addressed by some x and some y labels *)
      |> filter_out (fn (ts,_) => (exists (tag_sub x) andf exists (tag_sub y)) ts)
      (* Coalesce values addressed by same (x,y) pair *)
      |> AList.coalesce (eq_set (op =))
      |> map (apsnd (fn xs => (* (x,y) * (tags,value) list *)
                      (* Check if value is associated with all the tags we want *)
                      filter (fn (tags,_) => exists (tag_sub x) tags andalso exists (tag_sub y) tags andalso exists (tag_sub v) tags) xs
                      (* Raise warning if multiple values remain *)
                      |> (fn [] => NONE
                           | [(_,x)] => SOME x
                           | (_,x)::_ => (warning "Values left, taking first"; SOME x))))

    val xlabels' =
      map concat xlabels |> rev
    val xsize = 8
    fun pad x = StringCvt.padLeft #" " xsize ("  " ^ x)
    val () =
      fold (fn tag => fn acc => pad tag ^ acc) xlabels' ("    " ^ name)
      |> writeln
    fun write_row ylabel =
      values
      |> filter (fn (tags,_) => exists (fn tag => string_of_tag tag = ylabel) tags)
      |> sort (fn ((x,_),(y,_)) => string_ord (concat x, concat y))
      |> map snd
      |> (fn x => fold (fn timing => fn acc =>
                           (case timing of
                                 NONE => ""
                               | SOME timing => #elapsed (timing : Timing.timing) |> Time.toReal |> print_real |> pad)
                          ^ acc
                       )
                       x ("\t " ^ ylabel))
      |> writeln
    fun write_row ylabel =
      xlabels'
      (* Lookup associated values *)
      |> map (fn x => AList.lookup (fn (t1,t2) => eq_set (string_ord #> is_equal) (t1, map string_of_tag t2)) values [x,ylabel])
      |> map (fn NONE => NONE | SOME NONE => NONE | SOME (SOME xs) => SOME xs)
      |> (fn x => fold (fn timing => fn acc =>
                           (case timing of
                                 NONE => ""
                               | SOME timing => #elapsed (timing : Timing.timing) |> Time.toReal |> print_real |> pad)
                          ^ acc
                       )
                       x ("\t " ^ ylabel))
      |> writeln
  in
    matrix
    |> @{make_string}
    |> writeln
(*;
    ylabels
    |> map concat
    |> map write_row;
    writeln " " *)
  end