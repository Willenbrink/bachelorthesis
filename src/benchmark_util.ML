datatype tag =
    Test of string
  | Input of string
  | Index of string

fun string_of_tag x = case x of
    Test x => x
  | Input x => x
  | Index x => x

fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6

fun compare tags tests (resultss : {cpu: Time.time, elapsed: Time.time, gc: Time.time} list list) =
    (fold (fn name => fn acc => StringCvt.padLeft #" " 6 name ^ "\t" ^ acc) tags "" |> writeln;
    map_index
      (fn (i,name) =>
        fold (fn timing => fn acc => (#elapsed timing |> Time.toReal |> print_real) ^ "\t" ^ acc)
          (map (fn el => nth el i) resultss) name)
      tests |> map writeln)

fun compare (benchmark : (tag list * Timing.timing) list) name
            (filter_x : tag -> bool) (filter_y : tag -> bool) (filter_v : tag -> bool) =
  let
    fun concat (tag::tags) = fold (fn x => fn y => string_of_tag x ^ "-" ^ y) tags (string_of_tag tag)
    val xlabels : tag list list =
      benchmark
      |> map fst
      |> map (filter filter_x)
      |> filter (not o null)
      |> distinct (op =)
    val ylabels : tag list list =
      benchmark
      |> map fst
      |> map (filter filter_y)
      |> filter (not o null)
      |> distinct (op =)
    val values : (tag list * Timing.timing option) list =
      benchmark
      (* Split tags for later *)
      |> map (fn (ts,v) => (filter (fn tag => filter_x tag orelse filter_y tag) ts, (ts,v)))
      (* Remove any value which is not addressed by both x and y labels *)
      |> filter_out (fn (ts,_) => null ts)
      (* Coalesce values addressed by same (x,y) pair *)
      |> AList.coalesce (eq_set (op =))
      |> map (apsnd (fn xs => (* (x,y) * (tags,value) list *)
                      (* Check if value is associated with all the tags we want *)
                      filter (fn (tags,_) => exists filter_x tags andalso exists filter_y tags andalso exists filter_v tags) xs
                      (* Raise warning if multiple values remain *)
                      |> (fn [] => NONE
                           | [(_,x)] => SOME x
                           | (_,x)::_ => (warning "Values left, taking first"; SOME x))))
    val matrix = map (fn x => map (fn y => (x,y)) ylabels) xlabels

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
    ylabels
    |> map concat
    |> map write_row;
    writeln " "
  end