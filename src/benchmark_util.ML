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

fun is_subtag tag_sub tag_super =
  (case (tag_sub, tag_super) of
      (Test sub,Test super) => String.isSubstring sub super
    | (Gen sub,Gen super) => String.isSubstring sub super
    | (Index sub,Index super) => String.isSubstring sub super
    | (Size sub, Size super) => String.isSubstring sub super
    | (_, _) => false
  )

fun exists_supertag (sub,supers) = exists (is_subtag sub) supers

fun sum_timings [] = NONE
  | sum_timings (t::timings) = fold Spec_Check_Base.add_timing timings t |> SOME

fun print_real real = 
  real
  |> Real.fmt (StringCvt.FIX (SOME 3))
  |> StringCvt.padLeft #" " 6

fun get_table benchmark (x : tag) (y : tag) =
  let
    fun filter_labels tag =
      benchmark
      |> map fst
      |> map (filter (is_subtag tag))
      |> filter_out null
      |> map the_single
      |> distinct (op =)
    (* Get the list of x/y labels. Each label is a single tag. *)
    val xlabels : tag list = filter_labels x
    val ylabels : tag list = filter_labels y

    fun filter_tag tag table = filter (fn (val_tags, _) => exists_supertag (tag, val_tags)) table
    val table =
      map (fn y =>
        let val row = maps (fn x =>
            benchmark
            |> filter_tag y
            |> filter_tag x
            (* Store tests addressed by identical tags in one list *)
            |> map (fn (val_tags,v) => ([x, y], (filter_out (fn t => exists_supertag (t,[x, y])) val_tags,v)))
            |> AList.coalesce (eq_set (op =))
            |> map (fn (_, v) => (x, v))
            )
            xlabels
        in
        (y, row)
        end)
      ylabels
  in (xlabels, ylabels, table) end

fun print_table name show_values ((xlabels, ylabels, table)) =
  let
    val xsize = 8
    fun pad x = StringCvt.padLeft #" " xsize ("  " ^ x)

    val longest_row = map (snd #> length) table |> sort_distinct int_ord |> rev |> hd
    fun write_cell row i =
      let
        val xlab = nth xlabels i
        val cell = find_first (fn (x,v) => is_subtag x xlab) row
      in
      show_values (cell |> Option.valOf |> snd handle Option => []) |> pad
      end
    fun write_row (ylabel,row) =
      fold_rev (curry op ^) (map (write_cell row) (0 upto (longest_row - 1))) ("\t " ^ string_of_tag ylabel)
  in
    (name ^ "\n" ^ fold_rev (fn tag => fn acc => pad (string_of_tag tag) ^ acc) xlabels "")
    |> fold (fn x => fn acc => acc ^ "\n" ^ write_row x) table
    |> writeln
  end

fun table benchmark show name x y =
  get_table benchmark x y
  |> print_table name show

fun print_values filter_tags values =
  let
(*
    val filter_tags =
      if eq_tag (Size "", filter_tags)
      then filter_tags
      else (Size "") :: filter_tags
*)
    val values' =
      values
      |> filter (fn (t,_) => forall (fn filter_tag => exists_supertag (filter_tag,t)) filter_tags)
    val () =
      values'
      |> map fst
      |> map (fn val_tags => filter_out (fn vt => exists (fn ft => is_subtag ft vt) filter_tags) val_tags)
      |> distinct (op =)
      |> (fn x => if length x > 1 then raise Fail ("Multiple values: " ^ @{make_string} x ^ "\n remaining of: " ^ @{make_string} values) else ())
  in
    values'
    |> map snd
    |> (fn [] => NONE | list => fold (curry op Time.+) list (Time.zeroTime) |> SOME)
    |> apply_def (@{make_string}) "N/A"
  end

fun print_timing timing = #elapsed (timing : Timing.timing) |> Time.toReal |> print_real

fun timer name f_test inputs =
  let val r = Random.new ()
  in
    (*writeln (name);*)
    inputs
    |> map_index (fn (i,input) => r
            |> funpow i Random.next
            |> input
            |> fst (* Discard returned random value *)
            |> Timing.timing f_test
            |> fst)
    |> map (#cpu)
    |> (fn list => fold (curry op +) list (Time.fromSeconds 0))
    |> (fn test => (Test name, test))
  end