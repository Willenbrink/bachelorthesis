(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
    | encode_type (TFree (a, _)) = Free (a, dummyT)
    | encode_type (TVar (a, _)) = Var (a, dummyT);

fun apply_def f def x = case x of
    NONE => def
  | SOME v => f v

fun lookup_all eq list value =
  filter (curry eq value o fst) list
  |> map snd

fun print_size name obj =
  let val size = Real.fromInt (ML_Heap.obj_size obj) / 1000000.0 |> @{make_string}
  in name ^ ": " ^ size ^ "MB" |> writeln end

fun inters_orig _ [] = raise Fail "Empty intersect is undefined"
  | inters_orig ord (xs :: xss) = fold (Ord_List.inter ord) xss xs

(* Traverse shortest list
Drop items not contained in first list from other lists during traversal *)
fun inters _ [] = []
  | inters _ [xs] = xs
  | inters ord (xs :: xss) =
  let
    fun discard_irrelevant smallest [] acc = (SOME smallest, acc) (* All lists traversed *)
      | discard_irrelevant _ ([]::_) _ = (NONE, [[]]) (* One list is empty, intersection complete *)
      | discard_irrelevant smallest ((x::xs) :: xss) acc =
        case ord (smallest,x) of
          GREATER => discard_irrelevant smallest (xs :: xss) acc (* xs contains irrelevant items, drop them *)
        | LESS => (NONE, (x::xs) :: acc @ xss) (* smallest is not contained in xs. Return immediately, drop irrelevant items from other lists later. *)
        | EQUAL => discard_irrelevant smallest xss (xs :: acc) (* Item found, continue with next list *)

    fun intersect_each [] _ acc = acc
       | intersect_each (smallest :: ss) xss acc =
          (* Check if smallest is contained in all lists while dropping irrelevant items *)
          let val (smallest_maybe, xss) = discard_irrelevant smallest xss []
              val acc = case smallest_maybe of NONE => acc | SOME x => x :: acc
          in
          intersect_each ss xss acc
          end
    (* Sort lists by length so we only traverse the shortest one completely *)
    val (xs :: xss) =
      map (fn xs => (length xs, xs)) (xs :: xss)
      |> sort (int_ord o apply2 fst)
      |> map snd
  in
  intersect_each xs xss []
  |> rev
  end

(* Traverse first list without sorting.
Drop items not contained in first list from other lists during traversal *)
fun inters' _ [] = []
  | inters' _ [xs] = xs
  | inters' ord (xs :: xss) =
  let
    fun discard_irrelevant smallest [] acc = (SOME smallest, acc) (* All lists traversed *)
      | discard_irrelevant _ ([]::_) _ = (NONE, [[]]) (* One list is empty, intersection complete *)
      | discard_irrelevant smallest ((x::xs) :: xss) acc =
        case ord (smallest,x) of
          GREATER => discard_irrelevant smallest (xs :: xss) acc (* xs contains irrelevant items, drop them *)
        | LESS => (NONE, (x::xs) :: acc @ xss) (* smallest is not contained in xs. Return immediately, drop irrelevant items from other lists later. *)
        | EQUAL => discard_irrelevant smallest xss (xs :: acc) (* Item found, continue with next list *)

    fun intersect_each [] _ acc = acc
       | intersect_each (smallest :: ss) xss acc =
          (* Check if smallest is contained in all lists while dropping irrelevant items *)
          let val (smallest_maybe, xss) = discard_irrelevant smallest xss []
              val acc = case smallest_maybe of NONE => acc | SOME x => x :: acc
          in
          intersect_each ss xss acc
          end
    (* Sort lists by length so we only traverse the shortest one completely
    val (xs :: xss) =
      map (fn xs => (length xs, xs)) (xs :: xss)
      |> sort (int_ord o apply2 fst)
      |> map snd
    TODO disabled because sorting is slow.
*)
  in
  intersect_each xs xss []
  |> rev
  end