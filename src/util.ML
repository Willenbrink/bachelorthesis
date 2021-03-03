(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
    | encode_type (TFree (a, _)) = Free (a, dummyT)
    | encode_type (TVar (a, _)) = Var (a, dummyT);

fun inters _ [] = []
  | inters ord xss  =
  let
    val (xs :: xss) = sort (int_ord o apply2 length) xss
  in
  fold (Ord_List.inter ord) xss xs
  end

(* Traverse shortest list
Drop items not contained in first list from other lists during traversal *)
fun inters' _ [] = []
  | inters' _ [xs] = xs
  | inters' ord xss  =
  let
    fun discard_irrelevant smallest [] acc = (SOME smallest, acc) (* All lists traversed *)
      | discard_irrelevant _ ([]::_) _ = (NONE, []) (* One list is empty, intersection complete *)
      | discard_irrelevant smallest ((x::xs) :: xss) acc =
        case ord (smallest,x) of
          GREATER => discard_irrelevant smallest (xs :: xss) acc (* xs contains irrelevant items, drop them *)
        | LESS => (NONE, (x::xs) :: xss) (* smallest is not contained in xs. Return immediately, drop irrelevant items from other lists later. *)
        | EQUAL => discard_irrelevant smallest xss (xs :: acc) (* Item found, continue with next list *)

    fun intersect_each [] _ acc = acc
       | intersect_each (smallest :: xs) xss acc =
          (* Check if smallest is contained in all lists while dropping irrelevant items *)
          let val (smallest_maybe, xss) = discard_irrelevant smallest xss []
          in intersect_each xs xss (smallest_maybe :: acc) end
    (* Sort lists by length so we only traverse the shortest one completely *)
    val (xs :: xss) = sort (int_ord o apply2 length) xss
  in
  intersect_each xs xss []
  |> map_filter I
  end