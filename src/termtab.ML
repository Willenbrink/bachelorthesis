structure TT_Index : TERM_INDEX =
struct

structure TT = Termtab
type 'a T = 'a list TT.table

val empty = TT.empty
fun content t = TT.dest t |> map #2 |> flat
fun is_empty t = content t |> null

exception INSERT
fun insert eq (k,v) table =
  TT.map_default (k,[]) (fn xs => if member eq xs v then raise INSERT else Library.insert eq v xs) table
  handle TT.DUP _ => raise INSERT
fun insert_safe eq (t,v) table = insert eq (t,v) table handle INSERT => table

exception DELETE
fun delete test (t) table =
  TT.map_default (t,[]) (fn xs => if member (snd #> test) xs () then Library.remove (snd #> test) () xs else raise DELETE) table
  handle TT.UNDEF _ => raise DELETE
fun delete_safe test (t) table = delete test (t) table handle DELETE => table

fun variants t x = case TT.lookup t x of NONE => [] | SOME xs => xs
fun generalisations t x = raise Fail "UNDEFINED"
fun instances t x = raise Fail "UNDEFINED"
fun unifiables t x = raise Fail "UNDEFINED"

fun merge eq t1 t2 = TT.merge_list eq (t1,t2)

end