structure TT_Index : TERM_INDEX =
struct
structure TT = Termtab
type value = term
type T = value list TT.table
val empty = TT.empty
val content = TT.dest #> map #2 #> flat
val is_empty = content #> null
exception INSERT
fun insert eq (t,v) table =
  TT.map_default (t,[]) (fn xs => if member eq xs v then raise INSERT else Library.insert eq v xs) table
  handle TT.DUP _ => raise INSERT
fun insert_safe eq (t,v) table = insert eq (t,v) table handle INSERT => table

exception DELETE
fun delete eq (t,v) table =
  TT.map_default (t,[]) (fn xs => if member eq xs v then Library.remove eq v xs else raise DELETE) table
  handle TT.UNDEF _ => raise DELETE
fun delete_safe eq (t,v) table = delete eq (t,v) table handle DELETE => table

fun lookup t x = case TT.lookup t x of NONE => [] | SOME xs => xs
fun generalisations _ = raise Fail "UNDEFINED"
fun instances _ = raise Fail "UNDEFINED"
fun unifiables _ = raise Fail "UNDEFINED"

fun merge eq t1 t2 = TT.merge_list eq (t1,t2)
end