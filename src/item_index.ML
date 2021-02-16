structure Item_Index : TERM_INDEX =
struct
structure IN = Item_Net
type value = term
type T = value IN.T

val empty = IN.init Term.aconv_untyped (K [])
val is_empty = IN.is_empty
val content = IN.content

exception INSERT
fun insert eq (t,_) net =
  if IN.member net t
  then raise INSERT
  else IN.update t net
fun insert_safe eq (t,_) net = IN.update t net

exception DELETE
fun delete eq (t,_) net =
  if IN.member net t
  then IN.remove t net
  else raise DELETE
fun delete_safe eq (t,_) net = IN.remove t net

fun merge eq t1 t2 = IN.merge (t1,t2)

fun lookup t x = IN.lookup t x
fun generalisations _ = raise Fail "UNDEFINED"
fun instances _ = raise Fail "UNDEFINED"
fun unifiables _ = raise Fail "UNDEFINED"
end