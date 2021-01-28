
signature TERM_INDEX =
sig
    type value
    type T
    val empty: T
    val is_empty: T -> bool
    val content: T -> value list

    exception INSERT
    val insert: (value * value -> bool) -> term * value -> T -> T
    val insert_safe: (value * value -> bool) -> term * value -> T -> T

    exception DELETE
    val delete: (value * value -> bool) -> term * value -> T -> T
    val delete_safe: (value * value -> bool) -> term * value -> T -> T
    
    val lookup: T -> term -> value list
    val generalisations: T -> term -> value list
    val instances: T -> term -> value list
    val unifiables: T -> term -> value list

    val merge: (value * value -> bool) -> T -> T -> T

end;

(* TODO move somewhere more appropriate *)
(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
    | encode_type (TFree (a, _)) = Free (a, dummyT)
    | encode_type (TVar (a, _)) = Var (a, dummyT);
