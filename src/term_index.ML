
signature TERM_INDEX =
sig
    type 'a T
    val empty: 'a T
    val is_empty: 'a T -> bool
    val content: 'a T -> 'a list

    exception INSERT
    val insert: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    val insert_safe: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T

    exception DELETE
    val delete: ('a -> bool) -> term -> 'a T -> 'a T
    val delete_safe: ('a -> bool) -> term -> 'a T -> 'a T
    
    val lookup: 'a T -> term -> 'a list
    val generalisations: 'a T -> term -> 'a list
    val instances: 'a T -> term -> 'a list
    val unifiables: 'a T -> term -> 'a list

    val merge: ('a * 'a -> bool) -> 'a T -> 'a T -> 'a T

end;

(* TODO move somewhere more appropriate *)
(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
    | encode_type (TFree (a, _)) = Free (a, dummyT)
    | encode_type (TVar (a, _)) = Var (a, dummyT);
