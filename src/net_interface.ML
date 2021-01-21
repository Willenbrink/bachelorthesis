
signature TERM_INDEX =
sig
    type 'a T
    val empty: 'a T
    val is_empty: 'a T -> bool
    val content: ('a * 'a -> bool) -> 'a T -> 'a list

    exception INSERT
    val insert: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    val insert_safe: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T

    exception DELETE
    val delete: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    val delete_safe: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    
    val lookup: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val generalisations: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val instances: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val unifiables: ('a * 'a -> bool) -> term -> 'a T -> 'a list

(*    val subtract: ('a * 'a -> bool) -> 'a T -> 'a T -> 'a list
    val merge: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T

    val encode_type: typ -> term
Usage? *)
end;
