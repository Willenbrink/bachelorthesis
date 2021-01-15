
signature NET =
sig
    type 'a T
    val empty: 'a T
    val is_empty: 'a T -> bool

    exception INSERT
    val insert: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    val insert_safe: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T

    exception DELETE
    val delete: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    val delete_safe: ('a * 'a -> bool) -> term * 'a -> 'a T -> 'a T
    
    val lookup: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val variants: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val match: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val instances: ('a * 'a -> bool) -> term -> 'a T -> 'a list
    val unify: ('a * 'a -> bool) -> term -> 'a T -> 'a list

    val content: ('a * 'a -> bool) -> 'a T -> 'a list
    val subtract: ('a * 'a -> bool) -> 'a T -> 'a T -> 'a list
    val merge: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T

    val encode_type: typ -> term
end;
