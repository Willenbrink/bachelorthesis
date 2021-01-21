
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

(*    val subtract: ('a * 'a -> bool) -> 'a T -> 'a T -> 'a list
    val merge: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T

    val encode_type: typ -> term
Usage? *)
end;
