
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
