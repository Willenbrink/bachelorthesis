
signature NET =
sig
    type key
    val key_of_term: term -> key list
    val encode_type: typ -> term
    type 'a net
    val empty: 'a net
    val is_empty: 'a net -> bool

    exception INSERT
    val insert: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
    val insert_term: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
    val insert_safe: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
    val insert_term_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net

    exception DELETE
    val delete: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
    val delete_term: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
    val delete_safe: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
    val delete_term_safe: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net

    val lookup: 'a net -> key list -> 'a list
    val match_term: 'a net -> term -> 'a list
    val unify_term: 'a net -> term -> 'a list
    val entries: 'a net -> 'a list
    val subtract: ('b * 'a -> bool) -> 'a net -> 'b net -> 'b list
    val merge: ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
    val content: 'a net -> 'a list
end;
