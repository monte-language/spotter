type ('a, 's) t = 's -> 'a * 's

val run : ('a, 's) t -> 's -> 'a * 's
val return : 'a -> ('a, 's) t
val map : ('a -> 'b) -> ('a, 's) t -> ('b, 's) t
val bind : ('a, 's) t -> ('a -> ('b, 's) t) -> ('b, 's) t
val and_then : (unit, 's) t -> ('a, 's) t -> ('a, 's) t
val get : ('s, 's) t
val set : 's -> (unit, 's) t
val modify : ('s -> 's) -> (unit, 's) t
