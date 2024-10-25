type t

val zero : t
val one : t
val succ : t -> t
val pred : t -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val eq : t -> t -> bool
val lt : t -> t -> bool

val to_int : t -> int