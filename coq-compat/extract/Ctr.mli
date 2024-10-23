module type Ctr =
 sig
  val create : unit -> unit

  val incr : unit -> unit

  val get : unit -> BigInt.t

  (*In OCaml, this is the identity function*)
  val reset : 'a -> 'a
 end

module type BigIntVal =
 sig
  val coq_val : BigInt.t
 end

module BigIntTy (_: BigIntVal) : State.ModTy with type t = BigInt.t 

module MakeCtr (_: BigIntVal) : Ctr