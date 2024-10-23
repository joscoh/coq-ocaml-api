open CoqAPI
(*Simple Counter, starting at 0 and incrementing*)

(*Create the counter*)
val create : unit -> unit

(*Reset value to 0*)
val reset : unit -> unit

(*Increment counter value*)
val incr : unit -> unit

(*Get the current value of the counter*)
val read : unit -> BigInt.t