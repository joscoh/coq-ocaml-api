open CoqAPI
(*Simple Counter, starting at 0 and incrementing*)

(*Create the counter*)
val create : unit

(*Reset value to 0*)
val reset : unit

(*Increment counter value*)
val incr : unit

(*Get the current value of the counter*)
val read : unit -> BigInt.t