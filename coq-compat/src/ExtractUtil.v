From CoqCompat Require Import IntFuncs CoqCtr State.
From Coq Require Export Extraction.
From ExtLib Require Import Monads EitherMonad StateMonad.

Extraction Blacklist Nat String List Option Bool Strings.

Require Export Coq.extraction.ExtrOcamlBasic.
(*Extract to native OCaml strings*)
Require Export Coq.extraction.ExtrOcamlNativeString.

Set Extraction KeepSingleton.

(* Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive prod => "(*)"  [ "(,)" ]. *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inlined Constant proj_sumbool => "".

(*BigInts*)

Extract Inlined Constant CoqBigInt.t => "BigInt.t".
Extract Inlined Constant CoqBigInt.zero => "BigInt.zero".
Extract Inlined Constant CoqBigInt.one => "BigInt.one".
Extract Inlined Constant CoqBigInt.succ => "BigInt.succ".
Extract Inlined Constant CoqBigInt.pred => "BigInt.pred".
Extract Inlined Constant CoqBigInt.add => "BigInt.add".
Extract Inlined Constant CoqBigInt.sub => "BigInt.sub".
Extract Inlined Constant CoqBigInt.mul => "BigInt.mul".
Extract Inlined Constant CoqBigInt.lt => "BigInt.lt".
Extract Inlined Constant CoqBigInt.eqb => "BigInt.eq".

(*Ints*)

Extract Inlined Constant CoqInt.int => "Stdlib.Int.t".
Extract Inlined Constant CoqInt.eqb => "Stdlib.Int.equal".
Extract Inlined Constant CoqInt.zero => "Stdlib.Int.zero".
Extract Inlined Constant CoqInt.one => "Stdlib.Int.one".
Extract Inlined Constant CoqInt.succ => "Stdlib.Int.succ".
Extract Inlined Constant CoqInt.pred => "Stdlib.Int.pred".
Extract Inlined Constant CoqInt.add => "Stdlib.Int.add".
Extract Inlined Constant CoqInt.sub => "Stdlib.Int.sub".
Extract Inlined Constant CoqInt.mul => "Stdlib.Int.mul".
Extract Inlined Constant CoqInt.lt => "(fun x y -> Stdlib.Int.compare x y < 0)".

(*Error Monad*)

Extract Constant errorM "'a" => "'a".
Extract Inductive errtype => exn [""].
Extract Inlined Constant Not_found => "Not_found".
Extract Inlined Constant Invalid_argument => "Invalid_argument".
Extract Inlined Constant err_ret => "".
Extract Inlined Constant throw => "raise".
Extract Inlined Constant err_bnd => "(@@)".
Extraction Inline Monad_errorM.

(*Monads*)

(*General state monad*)
Extract Constant st "'a" "'b" => "'b".
Extract Inlined Constant st_bind => "(@@)".
Extract Inlined Constant st_ret => "(fun x -> x)".
Extract Inlined Constant st_bind_dep => "(fun x y -> y x () ())".

(*Combine state monads*)
Extract Inlined Constant st_lift1 => "".
Extract Inlined Constant st_lift2 => "".

(*State + error monad*)
Extract Constant errState "'a" "'b" => "'b".
Extract Inlined Constant errst_bind => "(@@)".
Extract Inlined Constant errst_ret => "(fun x -> x)".
Extract Inlined Constant errst_lift1 => "".
Extract Inlined Constant errst_lift2 => "".


(*Mutable state monads*)
Extract Constant State.st_ty "'a" => "'a ref".
Extract Inlined Constant State.new_st => "ref".
Extract Inlined Constant State.st_set => "(fun x -> st_ref := x)".
Extract Inlined Constant State.st_get => "!st_ref".
Extract Inlined Constant State.st_run_UNSAFE => "(fun _ x -> st_ref := T.initial; x)".

(*Try/Catch*)
(* We need to compare names for equality because
  we cannot just put e in the match, or else it is interpreted
  as a variable/wildcard*)
Extract Inlined Constant trywith => "(fun x e ret ->
  try x ()
  with | e1 -> if e = e1 then ret () else raise e1)".
Extract Inlined Constant errst_trywith => "(fun x e ret ->
  try x ()
  with | e1 -> if e = e1 then ret () else raise e1)".
