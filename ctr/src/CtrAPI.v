(*A very simple counter API*)
From CoqCompat Require Import Monads CoqCtr.

Module ZVal <: BigIntVal.
Definition val := CoqBigInt.zero.
End ZVal.

Module C := MakeCtr ZVal.

Definition create : unit -> ctr unit :=
  C.create.

Definition reset : unit -> ctr unit :=
  C.create.

Definition incr : unit -> ctr unit :=
  C.incr.

Definition read : unit -> ctr CoqBigInt.t :=
  C.get.

(*For Coq only, not in .mli file*)
Definition run_and_reset {A: Type} : ctr A -> A :=
  @C.reset A.