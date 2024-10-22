(*A very simple counter API*)
From CoqCompat Require Import Monads CoqCtr.

Module ZVal <: BigIntVal.
Definition val := CoqBigInt.zero.
End ZVal.

Module C := MakeCtr ZVal.

Definition create : ctr unit :=
  C.create.

Definition reset : ctr unit :=
  C.create.

Definition incr : ctr unit :=
  C.incr tt.

Definition read : unit -> ctr CoqBigInt.t :=
  fun _ => C.get tt.