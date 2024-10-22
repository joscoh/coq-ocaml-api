(*A Subset of the OCaml List library
(https://ocaml.org/manual/5.2/api/List.html), 
showing how to use exceptions in Coq*)
From CoqCompat Require Import Monads IntFuncs.
Import MonadNotations.

Local Open Scope err_scope.

(*Declare the exceptions we need*)
Definition Failure : errtype := mk_errtype "Failure" tt.

(*A subset of interesting functions from the API*)
Fixpoint length_aux {A: Type} (len: CoqInt.int)  (l: list A): CoqInt.int :=
  match l with
  | nil => len
  | _ :: l => length_aux (CoqInt.succ len) l
  end.
Definition length {A: Type} (l: list A) := length_aux CoqInt.zero l.

Definition hd {A: Type} (l: list A) : errorM A :=
  match l with
  | nil => throw Failure
  | x :: _ => err_ret x
  end.

Definition tl {A: Type} (l: list A) : errorM (list A) :=
  match l with
  | nil => throw Failure
  | _ :: t => err_ret t
  end.

(*TODO: nth*)