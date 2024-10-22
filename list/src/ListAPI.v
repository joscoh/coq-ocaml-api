(*A Subset of the OCaml List library
(https://ocaml.org/manual/5.2/api/List.html), 
showing how to use exceptions in Coq*)
From CoqCompat Require Import Monads IntFuncs.
Import MonadNotations.

Local Open Scope err_scope.

(*Declare the exceptions we need*)
Definition Failure (msg: string) : errtype := mk_errtype "Failure" msg.
Definition InvalidArg (msg: string) : errtype := mk_errtype "InvalidArg" msg. 

(*A subset of interesting functions from the API*)
Fixpoint length_aux {A: Type} (len: CoqInt.int)  (l: list A): CoqInt.int :=
  match l with
  | nil => len
  | _ :: l => length_aux (CoqInt.succ len) l
  end.
Definition length {A: Type} (l: list A) := length_aux CoqInt.zero l.

Definition hd {A: Type} (l: list A) : errorM A :=
  match l with
  | nil => throw (Failure "hd")
  | x :: _ => err_ret x
  end.

Definition tl {A: Type} (l: list A) : errorM (list A) :=
  match l with
  | nil => throw (Failure "tl")
  | _ :: t => err_ret t
  end.

Fixpoint nth_aux {A: Type} (l: list A) (n: CoqInt.int) : errorM A :=
  match l with
    | nil => throw (Failure "nth")
    | a :: l => if CoqInt.eqb n CoqInt.zero then err_ret a
      else nth_aux l (CoqInt.pred n)
  end.

Definition nth {A: Type} (l: list A) (n: CoqInt.int) : errorM A :=
  if CoqInt.lt n CoqInt.zero then throw (InvalidArg "List.nth") else
  nth_aux l n.

(*iter for state? iter2 for errstate?*)