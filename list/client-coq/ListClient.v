Require Import Coq.Lists.List.
From ListAPI Require Import ListAPI.
Import ListNotations.
Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(*Compute [length] and [nth] of list*)
Definition test : list Z := [ 1; 2; 3; 4 ].

Eval compute in (CoqInt.to_Z (ListAPI.length test)).
(*Gives 4*)

Eval compute in (ListAPI.nth test CoqInt.one).
(*Gives inr 2 (success)*)