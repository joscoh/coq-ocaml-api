From CtrAPI Require Import CtrAPI.
From CoqCompat Require Import Monads.
Import MonadNotations.
Local Open Scope state_scope.

Definition test :=
  _ <- create tt ;;
  x1 <- read tt ;;
  _ <- iter_st (fun _ => incr tt) (repeat 0 10);;
  x2 <- read tt ;;
  _ <- reset tt ;;
  x3 <- read tt ;;
  st_ret (x1, x2, x3).

Require Import Coq.ZArith.BinInt.

Definition runTest := 
  let '(n1, n2, n3) := run_and_reset test in
  (Z.to_nat n1, Z.to_nat n2, Z.to_nat n3).

Eval compute in runTest.
