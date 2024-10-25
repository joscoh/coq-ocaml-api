Require Export Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.

(*Here, we provide an interface for big integers.
  In Coq, we implement them using [Z]. We extract
  to OCaml's Zarith.t.
  Any code using BigInt.t should ONLY use this interface
  to ensure that the extracted code is valid OCaml and does
  not rely on Coq's Z type.
  It is easy to extend this with new functions; we include only
  a minimum subset for now*)

Definition t : Set := Z.
Definition zero : t := 0.
Definition one : t := 1.
Definition succ : t -> t := Z.succ.
Definition pred : t -> t := Z.pred.
Definition add : t -> t -> t := Z.add.
Definition sub : t -> t -> t := Z.sub.
Definition mul: t -> t -> t := Z.mul.
Definition lt : t -> t -> bool := Z.ltb.
Definition eqb : t -> t -> bool := Z.eqb.

(*For specification*)
Definition to_Z : t -> Z := id.

(*Specs - We write these clearly here bceause they are 
  axioms of the OCaml Zarith implementation*)

Lemma eqb_eq (z1 z2: t) : eqb z1 z2 = true <-> z1 = z2.
Proof. apply Z.eqb_eq. Qed.

(*Equality corresponds to Leibnitz equality*)
Lemma zero_spec: to_Z zero = 0.
Proof. reflexivity. Qed.

Lemma one_spec: to_Z one = 1.
Proof. reflexivity. Qed.

Lemma succ_spec z: to_Z (succ z) = Z.succ (to_Z z).
Proof. reflexivity. Qed.

Lemma pred_spec z: to_Z (pred z) = Z.pred (to_Z z).
Proof. reflexivity. Qed.

Lemma add_spec z1 z2: to_Z (add z1 z2) = to_Z z1 + to_Z z2.
Proof. reflexivity. Qed.

Lemma sub_spec z1 z2: to_Z (sub z1 z2) = to_Z z1 - to_Z z2.
Proof. reflexivity. Qed.

Lemma mul_spec z1 z2: to_Z (mul z1 z2) = to_Z z1 * to_Z z2.
Proof. reflexivity. Qed.

Lemma eqb_spec z1 z2: eqb z1 z2 = Z.eqb (to_Z z1) (to_Z z2).
Proof. reflexivity. Qed.

Lemma lt_spec z1 z2: lt z1 z2 = Z.ltb (to_Z z1) (to_Z z2).
Proof. reflexivity. Qed.
