(*A light axiomatization/implementation of OCaml's ints.
  We implement using Coq bounded ints but extract to
  OCaml int. See comment in CoqBigInt.t*)
Require Import Coq.ZArith.BinInt.
From compcert Require Import lib.Integers.
Require Coq.Init.Nat.

(*We need 31-bit ints*)
Module Wordsize_31.
  Definition wordsize := 31%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
Proof. discriminate. Qed.
End Wordsize_31.
Module Int31 := Make(Wordsize_31).

Definition int := Int31.int.
Definition zero := Int31.zero.
Definition one := Int31.one.
Definition succ (i: int) : int := Int31.add one i.
Definition pred (i: int) : int := Int31.sub i one.
Definition add (i1 i2: int) : int := Int31.add i1 i2.
Definition sub (i1 i2: int) : int := Int31.sub i1 i2.
Definition mul (i1 i2: int) : int := Int31.mul i1 i2.
Definition eqb := Int31.eq.
Definition lt := Int31.lt.

(*For proofs, should never be used in extracted code*)
(*Define our own functions; clients should not need to know CompCert ints*)
(*OCaml uses signed ints*)
Definition to_Z (i: int) : Z := Int31.signed i.
Definition of_Z (z: Z) : int := Int31.repr z.

Require Import Lia.

Lemma to_Z_zero: to_Z zero = 0%Z.
Proof. reflexivity. Qed.

Lemma to_Z_one: to_Z one = 1%Z.
Proof. reflexivity. Qed.

(*Signed ints: need assumption; cannot have overflow*)
Lemma to_Z_add (i1 i2: int):
  (Int31.min_signed <= to_Z i1 + to_Z i2 <= Int31.max_signed)%Z ->
  to_Z (add i1 i2) = Z.add (to_Z i1) (to_Z i2).
Proof.
  intros Hbound. unfold add, to_Z in *.
  rewrite Int31.add_signed.
  rewrite Int31.signed_repr; lia.
Qed. 

Lemma to_Z_succ (i: int): 
  (to_Z i < Int31.max_signed)%Z ->
  to_Z (succ i) = Z.succ (to_Z i).
Proof.
  intros Hbound. unfold succ. rewrite to_Z_add; rewrite to_Z_one.
  - apply Z.add_1_l.
  - pose proof (Int31.signed_range i). unfold to_Z in *. lia.
Qed.

Lemma to_Z_sub (i1 i2: int):
  (Int31.min_signed <= to_Z i1 - to_Z i2 <= Int31.max_signed)%Z ->
  to_Z (sub i1 i2) = Z.sub (to_Z i1) (to_Z i2).
Proof.
  intros Hbound. unfold sub, to_Z in *.
  rewrite Int31.sub_signed, Int31.signed_repr; lia.
Qed.

Lemma to_Z_pred (i: int): 
  (Int31.min_signed < to_Z i)%Z ->
  to_Z (pred i) = Z.pred (to_Z i).
Proof.
  intros Hbound. unfold pred. rewrite to_Z_sub; rewrite to_Z_one.
  - apply Z.sub_1_r.
  - pose proof (Int31.signed_range i); unfold to_Z in *; lia.
Qed.

Lemma to_Z_lt (i1 i2: int):
  lt i1 i2 = Z.ltb (to_Z i1) (to_Z i2).
Proof.
  unfold lt, to_Z.
  unfold Int31.lt.
  destruct (Z.ltb_spec (Int31.signed i1) (Int31.signed i2));
  destruct (Coqlib.zlt _ _); auto; try contradiction. lia.
Qed.

Lemma to_Z_eqb i1 i2: 
  eqb i1 i2 = Z.eqb (to_Z i1) (to_Z i2).
Proof.
  unfold eqb, to_Z. rewrite Int31.signed_eq.
  destruct (Z.eqb_spec (Int31.signed i1) (Int31.signed i2));
  destruct (Coqlib.zeq _ _); auto; contradiction.
Qed.

(*Useful in proofs*)
Lemma min31 : Int31.min_signed = (- 1073741824)%Z.
Proof. reflexivity. Qed.

Lemma max31 : Int31.max_signed = 1073741823%Z.
Proof. reflexivity. Qed.
