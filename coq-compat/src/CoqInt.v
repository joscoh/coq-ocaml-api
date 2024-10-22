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
Definition eqb := Int31.eq.
Definition zero := Int31.zero.
Definition one := Int31.one.
Definition succ (i: int) : int := Int31.add one i.


(*For proofs, should never be used in extracted code*)
(*Define our own functions; clients should not need to know CompCert ints*)
(*OCaml uses signed ints*)
Definition to_Z (i: int) : Z := Int31.signed i.
Definition of_Z (z: Z) : int := Int31.repr z.

Require Import Lia.
(* Require Import Coq.NArith.BinNat. *)

(*Signed ints: need assumption; cannot have overflow*)
Lemma to_Z_succ (i: int): 
  (to_Z i < Int31.max_signed)%Z ->
  to_Z (succ i) = Z.succ (to_Z i).
Proof.
  intros Hbound. unfold succ, to_Z, one in *.
  rewrite Int31.add_signed.
  rewrite Int31.signed_one by reflexivity.
  pose proof (Int31.signed_range i).
  rewrite Int31.signed_repr; lia.
Qed.
(* Require Import Integer.

Definition int : Type := int63.
Definition int_eqb : int -> int -> bool := int63_eqb.
(*NOTE: this is an axiom for OCaml*)
(*TODO: better way of identifying axioms*)
Definition int_eqb_eq : forall (i1 i2: int), i1 = i2 <-> int_eqb i1 i2 = true :=
  int63_eqb_eq.

Definition zero : int := int63_of_Z 0%Z eq_refl.
Definition one : int := int63_of_Z 1%Z eq_refl.
Definition two : int := int63_of_Z 2%Z eq_refl.
Definition five : int := int63_of_Z 5%Z eq_refl.
Definition neg_one : int := int63_of_Z (-1)%Z eq_refl.
Definition is_zero (i: int) : bool := int_eqb i zero.

Definition compare_to_int (c: comparison) : int :=
  match c with
  | Eq => zero
  | Lt => neg_one
  | Gt => one
  end.

Definition compare (i1 i2: int) : int := 
  compare_to_int (int63_compare i1 i2).


(*Add these as axioms: the Coq code never calls them*)
Axiom add : int -> int -> int.
Axiom mult: int -> int -> int.
(*TODO: switch to Compcert ints*)
Axiom ge : int -> int -> bool. *)