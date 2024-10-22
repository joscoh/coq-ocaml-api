Require Import Coq.ZArith.BinInt.
From compcert.lib Require Import Integers.

Definition int := int.
Definition eqb := Int.eq.
Definition succ (i: int) : int := Int.add Int.one i.

(*For proofs, should never be used in extracted code*)
Definition to_nat (i: int) : nat := Z.to_nat (Int.unsigned i).

(* Lemma 

Search Int.eq.


Int.same_if_eq: forall x y : Integers.int, Int.eq x y = true -> x = y
Int.eq_false: forall x y : Integers.int, x <> y -> Int.eq x y = false




(*A (limited) formalization of machine-length integers*)
(*We could use CompCert's integers, but that is a pretty large
dependency. For now, we avoid*)
(*The main difference is that we use a boolean predicate
  for computation and proof irrelevance.
  Additionally, we are not concerned we signed/unsigned 
  representations.
  Really, we just want a bound. We don't use ints for much
  except comparisons in OCaml*)
Require Export Coq.ZArith.BinInt.
Require Export Common.
(* From Proofs Require Import core.Common. *)

Local Open Scope Z_scope.

Section BoundedInt.

Variable bound : Z. (*For Ocaml: 2 ^ 62*)

(*Use boolean *)
Record int := mk_int { int_val : Z; 
  int_bound: Z.leb (-bound) int_val && Z.ltb int_val bound}.

Definition eqb (i1 i2: int) : bool :=
  Z.eqb (int_val i1) (int_val i2).

Lemma eqb_spec (i1 i2: int): reflect (i1 = i2) (eqb i1 i2).
Proof.
  unfold eqb.
  destruct (Z.eqb_spec (int_val i1) (int_val i2));
  [apply ReflectT | apply ReflectF].
  - destruct i1 as [i1 b1]; destruct i2 as [i2 b2];
    simpl in *; subst.
    assert (b1 = b2) by apply bool_irrelevance;
    subst; reflexivity.
  - intro C; subst; contradiction.
Qed.

Lemma eqb_eq (i1 i2: int) : i1 = i2 <-> eqb i1 i2.
Proof.
  destruct (eqb_spec i1 i2); subst; split; auto;
  discriminate.
Qed.

Definition compare (i1 i2: int) : comparison :=
  Z.compare (int_val i1) (int_val i2).

End BoundedInt.

Definition ocaml_int_size := 2 ^ 62.

Definition int63 := int ocaml_int_size.
Definition int63_eqb := eqb ocaml_int_size.
Lemma int63_eqb_eq (i1 i2: int63) : i1 = i2 <-> int63_eqb i1 i2.
Proof. apply eqb_eq. Qed.

Definition int63_of_Z (z: Z) (Hz: Z.leb (-ocaml_int_size) z && Z.ltb z ocaml_int_size) : int63 :=
  mk_int _ z Hz.
Definition int63_to_Z (i: int63) : Z := int_val _ i.

Definition int63_compare := compare ocaml_int_size. *)