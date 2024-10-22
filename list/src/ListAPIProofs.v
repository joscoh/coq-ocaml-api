Require Import Coq.ZArith.BinInt.
(*Simple proofs about functions in List API*)
From ListAPI Require Import ListAPI.

(*Proofs with ints*)

(*Proofs with exceptions*)



Require Import Lia.
(*A proof about [length]*)
Lemma length_aux_correct {A: Type} (len: CoqInt.int) (l: list A):
  (CoqInt.to_Z len + Z.of_nat (List.length l) < CoqInt.Int31.max_signed)%Z ->
  CoqInt.to_Z (length_aux len l) = 
    ((CoqInt.to_Z len) + Z.of_nat (List.length l))%Z.
Proof.
  revert len. induction l as [| h t IH]; intros len Hbound.
  - simpl; lia.
  - revert Hbound. simpl length_aux. simpl List.length.
    rewrite Znat.Nat2Z.inj_succ; intros Hbound. 
    rewrite IH; rewrite CoqInt.to_Z_succ; lia.
Qed.

Lemma length_correct {A: Type} (l: list A):
  (Z.of_nat (List.length l) < CoqInt.Int31.max_signed)%Z ->
  CoqInt.to_Z (length l) = Z.of_nat (List.length l).
Proof.
  intros Hbound.
  unfold length.
  rewrite length_aux_correct; auto.
Qed.