Require Import Coq.ZArith.BinInt.
Require Import Lia.
Require Import Coq.Lists.List.
From CoqCompat Require Import Monads.
From ListAPI Require Import ListAPI.

(*Simple proofs about functions in List API*)

(*Proofs with exceptions*)

(*hd and tl*)
Lemma hd_tl_eq {A: Type} (l: list A):
  l <> nil ->
  exists h t, hd l = err_ret h /\ tl l = err_ret t /\ l = h :: t.
Proof.
  intros Hnil. destruct l as [| h t]; [contradiction|].
  exists h. exists t. auto.
Qed.

(*Proofs with ints*)

(*length*)
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

(*Ints + exceptions*)

(*nth*)
Lemma nth_aux_correct {A: Type} (l: list A) (n: CoqInt.int):
  (0 <= CoqInt.to_Z n < Z.of_nat (List.length l))%Z ->
  exists a,
    nth_aux l n = err_ret a /\
    List.nth_error l (Z.to_nat (CoqInt.to_Z n)) = Some a.
Proof.
  revert n.
  induction l as [| h t IH]; intros n Hn; [simpl in *; lia|].
  simpl nth_aux.
  rewrite CoqInt.to_Z_eqb, CoqInt.to_Z_zero.
  destruct (Z.eqb_spec (CoqInt.to_Z n) 0).
  - exists h. split; auto. rewrite e. reflexivity.
  - specialize (IH (CoqInt.pred n)).
    rewrite CoqInt.to_Z_pred in IH; [| rewrite CoqInt.min31; lia].
    simpl List.length in Hn.
    specialize (IH (ltac:(lia))).
    destruct IH as [a [Hnthaux Hnth]].
    exists a. split; auto.
    rewrite Znat.Z2Nat.inj_pred in Hnth.
    destruct (Z.to_nat (CoqInt.to_Z n)) as [|n'] eqn : Hz; auto. 
    lia.
Qed.

Lemma nth_correct {A: Type} (l: list A) (n: CoqInt.int):
  (0 <= CoqInt.to_Z n < Z.of_nat (List.length l))%Z ->
  exists a,
    nth l n = err_ret a /\
    List.nth_error l (Z.to_nat (CoqInt.to_Z n)) = Some a.
Proof.
  intros Hz.
  unfold nth.
  rewrite CoqInt.to_Z_lt, CoqInt.to_Z_zero.
  destruct (Z.ltb_spec (CoqInt.to_Z n) 0); try lia.
  apply nth_aux_correct; assumption.
Qed.