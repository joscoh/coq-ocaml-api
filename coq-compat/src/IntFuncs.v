(*Functions that operate on [CoqBigInt.t]. They must
  ONLY use definitions/lemmas from that file. They cannot
  refer to the fact that the type is secretly Z underneath*)
From CoqCompat Require CoqBigInt CoqInt.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Export Lia.

Local Open Scope Z_scope.

Fixpoint int_length {A: Type} (l: list A) : CoqBigInt.t :=
  match l with
  | nil => CoqBigInt.zero
  | _ :: t => CoqBigInt.succ (int_length t)
  end. 

Lemma int_length_nonneg {A: Type} (l: list A) :
  0 <= CoqBigInt.to_Z (int_length l).
Proof.
  induction l; simpl.
  - rewrite CoqBigInt.zero_spec. lia.
  - rewrite CoqBigInt.succ_spec. lia.
Qed.

Lemma int_length_spec {A: Type} (l: list A) : 
  Z.to_nat (CoqBigInt.to_Z (int_length l)) = List.length l.
Proof.
  induction l; simpl int_length.
  - rewrite CoqBigInt.zero_spec. reflexivity.
  - rewrite CoqBigInt.succ_spec.
    rewrite Znat.Z2Nat.inj_succ.
    + rewrite IHl; reflexivity.
    + apply int_length_nonneg.
Qed. 

Lemma Z2Nat_eqb_nat (z1 z2: Z):
  0 <= z1 ->
  0 <= z2 ->
  Nat.eqb (Z.to_nat z1) (Z.to_nat z2) = Z.eqb z1 z2.
Proof.
  intros Hz1 Hz2.
  destruct (Z.eqb_spec z1 z2); subst; simpl.
  - apply PeanoNat.Nat.eqb_refl.
  - destruct (PeanoNat.Nat.eqb_spec (Z.to_nat z1) (Z.to_nat z2));
    auto.
    apply Znat.Z2Nat.inj_iff in e; auto. contradiction.
Qed.
    
(*A corollary*)
Lemma int_length_eq {A: Type} (l1 l2: list A):
  CoqBigInt.eqb (int_length l1) (int_length l2) =
  Nat.eqb (length l1) (length l2).
Proof.
  rewrite CoqBigInt.eqb_spec.
  rewrite <- Z2Nat_eqb_nat; try solve[apply int_length_nonneg].
  rewrite !int_length_spec. reflexivity.
Qed.

(*Recursive Functions over BigInts*)

(*We want to write several functions that are recursive over
  integers, either because that is the function we want
  (i.e. nth) or because we need fuel for non-structural functions.
  We can do this by inducting on the accessibility proof of the lt
  relation (resulting in good OCaml code as documented in
  "Well Founded Recursion Done Right"). Here we do it
  generically so that we don't need the boilerplate for
  every such function (at the cost of having to write some
  functions a bit unnaturally).
  Although we do this completely generically, the OCaml functions
  do not have Obj.magic (a dependent case is likely different)*)

Lemma int_wf_lemma z : CoqBigInt.eqb z CoqBigInt.zero = false -> 
  CoqBigInt.lt z CoqBigInt.zero = false ->
  (Z.to_nat (CoqBigInt.to_Z (CoqBigInt.pred z)) 
  < Z.to_nat (CoqBigInt.to_Z z))%nat.
Proof.
  intros Hneq Hlt.
  rewrite CoqBigInt.pred_spec, Znat.Z2Nat.inj_pred.
  apply PeanoNat.Nat.lt_pred_l.
  rewrite CoqBigInt.eqb_spec in Hneq.
  rewrite <- Z2Nat_eqb_nat in Hneq.
  - rewrite CoqBigInt.zero_spec in Hneq; simpl in Hneq.
    apply EqNat.beq_nat_false_stt in Hneq; exact Hneq.
  - rewrite CoqBigInt.lt_spec, Z.ltb_ge, CoqBigInt.zero_spec in Hlt.
    exact Hlt.
  - rewrite CoqBigInt.zero_spec. apply Z.le_refl.
Qed.

Section IntFunc.
 Context {P: CoqBigInt.t -> Type} 
  (neg_case: forall z, CoqBigInt.lt z CoqBigInt.zero = true -> P z)
  (zero_case: P CoqBigInt.zero)
  (ind_case: forall z, CoqBigInt.eqb z CoqBigInt.zero = false ->
    CoqBigInt.lt z CoqBigInt.zero = false ->
    P (CoqBigInt.pred z) -> P z).

Lemma zero_lemma z : CoqBigInt.eqb z CoqBigInt.zero = true ->
  z = CoqBigInt.zero.
Proof.
rewrite CoqBigInt.eqb_eq. auto.
Qed.

(*The Fixpoint*)
Fixpoint int_rect_aux (z: CoqBigInt.t) 
  (ACC: Acc lt (Z.to_nat z)) {struct ACC} : P z :=
  match CoqBigInt.lt z CoqBigInt.zero as b return
  CoqBigInt.lt z CoqBigInt.zero = b -> P z with
  | true => fun Hlt => neg_case _ Hlt
  | false => fun Hlt =>
    match CoqBigInt.eqb z CoqBigInt.zero as b return
      CoqBigInt.eqb z CoqBigInt.zero = b -> P z with
    | true => fun Heq => eq_rect _ P zero_case _ (eq_sym (zero_lemma _ Heq))
    | false => fun Hneq => 
      ind_case _ Hneq Hlt (int_rect_aux (CoqBigInt.pred z) 
        (Acc_inv ACC (int_wf_lemma _ Hneq Hlt)))
    end eq_refl
  end eq_refl.

Definition int_rect (z: CoqBigInt.t) : P z :=
  int_rect_aux z (Wf_nat.lt_wf _).

End IntFunc.

(*Examples:*)

(*Generate a list from 0 to n-1*)
Definition iota (z: CoqBigInt.t) : list CoqBigInt.t :=
  @int_rect (fun _ => list CoqBigInt.t)
  (*lt*)
  (fun _ _ => nil)
  (*zero*)
  nil
  (*body*)
  (fun z _ _ rec => z :: rec) z.

(*nth on lists, recursive on int*)
Definition big_nth {A: Type} (l: list A)  (z: CoqBigInt.t) : option A :=
  @int_rect (fun _ => list A -> option A)
  (*lt*)
  (fun _ _ _ => None)
  (*zero*)
  (fun l =>
    match l with
    | nil => None
    | x :: _ => Some x
    end)
  (*pos*)
  (fun _ _ _ rec l =>
    match l with
    | nil => None
    | _ :: t => rec t
    end) z l.
