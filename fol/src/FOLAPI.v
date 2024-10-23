Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

(*Every term variable has type int*)

(*Variables*)
Definition var : Set := string.

(*Terms*)
Unset Elimination Schemes.
Inductive tm := 
| Tconst: Z -> tm
| Tvar: var -> tm
| Tadd: tm -> tm -> tm
| Tmult: tm -> tm -> tm
| Tlet: tm -> (var * tm) -> tm.

(*Boolean operators*)
Variant binop :=
| And | Or | Implies | Iff.

(*Quantifier*)
Variant quant :=
| Forall | Exists.

(*Formulas*)
Inductive fmla :=
| Feq: tm -> tm -> fmla
| Flt: tm -> tm -> fmla
| Fbinop: binop -> fmla -> fmla -> fmla
| Fnot: fmla -> fmla
| Fforall: (var * fmla) -> fmla
| Fexists: (var * fmla) -> fmla.

Definition tm_bound : Set := var * tm.
Definition fmla_bound : Set := var * fmla.
Set Elimination Schemes.

(*Induction Principles*)
Section TermInd.
Variable (P: tm -> Prop) 
(Pconst: forall c, P (Tconst c))
(Pvar: forall v, P (Tvar v))
(Padd: forall t1 t2, P t1 -> P t2 -> P (Tadd t1 t2))
(Pmult: forall t1 t2, P t1 -> P t2 -> P (Tmult t1 t2))
(Plet: forall t1 b, P t1 -> P (snd b) -> P (Tlet t1 b)).

Fixpoint tm_ind (t: tm) : P t :=
  match t with
  | Tconst c => Pconst c
  | Tvar v => Pvar v
  | Tadd t1 t2 => Padd _ _ (tm_ind t1) (tm_ind t2)
  | Tmult t1 t2 => Pmult _ _ (tm_ind t1) (tm_ind t2)
  | Tlet t1 (v, t2) => Plet _ (v, t2) (tm_ind t1) (tm_ind t2)
  end.
End TermInd.

Section FmlaInd.
Variable (P: fmla -> Prop)
(Peq: forall t1 t2, P (Feq t1 t2))
(Plt: forall t1 t2, P (Flt t1 t2))
(Pbinop: forall b f1 f2, P f1 -> P f2 -> P (Fbinop b f1 f2))
(Pnot: forall f, P f -> P (Fnot f))
(Pforall: forall b, P (snd b) -> P (Fforall b))
(Pexists: forall b, P (snd b) -> P (Fexists b)).

Fixpoint fmla_ind (f: fmla) : P f :=
  match f with
  | Feq t1 t2 => Peq t1 t2
  | Flt t1 t2 => Plt t1 t2
  | Fbinop b f1 f2 => Pbinop b _ _ (fmla_ind f1) (fmla_ind f2)
  | Fnot f => Pnot _ (fmla_ind f)
  | Fforall (v, f) => Pforall (v, f) (fmla_ind f)
  | Fexists (v, f) => Pexists (v, f) (fmla_ind f)
  end.

End FmlaInd.

(*TODO: Equality*)

(*Semantics*)

(*Variable valuation*)
Definition val := var -> Z.
Definition add_val (x: var) (z: Z) (v: val) : val :=
  fun y => if string_dec x y then z else v y.

Lemma add_val_twice (x : var) (z1 z2: Z) (v: val):
forall p,
  add_val x z1 (add_val x z2 v) p = add_val x z1 v p.
Proof.
  intros p. unfold add_val. destruct (string_dec x p); subst; auto.
Qed.

Lemma add_val_switch (x y : var) (z1 z2: Z) (v: val):
  x <> y ->
  forall p,
  add_val x z1 (add_val y z2 v) p = add_val y z2 (add_val x z1 v) p.
Proof.
  intros Hxy p. unfold add_val.
  destruct (string_dec x p); subst; auto.
  destruct (string_dec y p); subst; auto.
  contradiction.
Qed.

Fixpoint tm_rep (v: val) (t: tm) : Z :=
  match t with
  | Tvar x => v x
  | Tadd t1 t2 => (tm_rep v t1) + (tm_rep v t2)
  | Tmult t1 t2 => (tm_rep v t1) * (tm_rep v t2)
  | Tconst c => c
  | Tlet t1 (x, t2) => tm_rep (add_val x (tm_rep v t1) v) t2
  end.

Definition binop_rep (b: binop) : Prop -> Prop -> Prop :=
  match b with
  | And => and
  | Or => or
  | Implies => fun x y => x -> y
  | Iff => fun x y => x <-> y
  end.

Fixpoint fmla_rep (v: val) (f: fmla) : Prop :=
  match f with
  | Feq t1 t2 => (tm_rep v t1) = (tm_rep v t2)
  | Flt t1 t2 => (tm_rep v t1) < (tm_rep v t2)
  | Fbinop b f1 f2 => binop_rep b (fmla_rep v f1) (fmla_rep v f2)
  | Fnot f => ~ (fmla_rep v f)
  | Fforall (x, f) => forall d, fmla_rep (add_val x d v) f
  | Fexists (x, f) => exists d, fmla_rep (add_val x d v) f
  end.

(*Safe binding traversal*)

(*First, unsafe substitutiuon*)
Fixpoint tm_subst_unsafe (v: var) (t: tm) (t1: tm) : tm :=
  match t1 with
  | Tvar x => if string_dec v x then t else t1
  | Tconst c => Tconst c
  | Tadd t1 t2 => Tadd (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Tmult t1 t2 => Tmult (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Tlet t1 (y, t2) => Tlet (tm_subst_unsafe v t t1) 
    (y, (if string_dec v y then t2 else tm_subst_unsafe v t t2))
  end.
Fixpoint fmla_subst_unsafe (v: var) (t: tm) (f: fmla) : fmla :=
  match f with
  | Feq t1 t2 => Feq (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Flt t1 t2 => Flt (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Fbinop b f1 f2 => Fbinop b (fmla_subst_unsafe v t f1) (fmla_subst_unsafe v t f2)
  | Fnot f => Fnot (fmla_subst_unsafe v t f)
  | Fforall (x, f) => 
    Fforall (x, if string_dec v x then f else fmla_subst_unsafe v t f)
  | Fexists (x, f) => 
    Fexists (x, if string_dec v x then f else fmla_subst_unsafe v t f)
  end.

(*Free variables*)
Fixpoint tm_fv (t: tm) : list var :=
  match t with
  | Tvar x => [x]
  | Tconst _ => nil
  | Tadd t1 t2 => tm_fv t1 ++ tm_fv t2
  | Tmult t1 t2 => tm_fv t1 ++ tm_fv t2
  | Tlet t1 (x, t2) => tm_fv t1 ++ (remove string_dec x (tm_fv t2))
  end.
Fixpoint fmla_fv (f: fmla) : list var :=
  match f with
  | Feq t1 t2 => tm_fv t1 ++ tm_fv t2
  | Flt t1 t2 => tm_fv t1 ++ tm_fv t2
  | Fbinop _ f1 f2 => fmla_fv f1 ++ fmla_fv f2
  | Fnot f => fmla_fv f
  | Fforall (x, f) => remove string_dec x (fmla_fv f)
  | Fexists (x, f) => remove string_dec x (fmla_fv f)
  end.


(*Semantics for unsafe substitution*)

(*Valuations that agree on free vars are equivalent*)
Lemma tm_rep_change_vv (t: tm):
  forall (vv1 vv2: val) (Hvv: forall x, In x (tm_fv t) -> vv1 x = vv2 x),
  tm_rep vv1 t = tm_rep vv2 t.
Proof.
  induction t as [| | t1 t2 IH1 IH2 | t1 t2 IH1 IH2 | t1 [x t2] IH1 IH2]; simpl; auto;
  intros vv1 vv2 Hvv; try (setoid_rewrite in_app_iff in Hvv);
  rewrite (IH1 vv1 vv2); auto; try solve[f_equal; auto].
  apply IH2; simpl. intros y Hiny.
  unfold add_val. destruct (string_dec x y); subst; auto.
  apply Hvv. right. apply in_in_remove; auto.
Qed.

Lemma binop_rep_congr (P1 P2 P3 P4: Prop) b:
  P1 <-> P2 ->
  P3 <-> P4 ->
  binop_rep b P1 P3 <-> binop_rep b P2 P4.
Proof.
  intros Hiff1 Hiff2. destruct b; simpl; firstorder.
Qed.

Lemma fmla_rep_change_vv (f: fmla):
  forall (vv1 vv2: val) (Hvv: forall x, In x (fmla_fv f) -> vv1 x = vv2 x),
  fmla_rep vv1 f <-> fmla_rep vv2 f.
Proof.
  induction f as [ t1 t2 | t1 t2 | | ? IH | [x f] IH | [x f] IH] ; simpl; auto; intros vv1 vv2 Hvv;
  try (setoid_rewrite in_app_iff in Hvv);
  (*first 2 cases*)
  try solve[rewrite (tm_rep_change_vv t1 vv1 vv2) by auto;
    rewrite (tm_rep_change_vv t2 vv1 vv2) by auto;
    reflexivity];
  (*last 2 cases*)
  try solve[setoid_rewrite IH; [reflexivity | |]; auto; simpl;
    intros y Hiny; unfold add_val; destruct (string_dec x y); subst; auto;
    symmetry; apply Hvv, in_in_remove; auto].
  apply binop_rep_congr; auto.
Qed.

(*TODO START: define tm_bnd*)
Lemma tm_subst_unsafe_rep (v: var) (t: tm) (t1: tm) :
  (forall x, In x (tm_fv t) -> ~ In x (tm_bnd t1)) ->
  forall (vv: val), tm_rep vv (tm_subst_unsafe v t t1) =
  tm_rep (add_val v (tm_rep vv t) vv) t1.
Proof.
  induction t1 as [| x | | | t1 [x t2] IH1 IH2]; simpl; auto; intros vv;
  try solve[f_equal; auto].
  - (*var*) unfold add_val. destruct (string_dec v x); auto.
  - (*let*) rewrite <- IH1.
    destruct (string_dec v x); subst; auto.
    + apply tm_rep_change_vv. intros y Hy.
      unfold add_val. destruct (string_dec x y); auto.
    + simpl in IH2.
      rewrite IH2.
      apply tm_rep_change_vv.
      intros y Hiny.
      unfold add_val at 1 3 4 5.
      destruct (string_dec v y); subst; auto.
      destruct (string_dec x y); subst; auto; [contradiction|].

      erewrite tm_rep_change_vv.
      2: { intros y1 Hiny1. apply add }


      symmetry. erewrite tm_rep_change_vv.
      2: { intros y Hy. apply add_val_switch. auto. }
      change (fun y => add_val v (tm_rep vv t)
        (add_val x (tm_rep vv (tm_subst_unsafe v t t1)) vv) y) with 
        (add_val v (tm_rep vv t)
        (add_val x (tm_rep vv (tm_subst_unsafe v t t1)) vv)).
      rewrite <- (IH2 (add_val x (tm_rep vv (tm_subst_unsafe v t t1)) vv)).
      rewrite <- IH2.
      simpl.

      rewrite add_val_switch.
    
     rewrite IH2. apply tm_rep_change_vv. intros y Hy.
      rewrite add_val_twice.
      rewrite add_val_switch.
      unfold add_val. destruct (string_dec v y); subst; auto.
      destruct (string_dec x y); subst; auto.
      * apply tm_rep_change_vv.
  
   apply IH2.
  
  
   f_equal; auto. 
    + unfold add_val. destruct (string_dec v v); auto. contradiction.
    + unfold add_val.

(*TODO: implement open, close binders*)

(*Alpha equivalence*)

