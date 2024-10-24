Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.
From CoqCompat Require CoqBigInt.
From CoqCompat Require Import Monads CoqCtr.

(*Every term variable has type int*)

(*Variables*)
Definition var : Set := (string * CoqBigInt.t)%type.

Definition var_eqb (v1 v2: var) : bool :=
  (*Compare tags first*)
  CoqBigInt.eqb (snd v1) (snd v2) &&
  String.eqb (fst v1) (fst v2).

(*Want in [Prop], not [reflect]*)
Lemma var_eqb_eq v1 v2: var_eqb v1 v2 = true <-> v1 = v2.
Proof.
  unfold var_eqb. rewrite andb_true_iff, CoqBigInt.eqb_eq, String.eqb_eq.
  destruct v1 as [s1 i1]; destruct v2 as [s2 i2]; simpl; split;
  intros Heq; inversion Heq; subst; auto.
Qed.

Definition var_dec (v1 v2: var) : {v1 = v2} + {v1 <> v2}.
Proof.
  destruct (var_eqb v1 v2) eqn : Hvar.
  - left. apply var_eqb_eq in Hvar; auto.
  - right. intro Hc. subst. 
    assert (Hvar2: var_eqb v2 v2 = true) by (apply var_eqb_eq; auto).
    rewrite Hvar in Hvar2. discriminate.
Defined.

(*Terms*)
Unset Elimination Schemes.

Variant intop := | Add | Mult.

Inductive tm := 
| Tconst: Z -> tm
| Tvar: var -> tm
| Top: intop -> tm -> tm -> tm
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
(Pop: forall o t1 t2, P t1 -> P t2 -> P (Top o t1 t2))
(Plet: forall t1 b, P t1 -> P (snd b) -> P (Tlet t1 b)).

Fixpoint tm_ind (t: tm) : P t :=
  match t with
  | Tconst c => Pconst c
  | Tvar v => Pvar v
  | Top o t1 t2 => Pop o _ _ (tm_ind t1) (tm_ind t2)
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
  fun y => if var_dec x y then z else v y.

Lemma add_val_twice (x : var) (z1 z2: Z) (v: val):
forall p,
  add_val x z1 (add_val x z2 v) p = add_val x z1 v p.
Proof.
  intros p. unfold add_val. destruct (var_dec x p); subst; auto.
Qed.

Lemma add_val_switch (x y : var) (z1 z2: Z) (v: val):
  x <> y ->
  forall p,
  add_val x z1 (add_val y z2 v) p = add_val y z2 (add_val x z1 v) p.
Proof.
  intros Hxy p. unfold add_val.
  destruct (var_dec x p); subst; auto.
  destruct (var_dec y p); subst; auto.
  contradiction.
Qed.

Definition intop_rep (o: intop) : Z -> Z -> Z :=
  match o with
  | Add => Z.add
  | Mult => Z.mul
  end.

Fixpoint tm_rep (v: val) (t: tm) : Z :=
  match t with
  | Tvar x => v x
  | Top o t1 t2 => intop_rep o (tm_rep v t1) (tm_rep v t2)
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
  | Tvar x => if var_dec v x then t else t1
  | Tconst c => Tconst c
  | Top o t1 t2 => Top o (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Tlet t1 (y, t2) => Tlet (tm_subst_unsafe v t t1) 
    (y, (if var_dec v y then t2 else tm_subst_unsafe v t t2))
  end.
Fixpoint fmla_subst_unsafe (v: var) (t: tm) (f: fmla) : fmla :=
  match f with
  | Feq t1 t2 => Feq (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Flt t1 t2 => Flt (tm_subst_unsafe v t t1) (tm_subst_unsafe v t t2)
  | Fbinop b f1 f2 => Fbinop b (fmla_subst_unsafe v t f1) (fmla_subst_unsafe v t f2)
  | Fnot f => Fnot (fmla_subst_unsafe v t f)
  | Fforall (x, f) => 
    Fforall (x, if var_dec v x then f else fmla_subst_unsafe v t f)
  | Fexists (x, f) => 
    Fexists (x, if var_dec v x then f else fmla_subst_unsafe v t f)
  end.

(*Free variables*)
Fixpoint tm_fv (t: tm) : list var :=
  match t with
  | Tvar x => [x]
  | Tconst _ => nil
  | Top _ t1 t2 => tm_fv t1 ++ tm_fv t2
  | Tlet t1 (x, t2) => tm_fv t1 ++ (remove var_dec x (tm_fv t2))
  end.
Fixpoint fmla_fv (f: fmla) : list var :=
  match f with
  | Feq t1 t2 => tm_fv t1 ++ tm_fv t2
  | Flt t1 t2 => tm_fv t1 ++ tm_fv t2
  | Fbinop _ f1 f2 => fmla_fv f1 ++ fmla_fv f2
  | Fnot f => fmla_fv f
  | Fforall (x, f) => remove var_dec x (fmla_fv f)
  | Fexists (x, f) => remove var_dec x (fmla_fv f)
  end.

(*Bound variables*)
Fixpoint tm_bnd (t: tm) : list var :=
  match t with
  | Tlet t1 (x, t2) => x :: (tm_bnd t1) ++ (tm_bnd t2)
  | Top _ t1 t2 => tm_bnd t1 ++ tm_bnd t2
  | _ => nil
  end.
Fixpoint fmla_bnd (f: fmla) : list var :=
  match f with
  | Feq t1 t2 => tm_bnd t1 ++ tm_bnd t2
  | Flt t1 t2 => tm_bnd t1 ++ tm_bnd t2
  | Fbinop _ f1 f2 => fmla_bnd f1 ++ fmla_bnd f2
  | Fnot f => fmla_bnd f
  | Fforall (x, f) => x :: fmla_bnd f
  | Fexists (x, f) => x :: fmla_bnd f
  end.

(*Semantics for unsafe substitution*)

(*Valuations that agree on free vars are equivalent*)
Lemma tm_rep_change_vv (t: tm):
  forall (vv1 vv2: val) (Hvv: forall x, In x (tm_fv t) -> vv1 x = vv2 x),
  tm_rep vv1 t = tm_rep vv2 t.
Proof.
  induction t as [| | o t1 t2 IH1 IH2 | t1 [x t2] IH1 IH2]; simpl; auto;
  intros vv1 vv2 Hvv; try (setoid_rewrite in_app_iff in Hvv);
  rewrite (IH1 vv1 vv2); auto; try solve[f_equal; auto].
  apply IH2; simpl. intros y Hiny.
  unfold add_val. destruct (var_dec x y); subst; auto.
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
    intros y Hiny; unfold add_val; destruct (var_dec x y); subst; auto;
    symmetry; apply Hvv, in_in_remove; auto].
  apply binop_rep_congr; auto.
Qed.

Lemma tm_subst_unsafe_rep (v: var) (t: tm) (t1: tm) :
  (*Ensure no capture: no variable free in t can be bound in t1*)
  (forall x, In x (tm_fv t) -> In x (tm_bnd t1) -> False) ->
  forall (vv: val), tm_rep vv (tm_subst_unsafe v t t1) =
  tm_rep (add_val v (tm_rep vv t) vv) t1.
Proof.
  induction t1 as [| x | o t1 t2 IH1 IH2 | t1 [x t2] IH1 IH2]; simpl; auto; intros Hbnd vv;
  try solve[setoid_rewrite in_app_iff in Hbnd; f_equal; eauto].
  - (*var*) unfold add_val. destruct (var_dec v x); auto.
  - (*let*) setoid_rewrite in_app_iff in Hbnd. rewrite <- IH1 by eauto.
    destruct (var_dec v x); subst; auto.
    + apply tm_rep_change_vv. intros y Hy.
      unfold add_val. destruct (var_dec x y); auto.
    + simpl in IH2.
      rewrite IH2 by eauto.
      apply tm_rep_change_vv.
      intros y Hiny.
      unfold add_val at 1 3 4 5.
      destruct (var_dec v y); subst; auto.
      destruct (var_dec x y); subst; auto; [contradiction|].
      apply tm_rep_change_vv.
      intros z Hinz. unfold add_val.
      destruct (var_dec x z); subst; auto.
      (*Here, get contradiction with bound*)
      exfalso. apply (Hbnd z); auto.
Qed.

Lemma fmla_subst_unsafe_rep (v: var) (t: tm) (f: fmla) :
  (*Ensure no capture: no variable free in t can be bound in t1*)
  (forall x, In x (tm_fv t) -> In x (fmla_bnd f) -> False) ->
  forall (vv: val), fmla_rep vv (fmla_subst_unsafe v t f) <->
  fmla_rep (add_val v (tm_rep vv t) vv) f.
Proof.
  induction f as [| | | f IH | [x f] IH | [x f] IH]; simpl; auto; intros Hbnd vv; try setoid_rewrite in_app_iff in Hbnd;
  try solve[rewrite !tm_subst_unsafe_rep by eauto; reflexivity].
  - apply binop_rep_congr; eauto.
  - rewrite IH by eauto; reflexivity.
  - destruct (var_dec v x); subst.
    + setoid_rewrite fmla_rep_change_vv. reflexivity.
      2: intros y Hiny; rewrite add_val_twice; reflexivity.
      auto.
    + setoid_rewrite IH; eauto.
      simpl. setoid_rewrite fmla_rep_change_vv. reflexivity.
      1: intros y Hiny; reflexivity.
      intros y Hiny. unfold add_val at 1 2 3 5.
      destruct (var_dec x y); subst; auto;
      destruct (var_dec v y); subst; auto; try contradiction.
      apply tm_rep_change_vv.
      intros z Hinz. unfold add_val. destruct (var_dec x z); subst; auto. 
      exfalso. apply (Hbnd z); auto.
  - destruct (var_dec v x); subst.
    + setoid_rewrite fmla_rep_change_vv. reflexivity.
      2: intros y Hiny; rewrite add_val_twice; reflexivity.
      auto.
    + setoid_rewrite IH; eauto.
      simpl. setoid_rewrite fmla_rep_change_vv. reflexivity.
      1: intros y Hiny; reflexivity.
      intros y Hiny. unfold add_val at 1 2 3 5.
      destruct (var_dec x y); subst; auto;
      destruct (var_dec v y); subst; auto; try contradiction.
      apply tm_rep_change_vv.
      intros z Hinz. unfold add_val. destruct (var_dec x z); subst; auto. 
      exfalso. apply (Hbnd z); auto.
Qed.

(*Bindings and Variables*)

(*Idea: we have counter - all bindings and counters can ONLY
  be created through these functions*)
Module ZVal <: BigIntVal.
Definition val := CoqBigInt.zero.
End ZVal.

Module C := MakeCtr ZVal.

Import MonadNotations.
Local Open Scope state_scope.

Definition create_var (name: string) : ctr var :=
  _ <- C.incr tt ;;
  i <- C.get tt ;;
  st_ret (name, i).

Definition rename_var (v: var) : ctr var :=
  create_var (fst v).

(*Idea: in OCaml, these are opaque - ONLY way to construct bindings*)
Definition t_open_bound (b: tm_bound) : ctr (var * tm) :=
  let (v, t) := b in
  v1 <- rename_var v ;;
  st_ret (v1, tm_subst_unsafe v (Tvar v1) t).

Definition t_close_bound (v: var) (t: tm) : tm_bound :=
  (v, t).

Definition f_open_bound (b: fmla_bound) : ctr (var * fmla) :=
  let (v, f) := b in
  v1 <- rename_var v ;;
  st_ret (v1, fmla_subst_unsafe v (Tvar v1) f).

Definition f_close_bound (v: var) (f: fmla) : fmla_bound :=
  (v, f).

(* Type Safe API *)
Definition t_const (z: CoqBigInt.t) : tm := Tconst z.
Definition t_var (v: var) : tm := Tvar v.
Definition t_add (tm1 tm2: tm) : tm := Top Add tm1 tm2.
Definition t_mult (tm1 tm2: tm) : tm := Top Mult tm1 tm2.
Definition t_let (t1: tm) (b: tm_bound) : tm := Tlet t1 b.
Definition f_eq (tm1 tm2: tm) : fmla := Feq tm1 tm2.
Definition f_lt (tm1 tm2: tm) : fmla := Flt tm1 tm2.
Definition f_binop (b: binop) (f1 f2: fmla) : fmla := Fbinop b f1 f2.
Definition f_not (f: fmla) : fmla := Fnot f.
Definition f_forall (b: fmla_bound) : fmla := Fforall b.
Definition f_exists (b: fmla_bound) : fmla := Fexists b.

(*Because t_open_bound is no longer structurally recursive,
  we need a [size] metric*)
Fixpoint tm_size (t: tm) : nat :=
  match t with
  | Tconst _ => 1
  | Tvar _ => 1
  | Top _ t1 t2 => 1 + tm_size t1 + tm_size t2
  | Tlet t1 (x, t2) => 1 + tm_size t1 + tm_size t2
  end.

(*Substituting a variable for a variable does not change size*)
Lemma tm_subst_unsafe_var_size v1 v2 t:
  tm_size (tm_subst_unsafe v1 (Tvar v2) t) = tm_size t.
Proof.
  induction t as [| | | t1 [x t2] IH1 IH2]; simpl; auto.
  - destruct (var_dec _ _); reflexivity.
  - rewrite IH1. destruct (var_dec v1 x); auto.
Qed.  

(*Binding-safe traversal*)
From Equations Require Import Equations.
Require Import Lia.
(*Probably don't need but makes things much easier*)
Require Import Coq.Logic.FunctionalExtensionality.
Section SafeTraverse.
Local Obligation Tactic := simpl; try lia.

(* Lemma size_add1 t1 t2: (tm_size t1 < tm_size (Tadd t1 t2))%nat.
Proof. simpl; lia. Qed.
Lemma size_add2 t1 t2: (tm_size t2 < tm_size (Tadd t1 t2))%nat.
Proof. simpl; lia. Qed.
Lemma size_mult1 t1 t2: (tm_size t1 < tm_size (Tmult t1 t2))%nat.
Proof. simpl; lia. Qed.
Lemma size_mult2 t1 t2: (tm_size t2 < tm_size (Tmult t1 t2))%nat.
Proof. simpl; lia. Qed. *)

(*Express each case as function*)
(*For OCaml purposes, NOT dependently typed (but it would be
  easy to write an identical dependently typed version)*)
Variable (T: Type).
Variable (const_case: forall (c: Z), ctr T)
  (var_case: forall (x: var), ctr T)
  (op_case: forall (o: intop) (t1 t2: tm) (r1 r2: T), ctr T)
  (mult_case: forall (t1 t2: tm) (r1 r2: T), ctr T)
  (*NOTE: recursive case 2 on [t_open_bound] - b is the NEW variable*)
  (let_case: forall (t1: tm) (x: var) (t2: tm) (r1 r2: T), ctr T).

Equations tm_traverse (tm1: tm) : ctr T by wf (tm_size tm1) lt :=
  tm_traverse (Tconst c) := const_case c;
  tm_traverse (Tvar x) := var_case x;
  tm_traverse (Top o t1 t2) :=
    v1 <- tm_traverse t1 ;;
    v2 <- tm_traverse t2 ;;
    op_case o t1 t2 v1 v2;
  tm_traverse (Tlet t1 b) :=
    v1 <- tm_traverse t1 ;;
    (*Need dependent types here to have enough information for the proof*)
    st_bind_dep _ _ _ (t_open_bound b)
      (fun y s Heq => 
        v2 <- (tm_traverse (snd y)) ;;
        let_case t1 (fst y) (snd b) v1 v2).
Next Obligation.
intros t1 [v1 t2] _ _ y s Hy; subst.
simpl.
rewrite tm_subst_unsafe_var_size. lia.
Defined.
Next Obligation.
intros t1 b _; destruct b; simpl; lia.
Defined.
(* 
Fixpoint tm_traverse' (tm1: tm) (ACC: Acc lt (tm_size tm1)) {struct ACC} : ctr T.
Proof.
  destruct tm1 as [c | v | t1 t2 | t1 t2 | t1 b].
  - exact (const_case c).
  - exact (var_case v).
  - exact (r1 <- tm_traverse' t1 (Acc_inv ACC (size_add1 _ _)) ;;
    r2 <- tm_traverse' t2 (Acc_inv ACC (size_add2 _ _));;
    add_case t1 t2 r1 r2).
  - exact (r1 <- tm_traverse' t1 (Acc_inv ACC (size_mult1 _ _)) ;;
    r2 <- tm_traverse' t2 (Acc_inv ACC (size_mult2 _ _));;
    mult_case t1 t2 r1 r2).
  - refine (
     v1 <- tm_traverse' t1 (Acc_inv ACC _) ;;
    x <- t_open_bound b ;;
    v2 <- tm_traverse' (snd x) (Acc_inv ACC _) ;;
    let_case t1 (fst x) (snd b) v1 v2).
    Show Proof. *)

(*Now prove this equivalent to the non-dependent version*)
(*Use funext*)
Lemma tm_traverse_let (tm1: tm) (b: tm_bound) :
  tm_traverse (Tlet tm1 b) =
    v1 <- tm_traverse tm1 ;;
    x <- t_open_bound b ;;
    v2 <- tm_traverse (snd x) ;;
    let_case tm1 (fst x) (snd b) v1 v2.
Proof.
  simp tm_traverse. f_equal.
  apply functional_extensionality.
  unfold st_bind, st_bind_dep, bind, Monad_state. simpl. intros x.
  f_equal.
  apply functional_extensionality; intros i.
  destruct (runState (t_open_bound b)) eqn : Hr.
  reflexivity.
Qed.

(*TODO: do we need an induction principle?*)
End SafeTraverse.

(*Safe substitution*)
Definition sub_t  (v: var) (t: tm) (tm1: tm) : ctr tm :=
  tm_traverse tm 
    (fun c => st_ret (Tconst c))
    (fun x => st_ret (if var_dec v x then t else (Tvar x)))
    (fun o t1 t2 r1 r2 =>  st_ret (Top o r1 r2))
    (fun t1 x t2 r1 r2 => st_ret (Tlet r1 (x, r2))) tm1.

(*TODO: move*)

(*From Hoare State Monad paper*)
(*Instead of dependent types/Program, we have separate Prop*)
(*TODO: not polymorphic enough*)
Definition st_spec {A B: Type} (Pre: A -> Prop) (s: st A B)
  (Post: A -> B -> A -> Prop) : Prop :=
  forall i, Pre i -> Post i (fst (runState s i)) (snd (runState s i)).

Lemma st_spec_ret {A B: Type} (x: B):
  st_spec (fun _ => True) (st_ret x) (fun (s1: A) r s2 => s1 = s2 /\ r = x).
Proof.
  unfold st_spec; simpl; auto.
Qed.

Lemma st_spec_bind {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 (a: st St A) (b: A -> st St B):
  (st_spec P1 a Q1) ->
  (forall x, st_spec (P2 x) (b x) (Q2 x)) ->
  st_spec (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
    (st_bind b a) 
    (fun s1 y s3 => exists x s2, Q1 s1 x s2 /\ Q2 x s2 y s3).
Proof.
  unfold st_spec; simpl; intros Ha Hb i [Hi Himpl].
  exists (fst (runState a i)). exists (snd (runState a i)).
  split; auto.
  destruct (runState a i) as [v s] eqn : Hrun; simpl.
  apply Hb. apply Himpl. specialize (Ha _ Hi).
  rewrite Hrun in Ha; apply Ha.
Qed.

(*A weakening lemma*)
Lemma st_spec_weaken {A B: Type} (P1 P2: A -> Prop) (Q1 Q2: A -> B -> A -> Prop)
  (s: st A B):
  (forall i, P2 i -> P1 i) ->
  (forall i x f, Q1 i x f -> Q2 i x f) ->
  st_spec P1 s Q1 ->
  st_spec P2 s Q2.
Proof.
  unfold st_spec; intros; auto.
Qed.

Lemma st_spec_weaken_pre {A B: Type} (P1 P2: A -> Prop) Q
  (s: st A B):
  (forall i, P2 i -> P1 i) ->
  st_spec P1 s Q ->
  st_spec P2 s Q.
Proof.
  intros Hp.
  apply st_spec_weaken; auto.
Qed.

Lemma st_spec_weaken_post {A B: Type} (P: A -> Prop) 
  (Q1 Q2: A -> B -> A -> Prop)
  (s: st A B):
  (forall i x f, Q1 i x f -> Q2 i x f) ->
  st_spec P s Q1 ->
  st_spec P s Q2.
Proof.
  intros Hp.
  apply st_spec_weaken; auto.
Qed.
(*Much nicer for proofs*)
(*NOTE: st_spec_ret too weak (unlike paper) - we do in fact want
  to know that the precondition holds*)
Lemma prove_st_spec_ret {A B: Type} (P1 : A -> Prop) (Q1: A -> B -> A -> Prop) 
  (x: B):
  (forall i, P1 i -> Q1 i x i) ->
  st_spec P1 (st_ret x) Q1.
Proof.
  intros Hq.
  unfold st_spec, st_ret. simpl. auto.
Qed.

(*TODO: names should be consistent*)

Lemma prove_st_spec_bnd {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 Q3 (a: st St A) (b: A -> st St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (st_spec P1 a Q1) ->
  (forall x, st_spec (P2 x) (b x) (Q2 x)) ->
  (*Weaken head*)
  (forall i, P1 i -> (forall x s2, Q1 i x s2 -> P2 x s2)) ->
  (*Weaken rest*)
  (forall s1 s2 s3 x y, Q1 s1 x s2 -> Q2 x s2 y s3 -> Q3 s1 y s3) ->
  st_spec P1 (st_bind b a) Q3.
Proof.
  intros Ha Hb Hw1 Hw2. eapply st_spec_weaken.
  3: apply st_spec_bind. all: eauto; simpl.
  - intros i Hp. split; auto. apply Hw1. auto.
  - intros i x f [y [s [Hq1 Hq2]]]; eapply Hw2; eauto.
Qed.

(*Version that does not depend on initial state (i.e. Q2 does not depend on x)*)
(*If Q1 does not depend on initial state, then Q1 and P2 same*)
(*And if Q2 does not depend on initial state, then Q2 and Q3 same*)
Lemma prove_st_spec_bnd_nondep {St A B: Type} (P1 : St -> Prop)
  Q1 Q2 Q3 a (b: A -> st St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (st_spec P1 a (fun _ => Q1)) ->
  (forall x, st_spec (Q1 x) (b x) (fun _ => (Q2 x))) ->
  (*Weaken rest*)
  (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) ->
  st_spec P1 (st_bind b a) (fun _ => Q3).
Proof.
  intros Ha Hb Hw. eapply prove_st_spec_bnd; eauto.
  apply Hb. simpl. auto.
Qed.

Lemma st_spec_and {A B: Type} (P1 P2: A -> Prop) Q1 Q2 (o: st A B):
  st_spec P1 o Q1 ->
  st_spec P2 o Q2 ->
  st_spec (fun i => P1 i /\ P2 i) o (fun s1 r s2 => Q1 s1 r s2 /\ Q2 s1 r s2).
Proof.
  unfold st_spec. intros Hp1 Hp2 i [Hi1 Hi2]. auto.
Qed.

Lemma st_spec_get {A: Type} (P1: A -> Prop) (Q1: A -> A -> A -> Prop):
  (forall i, P1 i -> Q1 i i i) ->
  st_spec P1 (State.st_get) Q1.
Proof.
  intros Hpq. unfold st_spec; simpl. auto.
Qed.

Lemma st_spec_set {A: Type} (x: A) (P1: A -> Prop) (Q1: A -> unit -> A -> Prop):
  (forall i, P1 i -> Q1 i tt x) ->
  st_spec P1 (State.st_set x) Q1.
Proof.
  intros Hpq. unfold st_spec; simpl. auto.
Qed.

(*Prove dep bnd*)
Lemma prove_st_spec_dep_bnd {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 Q3 (a: st St A) (b: forall (b: A) (s: St), b = fst (runState a s) -> st St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (st_spec P1 a Q1) ->
  (forall x s Heq, st_spec (P2 x) (b x s Heq) (Q2 x)) ->
  (*Weaken head*)
  (forall i, P1 i -> (forall x s2, Q1 i x s2 -> P2 x s2)) ->
  (*Weaken rest*)
  (forall s1 s2 s3 x y, Q1 s1 x s2 -> Q2 x s2 y s3 -> Q3 s1 y s3) ->
  st_spec P1 (st_bind_dep _ _ _ a b) Q3.
Proof.
  (*Very, very tricky due to dependent types*)
  unfold st_spec; simpl. intros Ha Hb Hi Himpl i Hpi.
  generalize dependent (@eq_refl _ (fst (runState a i))).
  specialize (Hb (fst (runState a i)) i).
  generalize dependent (b (fst (runState a i)) i).
  intros b2 Hb2.
  specialize (Ha i).
  generalize dependent (runState a i).
  intros. eapply Himpl; eauto.
Qed.

(*And simpler version*)
Lemma prove_st_spec_dep_bnd_nondep {St A B: Type} (P1 : St -> Prop)
  Q1 Q2 Q3 a (b: forall (b: A) (s: St), b = fst (runState a s) -> st St B):
  (st_spec P1 a (fun _ => Q1)) ->
  (forall x s Heq, st_spec (Q1 x) (b x s Heq) (fun _ => (Q2 x))) ->
  (*Weaken rest*)
  (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) ->
  st_spec P1 (st_bind_dep _ _ _ a b) (fun _ => Q3).
Proof.
  intros Ha Hb Hw. eapply prove_st_spec_dep_bnd; eauto.
  apply Hb. simpl. auto.
Qed.

(*Counter*)
Lemma st_spec_incr (P1: CoqBigInt.t -> Prop) 
  (Q1: CoqBigInt.t -> unit -> CoqBigInt.t -> Prop):
  (forall i, P1 i -> Q1 i tt (CoqBigInt.succ i)) ->
  st_spec P1 (C.incr tt) Q1.
Proof.
  intros Hsucc. unfold st_spec; simpl. auto.
Qed.

(*Any constant invariant is preserved*)
Lemma st_spec_const {A B: Type} (x: st A B) (P1 P2: Prop):
  (P1 -> P2) ->
  st_spec (fun _ => P1) x (fun _ _ _ => P2).
Proof.
  unfold st_spec; auto.
Qed.

Lemma st_spec_init {A B: Type} (x: st A B) (P: A -> Prop):
  st_spec P x (fun s1 _ _ => P s1).
Proof.
  unfold st_spec. auto.
Qed.

(* Lemma st_spec_frame {A B: Type} (P1 P2: A -> Prop) Q1 (o: st A B):
  st_spec P1 o Q1 ->
  (st_spec P2 o (fun _ _ i => P2 i)) -> (*This property is preserved*)
  st_spec (fun i => P2 i /\ P1 i) o (fun s1 r s2 => P2 s2 /\ Q1 s1 r s2).
Proof.
  unfold st_spec. intros Ho Hpres. intros Hspec.
  intros i [Hp2 Hp1]. *)


(*TODO: move*)
(* Definition st_prop {A B: Type} (P: A -> B -> Prop) (x: B) (s: st A B) : Prop :=
  forall a, P a x -> P (runState s a). *)

(*P is an invariant relating the inputs and outputs with the states
  P1 is a property that holds on the output, assuming the invariant
  holds of the input*)
(* Definition st_spec {A B: Type} (P: A -> B -> Prop)
  (P1: B -> Prop) (x: B) (s: st A B) :=
  forall a, P a x ->
    P (snd (runState s a)) (fst (runState s a)) /\
    P1 (fst (runState s a)). 

Lemma st_spec_bind {A B: Type} (P: A -> B -> Prop)
  (P1 P2: B -> Prop) (x: B) (f: B -> st A B) (y: st A B):
  st_spec P P2 x y -> (*NOTE: don't need P1 here*)
  ( st_spec P P1 x (f x)) ->
  st_spec P P1 x (st_bind f y).
Proof.
Admitted. *)
  (* unfold st_spec, st_bind; simpl; intros Hx Hb a Ha.
  destruct (runState y a) as [v s] eqn : Hrun; simpl.
  apply Hb. specialize (Hx _ Ha).
  rewrite Hrun in Hx. simpl in Hx. apply Hx.
Qed.  *)

(*Term well-formed wrt state - all variables have smaller indices*)
Definition tm_vars t := tm_fv t ++ tm_bnd t.
Definition tm_st_wf (i: CoqBigInt.t) (t: tm) : Prop :=
  forall v, In v (tm_vars t) -> snd v < i.

(*Prove correctness of substitution*)

(*Traversal well-formed*)

Section TraverseWf.
Variable (T: Type).

Print tm_traverse.

(*Any term remains well-formed after any other term is traversed
  (i.e. the counter only increases)*)
(* Lemma traverse_wf wconstr wvar wadd wmult wlet tm1 tm2:
  st_spec (fun s1 => tm_st_wf s1 tm2)
    (tm_traverse T wconstr wvar wadd wmult wlet tm1)
    (fun _ _ s2 => tm_st_wf s2 tm2).
Proof.
  apply tm_traverse_elim.
  - intros c. apply prove_ simpl. *)

End TraverseWf.
(*First, prove well-formed*)
Section SubCorrect.
Variable (v: var) (t: tm).
Definition sub_rep (vv: val) (tm1 tm2: tm) :=
  tm_rep vv tm1 = tm_rep (add_val v (tm_rep vv t) vv) tm2.

(*[t_open_bound] increases the state*)
Lemma t_open_bound_st (b: tm_bound):
  st_spec (fun _ => True) (t_open_bound b)
    (fun i _ j => i < j).
Proof.
  unfold t_open_bound.
  destruct b as [v2 t2].
  apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
    (Q1:= fun i _ j => i < j)
    (Q2:=fun _ i _ j => i <= j)
    (Q3:=fun i _ j => i < j); auto; [| |intros; lia].
  + unfold rename_var, create_var.
    (*Reason about counter*)
    apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
    (Q1:= fun i _ j => i < j)
    (Q2:=fun _ i _ j => i <= j)
    (Q3:=fun i _ j => i < j); auto; [| | intros; lia].
    * apply st_spec_incr. intros. (*TODO: lemma*)
      unfold CoqBigInt.succ. lia.
    * intros _. apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
      (Q1:= fun i _ j => i <= j)
      (Q2:=fun _ i _ j => i <= j)
      (Q3:=fun i _ j => i <= j); auto; [| | intros; lia].
      -- apply st_spec_get. intros; lia.
      -- intros x. apply prove_st_spec_ret. intros; lia.
  + intros x. apply prove_st_spec_ret. intros; lia.
Qed.

(* 
Lemma t_open_bound_spec (tm1: tm) (b: tm_bound):
  st_spec (fun i => tm_st_wf i tm1) (t_open_bound b) 
    (fun _ b2 s2 => tm_st_wf s2 tm1 /\ (*Still wf*)
    ~ In (fst b2) (tm_vars tm1) /\ (*New var in term's vars*)
    ~ In (fst b2) (tm_vars (snd b)) /\ (*New var not in old term*)
    (*semantics are same except v is mapped to new var*)
    forall vv, tm_rep vv (snd b2) = tm_rep (add_val v (vv (fst b2)) vv) (snd b)).
Proof.
  unfold t_open_bound.
  destruct b as [v2 t2].
  apply prove_st_spec_bnd_nondep with (Q1:=fun v1 s1 => 
    tm_st_wf s1 tm1 /\
    ~ 
    )
    (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
  - unfold rename_var, create_var.
    (*Here, use counter info*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
      (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
    + apply st_spec_incr. 
      (*The only interesting part: if wf, still wf with succ*)
      intros i. unfold tm_st_wf.
      (*TODO: add result: i < CoqBigInt.succ i*)
      intros Hlt x Hinx. 
      assert (Hsucc: forall x, x < CoqBigInt.succ x) by (unfold CoqBigInt.succ; lia).
      specialize (Hsucc i). specialize (Hlt _ Hinx). lia.
    + intros _. apply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
      (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
      * apply st_spec_get. auto.
      * intros i. apply prove_st_spec_ret. auto.
  - intros x. apply prove_st_spec_ret. auto.
Qed.

st_spec (fun i : CoqBigInt.t => tm_st_wf i t) (t_open_bound b)
(fun (_ : CoqBigInt.t) (r : var * tm) (s2 : CoqBigInt.t) =>
tm_st_wf s2 t /\ ~ In (fst r) (tm_fv t1)) *)

Lemma tm_st_wf_lt i j tm1:
  tm_st_wf i tm1 ->
  i <= j ->
  tm_st_wf j tm1.
Proof. unfold tm_st_wf. intros Hwf Hij v1 Hinv1.
  specialize (Hwf _ Hinv1). lia. 
Qed.

Definition var_st_wf (i: CoqBigInt.t) (v: var) : Prop :=
  snd v < i.

Lemma var_st_wf_lt i j v1:
  var_st_wf i v1 ->
  i <= j ->
  var_st_wf j v1.
Proof.
  unfold var_st_wf. lia.
Qed.

(*If the state only increases, all terms are still wf*)
Lemma tm_st_wf_preserved {A: Type} (tm1: tm) (o: state CoqBigInt.t A):
  st_spec (fun _ => True) o (fun i _ j => i <= j) ->
  st_spec (fun i => tm_st_wf i tm1) o (fun _ _ j => tm_st_wf j tm1).
Proof.
  intros Hspec.
  apply st_spec_weaken with (P1:=fun i => True /\ tm_st_wf i tm1)
    (Q1:=fun i _ j => i <= j /\ tm_st_wf i tm1); auto.
  - intros i _ j [Hij Hwf]. eapply tm_st_wf_lt; eauto.
  - apply st_spec_and; auto. apply st_spec_init.
Qed.

Lemma var_st_wf_preserved {A: Type} (v1: var) (o: state CoqBigInt.t A):
  st_spec (fun _ => True) o (fun i _ j => i <= j) ->
  st_spec (fun i => var_st_wf i v1) o (fun _ _ j => var_st_wf j v1).
Proof.
  intros Hspec.
  apply st_spec_weaken with (P1:=fun i => True /\ var_st_wf i v1)
    (Q1:=fun i _ j => i <= j /\ var_st_wf i v1); auto.
  - intros i _ j [Hij Hwf]. eapply var_st_wf_lt; eauto.
  - apply st_spec_and; auto. apply st_spec_init.
Qed.

(*TODO: prove stronger lemma after*)
Lemma t_open_bound_wf (tm1: tm) (b: tm_bound):
  st_spec (fun i => tm_st_wf i tm1) (t_open_bound b) 
    (fun _ _ s2 => tm_st_wf s2 tm1).
Proof.
  apply tm_st_wf_preserved.
  apply st_spec_weaken with (P1:=fun _ => True)
  (Q1:=fun i _ j => i < j); auto; [intros; lia|].
  apply t_open_bound_st.
Qed.
(*   
   intros i; auto.
  -

  unfold t_open_bound.
  destruct b as [v2 t2].
  eapply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
    (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
  - unfold rename_var, create_var.
    (*Here, use counter info*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
      (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
    + apply st_spec_incr. 
      (*The only interesting part: if wf, still wf with succ*)
      intros i. unfold tm_st_wf.
      (*TODO: add result: i < CoqBigInt.succ i*)
      intros Hlt x Hinx. 
      assert (Hsucc: forall x, x < CoqBigInt.succ x) by (unfold CoqBigInt.succ; lia).
      specialize (Hsucc i). specialize (Hlt _ Hinx). lia.
    + intros _. apply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
      (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
      * apply st_spec_get. auto.
      * intros i. apply prove_st_spec_ret. auto.
  - intros x. apply prove_st_spec_ret. auto.
Qed. *)

(*Prove that resulting state is larger*)
Lemma sub_t_incr (tm1: tm):
  st_spec (fun _ => True) (sub_t v t tm1) (fun s1 _ s2 => s1 <= s2).
Proof.
  unfold sub_t.
  apply tm_traverse_elim.
  - intros c; apply prove_st_spec_ret. intros. lia.
  - intros x. apply prove_st_spec_ret. intros. lia.
  - intros o t1 t2 IH1 IH2.
    apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
    (Q1:= fun i _ j => i <= j)
    (Q2:=fun _ i _ j => i <= j)
    (Q3:=fun i _ j => i <= j); auto; [| intros; lia].
    intros r1. apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
    (Q1:= fun i _ j => i <= j)
    (Q2:=fun _ i _ j => i <= j)
    (Q3:=fun i _ j => i <= j); auto; [| intros; lia].
    intros r2. apply prove_st_spec_ret. intros; lia.
  - intros t1 b IHb IHt1.
    apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
    (Q1:= fun i _ j => i <= j)
    (Q2:=fun _ i _ j => i <= j)
    (Q3:=fun i _ j => i <= j); auto; [| intros; lia].
    intros r1.
    apply prove_st_spec_dep_bnd with (P2:= fun _ _ => True) 
    (Q1:= fun i _ j => i <= j)
    (Q2:=fun _ i _ j => i <= j)
    (Q3:=fun i _ j => i <= j); auto; [| | intros; lia].
    + (*Prove [t_open_bound]*) eapply st_spec_weaken_post.
      2: apply t_open_bound_st. simpl. intros; lia.
    + (*Prove rest - from IH2*)
      intros b2 i Hb2.
      apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
      (Q1:= fun i _ j => i <= j)
      (Q2:=fun _ i _ j => i <= j)
      (Q3:=fun i _ j => i <= j); auto; [| | intros; lia].
      1: { eapply IHb; eauto. }
      intros t2. apply prove_st_spec_ret; intros; lia.
Qed.

(*Therefore, all terms and variables are wf*)
Lemma sub_t_wf (tm2: tm) (tm1: tm):
  st_spec (fun i => tm_st_wf i tm2)
    (sub_t v t tm1)
    (fun _ _ s2 => tm_st_wf s2 tm2).
Proof.
  apply tm_st_wf_preserved, sub_t_incr.
Qed.

Lemma sub_t_var_wf (v1: var) (tm1: tm):
  st_spec (fun i => var_st_wf i v1)
    (sub_t v t tm1)
    (fun _ _ s2 => var_st_wf s2 v1).
Proof.
  apply var_st_wf_preserved, sub_t_incr.
Qed.

(* 
(*TODO: START *)


      apply t_open_bound_st.

    
    
     (Q1:=fun v1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r1.

      * apply IH1. auto.
      * intros r2. apply prove_st_spec_ret.
    
     with (P1).
  
  
   auto.

Lemma sub_t_wf (tm2: tm) (tm1: tm):
  st_spec (fun i => tm_st_wf i tm2)
    (sub_t v t tm1)
    (fun _ _ s2 => tm_st_wf s2 tm2). 
Proof.
  unfold sub_t.
  apply tm_traverse_elim.
  - intros c. apply prove_st_spec_ret. auto.
  - intros x. apply prove_st_spec_ret. auto.
  - intros o t1 t2 IH1 IH2.
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r1.
    apply prove_st_spec_bnd_nondep with (Q1:=fun r2 s2 => tm_st_wf s2 tm2)
    (Q2 := fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r2. apply prove_st_spec_ret. auto.
  - (*let case*) intros t1 b IH1 IH2.
    (*eliminate dependent bind*)
    (* rewrite <- (tm_traverse_equation_5 tm _ _ _ _
      (fun _ x _ r1 r2 => st_ret (Tlet r1 (x, r2)))),
    tm_traverse_let. *)
    (*Now go through binds*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r1.
    (*Here, need to reason about [t_open_bound]*)
    (*TODO: is this right Q1 and Q2?*)
    apply prove_st_spec_dep_bnd_nondep with (Q1:=fun v1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    + apply t_open_bound_wf.
    + (*Now use 2nd IH*)
      intros b1 s1 Hb1.
      apply prove_st_spec_bnd_nondep with (Q1:=fun v1 s1 => tm_st_wf s1 tm2)
      (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
      * (*Why we needed "dep" case - for IH premise*) eapply IH1; eauto.
      * intros t2. apply prove_st_spec_ret. auto.
Qed. *)



(* Lemma sub_t_var_wf (x: var)  (tm1: tm):
  st_spec (fun i => var_st_wf i x)
    (sub_t v t tm1)
    (fun _ _ s2 => var_st_wf s2 x). 
Proof.
  unfold sub_t.
  apply tm_traverse_elim.
  - intros c. apply prove_st_spec_ret. auto.
  - intros x. apply prove_st_spec_ret. auto.
  - intros o t1 t2 IH1 IH2.
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r1.
    apply prove_st_spec_bnd_nondep with (Q1:=fun r2 s2 => tm_st_wf s2 tm2)
    (Q2 := fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r2. apply prove_st_spec_ret. auto.
  - (*let case*) intros t1 b IH1 IH2.
    (*eliminate dependent bind*)
    (* rewrite <- (tm_traverse_equation_5 tm _ _ _ _
      (fun _ x _ r1 r2 => st_ret (Tlet r1 (x, r2)))),
    tm_traverse_let. *)
    (*Now go through binds*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    intros r1.
    (*Here, need to reason about [t_open_bound]*)
    (*TODO: is this right Q1 and Q2?*)
    apply prove_st_spec_dep_bnd_nondep with (Q1:=fun v1 s1 => tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
    + apply t_open_bound_wf.
    + (*Now use 2nd IH*)
      intros b1 s1 Hb1.
      apply prove_st_spec_bnd_nondep with (Q1:=fun v1 s1 => tm_st_wf s1 tm2)
      (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.
      * (*Why we needed "dep" case - for IH premise*) eapply IH1; eauto.
      * intros t2. apply prove_st_spec_ret. auto.
Qed. *)

Lemma tm_st_wf_op i o t1 t2:
  tm_st_wf i t1 ->
  tm_st_wf i t2 ->
  tm_st_wf i (Top o t1 t2).
Proof.
Admitted.
  (* unfold tm_st_wf. simpl. setoid_rewrite in_app_iff. 
  intros H1 H2 x [Hinv | Hinv]; auto.
Qed. *)

Ltac destruct_all :=
  repeat match goal with
  | H: ?P /\ ?Q |-_ => destruct H
  end.

Ltac split_all :=
  repeat match goal with
  | |- ?P /\ ?Q => split
  end.

Ltac destruct_or :=
  repeat match goal with
  | H: ?P \/ ?Q |- _ => destruct H
  end.

Lemma tm_st_wf_op_iff i o t1 t2:
  tm_st_wf i (Top o t1 t2) <->
  tm_st_wf i t1 /\
  tm_st_wf i t2.
Proof.
  unfold tm_st_wf, tm_vars; simpl.
  repeat (setoid_rewrite in_app_iff). split; intros Hall; destruct_all;
  split_all; intros; auto; destruct_or; auto.
Qed.


Lemma tm_st_wf_let_iff i t1 b:
  tm_st_wf i (Tlet t1 b) <->
  tm_st_wf i t1 /\
  var_st_wf i (fst b) /\
  tm_st_wf i (snd b).
Proof.
  destruct b as [v1 t2].
  unfold tm_st_wf, var_st_wf, tm_vars; simpl. 
  repeat (setoid_rewrite in_app_iff; simpl).
  split.
  - intros Hwf. split_all; auto.
    + intros; destruct_all; destruct_or; auto.
    + intros v2 [Hinv2 | Hinv2]; auto.
      destruct (var_dec v2 v1); subst; auto.
      apply Hwf. left. right. apply in_in_remove; auto.
  - intros [Hwf1 [Hwfv Hwf2]] v2. intros; destruct_or; subst; auto.
    apply in_remove in H. destruct_all. auto.
Qed.


(* Lemma tm_st_wf_op_inv i o t1 t2: *)
  (* tm_st_wf i (Top o t1 t2) ->
  tm_st_wf i t1 /\
  tm_st_wf i t2.
Proof.
  unfold tm_st_wf, tm_vars; simpl.
  repeat (setoid_rewrite in_app_iff). intros Hall.
  split; intros x [Hinv | Hinv]; auto.
Qed. *)

Lemma sub_rep_op o vv t1 t2 r1 r2:
  sub_rep vv r1 t1 ->
  sub_rep vv r2 t2 ->
  sub_rep vv (Top o r1 r2) (Top o t1 t2).
Proof.
  unfold sub_rep. simpl. intros; f_equal; auto.
Qed.




Lemma sub_t_correct (tm1: tm) :
  st_spec 
    (fun i => tm_st_wf i t /\ tm_st_wf i tm1 /\ var_st_wf i v) 
    (sub_t v t tm1)
    (fun _ t2 i => tm_st_wf i t /\ tm_st_wf i tm1 /\ 
      tm_st_wf i t2 /\ var_st_wf i v /\ forall vv, sub_rep vv t2 tm1).
Proof.
  unfold sub_t.
  apply tm_traverse_elim.
  - unfold sub_rep. intros c. simpl. apply prove_st_spec_ret.
    intros i Hwf. simpl. destruct_all; split_all; auto.
  - intros x. unfold sub_rep. simpl. apply prove_st_spec_ret.
    intros i [Hwf1 [Hwf2 Hwfv]]. unfold add_val.
    split_all; auto; destruct (var_dec v x); auto.
  - intros o t1 t2 IH2 IH1.
    (*First, change to t1 and t2 wf*)
    apply st_spec_weaken with (P1:= fun i =>
      tm_st_wf i t2 /\ (tm_st_wf i t /\ tm_st_wf i t1 /\ var_st_wf i v))
    (Q1:=fun _ tm2 i =>
      tm_st_wf i t /\ tm_st_wf i t1 /\ tm_st_wf i t2 /\ 
      tm_st_wf i tm2 /\ var_st_wf i v /\ (forall vv, sub_rep vv tm2 (Top o t1 t2)));
    try solve[intros; rewrite tm_st_wf_op_iff in *; intros; destruct_all; split_all; auto].
    (*Now go through first IH*)
    (*A bit tricky: we will need to separate out some preconditions
      and prove they are preserved separately*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 =>
      (*Stuff to prove separately*)
      (tm_st_wf s1 t2) /\
      (*Conclusions of IH1*)
      (tm_st_wf s1 t /\
      tm_st_wf s1 t1 /\
      tm_st_wf s1 r1 /\
      var_st_wf s1 v /\
      (forall vv, sub_rep vv r1 t1)))
    (*TODO: isn't this the same as post*)
    (Q2:= fun _ t3 s4 =>
      tm_st_wf s4 t /\
      tm_st_wf s4 t1 /\
      tm_st_wf s4 t2 /\
      tm_st_wf s4 t3 /\
      var_st_wf s4 v /\
      (forall vv, sub_rep vv t3 (Top o t1 t2))); auto;
    [apply st_spec_and; [apply sub_t_wf |apply IH1] |].
    (*Now do same for t2 part*)
    intros r1.
    (*Again weaken to get hyps in right place*)
    apply st_spec_weaken_pre with (P1:= fun i =>
      (*Not needed in IH*)
      (tm_st_wf i t1 /\ tm_st_wf i r1 /\ (forall vv : val, sub_rep vv r1 t1)) /\ 
      (*In IH*)
      (tm_st_wf i t /\ tm_st_wf i t2 /\ var_st_wf i v));
    [intros; destruct_all; split_all; auto|].
    apply prove_st_spec_bnd_nondep with (Q1:=fun r2 s2 =>
      (*Suff to prove separately*)
      (tm_st_wf s2 t1 /\ tm_st_wf s2 r1 /\ (forall vv : val, sub_rep vv r1 t1)) /\
      (*Concludions of IH2*)
      (tm_st_wf s2 t /\ tm_st_wf s2 t2 /\ tm_st_wf s2 r2 /\ var_st_wf s2 v /\
        (forall vv, sub_rep vv r2 t2)))
    (Q2:=fun _ t3 s4 =>
      tm_st_wf s4 t /\ tm_st_wf s4 t1 /\ tm_st_wf s4 t2 /\
      tm_st_wf s4 t3 /\ var_st_wf s4 v /\
      (forall vv, sub_rep vv t3 (Top o t1 t2))); auto;
    [apply st_spec_and; [| apply IH2; auto]|].
    1: { 
      apply st_spec_and; [apply sub_t_wf| apply st_spec_and];
      [apply sub_t_wf | apply st_spec_const]; auto.
    }
    (*Now at end, prove goal*)
    intros r2.
    apply prove_st_spec_ret.
    intros i [[Hwf1 [Hwfr1 Hval1]] [Hwft [Hwf2 [Hwfr2 [Hwfv Hval2]]]]].
    split_all; auto.
    + rewrite tm_st_wf_op_iff. split; auto.
    + intros vv. apply sub_rep_op; auto.
  - (*Tlet - interesting case*)
    intros t1 b1 IHb IHt1.
    (*Like before, first remove Tlet from wf*)
    apply st_spec_weaken with (P1:= fun i =>
      (tm_st_wf i (snd b1) /\ var_st_wf i (fst b1)) /\
      (tm_st_wf i t /\ tm_st_wf i t1 /\ var_st_wf i v))
    (Q1:=fun _ tm2 i => tm_st_wf i t /\ tm_st_wf i t1 /\
      var_st_wf i (fst b1) /\ tm_st_wf i (snd b1) /\
      tm_st_wf i tm2 /\ var_st_wf i v /\ 
      (forall vv, sub_rep vv tm2 (Tlet t1 b1))); auto;
    try solve[ setoid_rewrite tm_st_wf_let_iff; intros; destruct_all; split_all; auto].
    (*Now apply IHt1*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 i =>
      (*Stuff to prove separately*)
      (tm_st_wf i (snd b1) /\ var_st_wf i (fst b1)) /\
      (*Conclusions of IH*)
      (tm_st_wf i t /\ tm_st_wf i t1 /\ tm_st_wf i r1 /\
       var_st_wf i v /\ (forall vv, sub_rep vv r1 t1)))
    (Q2:=(fun _ tm2 i =>
      tm_st_wf i t /\
      tm_st_wf i t1 /\
      var_st_wf i (fst b1) /\
      tm_st_wf i (snd b1) /\
      tm_st_wf i tm2 /\ var_st_wf i v /\ 
        (forall vv, sub_rep vv tm2 (Tlet t1 b1)))); auto.
    1: {
      apply st_spec_and; [apply st_spec_and | apply IHt1];
      [apply sub_t_wf|apply sub_t_var_wf].
    }
    intros r1.
    (*TODO: START*)
      (tm_st_wf s1 t2) /\
      (*Conclusions of IH1*)
      (tm_st_wf s1 t /\
      tm_st_wf s1 t1 /\
      tm_st_wf s1 r1 /\
      var_st_wf s1 v /\
      (forall vv, sub_rep vv r1 t1)))
    (*TODO: isn't this the same as post*)
    (Q2:= fun _ t3 s4 =>
      tm_st_wf s4 t /\
      tm_st_wf s4 t1 /\
      tm_st_wf s4 t2 /\
      tm_st_wf s4 t3 /\
      var_st_wf s4 v /\
      (forall vv, sub_rep vv t3 (Top o t1 t2))); auto;
    apply prove_
    
     }

    (*TODO: prove iff lemma for tm_st_wf Tlet*)
    (*idea: first only consumes t1, gives v1
      then in [t_open_bound], get that
      1. new var is not in bound *)
      Print unsafe_s.


    1: {  }

    (Q1:=fun _ tm2 i =>
      tm_st_wf i t /\ tm_st_wf i t1 /\ tm_st_wf i t2 /\ 
      tm_st_wf i tm2 /\ var_st_wf i v /\ (forall vv, sub_rep vv tm2 (Top o t1 t2)));

    + (*Prove t1 part*)
      .

  (*Idea: P2: after we have IH1, Q2, have full result (rest)*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 =>
      (tm_st_wf s1 t /\ 
      tm_st_wf s1 t2) /\
      tm_st_wf s1 t1 /\
      tm_st_wf s1 r1 /\
      (forall vv, sub_rep vv r1 t1))
    (Q2:= fun _ t3 s4 =>
      tm_st_wf s4 t /\
      tm_st_wf s4 (Top o t1 t2) /\
      tm_st_wf s4 t3 /\
      (forall vv, sub_rep vv t3 (Top o t1 t2))); auto.
    1: { eapply st_spec_weaken. 3: apply IH2. all: simpl; auto.
      intros; destruct_all; auto.
      intros; destruct_all; auto. }
    intros r1.
    (*Idea: prove stronger Post (post of IH)
      combine with "and"*)
    apply prove_st_spec_bnd_nondep with
    (Q1:= fun r2 s2 =>
      (tm_st_wf s2 t /\
      tm_st_wf s2 t2 /\
      tm_st_wf s2 r2 /\
      (forall vv, sub_rep vv r2 t2)) /\
      (
      tm_st_wf s2 t1 /\
      tm_st_wf s2 r1 /\
      (forall vv, sub_rep vv r1 t1))
      )
    (Q2:= fun _ t3 s4 =>
      tm_st_wf s4 t /\
      tm_st_wf s4 (Top o t1 t2) /\
      tm_st_wf s4 t3 /\
      (forall vv, sub_rep vv t3 (Top o t1 t2))); auto.
    +  (*Need to use "and" lemma to split*)
      (*Forst, get t and t2 together*)
      apply st_spec_and. [apply IH1; auto|].
      (*Now, need to show that [tm_st_wf] and [sub_rep] are preserved*)
      (*Separate lemma to show just wf preservation*)
      apply st_spec_and; [apply sub_t_wf|].
      apply st_spec_const. auto.
    + intros r2. apply prove_st_spec_ret.
      intros i [[Hwft [Hwfr2 Hrep2]] [Hwfr1 Hrep1]].
      split; [|split]; auto.
      (*Prove props preserved by [Top]*)
      -- apply tm_st_wf_op; auto.
      -- intros vv. apply sub_rep_op; auto.
  - (*let case - interesting*)
    intros t1 b IHb IHt1.
    (*First, use IHt1*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun r1 s1 =>
      tm_st_wf s1 t /\ 
      tm_st_wf s1 r1 /\
      (forall vv, sub_rep vv r1 t1))
    (Q2:= fun _ t3 s4 =>
      tm_st_wf s4 t /\
      tm_st_wf s4 t3 /\
      (forall vv, sub_rep vv t3 (Tlet t1 b))); auto.
    intros r1.
    (*Now open the bound - need to know that new var not in freevars of t*)
    apply prove_st_spec_dep_bnd_nondep with 
    (Q1:=fun y1 s2 => 
      tm_st_wf s2 t /\ 
      tm_st_wf s2 r1 /\
      (forall vv, sub_rep vv r1 t1) /\
      ~ In (fst y1) (tm_fv t1)) (*TODO: see if this is enough*)
     (Q2:= fun _ t3 s4 =>
      tm_st_wf s4 t /\
      tm_st_wf s4 t3 /\
      (forall vv, sub_rep vv t3 (Tlet t1 b))); auto.
    + (*Prove [t_open_bound] part*)
      (*Want to get rid of r1 parts, not interesting*)
      eapply st_spec_weaken with (P1:= fun i =>
        (tm_st_wf i r1 /\ (forall vv : val, sub_rep vv r1 t1)) /\
        tm_st_wf i t) (Q1 := fun _ x f =>
        (tm_st_wf f r1 /\ (forall vv : val, sub_rep vv r1 t1)) /\
        (tm_st_wf f t /\ ~ In (fst x) (tm_fv t1))); auto.
      1: { intros i. intros [Hwf1 [Hwf2 Hvv]]. auto. }
      1: { intros _ x f [[Hwf1 Hvv] [Hwf2 Hfv]]; auto. }
      (*separate out interesting parts*)
      apply st_spec_and.
      1: { apply st_spec_and; [apply t_open_bound_wf|apply st_spec_const]; auto. }
      (*Prove postcondition of [t_open_bound]*)
      {
        unfold t_open_bound.
        destruct b as [v2 t2]. 
        eapply prove_st_spec_bnd_nondep with (Q1:= fun v1 s1 => tm_st_wf s1 t /\
        ~ In v1 (tm_fv t1)) (Q2:=fun _ r s2 =>
          tm_st_wf s2 t /\ ~ In (fst r) (tm_fv t1)); auto.
        - (*[rename_var] goal*)
          unfold rename_var.

      }
        *


eapply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
    (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
  - unfold rename_var, create_var.
    (*Here, use counter info*)
    apply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
      (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
    + apply st_spec_incr. 
      (*The only interesting part: if wf, still wf with succ*)
      intros i. unfold tm_st_wf.
      (*TODO: add result: i < CoqBigInt.succ i*)
      intros Hlt x Hinx. 
      assert (Hsucc: forall x, x < CoqBigInt.succ x) by (unfold CoqBigInt.succ; lia).
      specialize (Hsucc i). specialize (Hlt _ Hinx). lia.
    + intros _. apply prove_st_spec_bnd_nondep with (Q1:=fun _ s1 => tm_st_wf s1 tm1)
      (Q2:=fun _ _ s2 => tm_st_wf s2 tm1); auto.
      * apply st_spec_get. auto.
      * intros i. apply prove_st_spec_ret. auto.
  - intros x. apply prove_st_spec_ret. auto.


      * apply 
      1: { intros i.
      
      
       rewrite and_comm. }
      apply st_spec_and; [apply t_open_bound_wf|].
      apply st_spec_and; [apply t_open_bound_wf|].
       Search t_open_bound.
    
    tm_st_wf s1 tm2)
    (Q2:= fun _ t3 s4 => tm_st_wf s4 tm2); auto.


    * auto.
    + auto.
  - 
          unfold tm_st_wf.
        
         [Hwft [Hwfr2 [Hrep2 [Hwfr1 Hrep1]]]].

        

(* eapply st_spec_weaken with (Q1:=
        (fun _ t3 s4 =>
          (tm_st_wf )
        
        ).
      3: { apply st_spec_and.  }
      (*Idea: in precondition, add " /\ True"
        then prove "and" *)
      eapply st_spec_weaken.
      3: {
        apply st_spec_and. apply IH1.
      }
      apply st_spec_and.
      * apply IH1.*)
      *
      (Q2 := fun _ t3 t4 =>
        ).
      1: eapply st_spec_weaken; [| | apply IH1; auto].
      1: apply IH1.
       (Q1:=fun r2 s2 =>
      tm_st_wf s2 t /\
      tm_st_wf s2 r1 /\
      (forall vv, sub_rep vv r1 t1) /\
      tm_st_wf s2 r2 /\
      (forall vv, sub_rep vv r2 t2)).
      * eapply st_spec_weaken. 3: apply IH1. 
        -- intros i [Hi _]; exact Hi.
        -- simpl. intros _  apply IH1.
      
       with 
      (*Q1: after IH2*)
      (Q1:= fun _ r2 s2 =>
      tm_st_wf s2 t /\
      tm_st_wf s2 r1 /\
      (forall vv, sub_rep vv r1 t1) /\
      tm_st_wf s2 r2 /\
      (forall vv, sub_rep vv r2 t2))
      (*P2, almost the same - *)
      (P2 := fun r2 s2 =>
      tm_st_wf s2 t /\
      tm_st_wf s2 r1 /\
      (forall vv, sub_rep vv r1 t1) /\
      tm_st_wf s2 r2 /\
      (forall vv, sub_rep vv r2 t2)).
      
      (Q2:= fun _ _ t3 s4 =>
        tm_st_wf s4 t /\
        tm_st_wf s4 t3 /\
        (forall vv, sub_rep vv t3 (Tadd t1 t2))).
      * apply st_spec_weaken with
        (Q1:= fun s2 ). 3: apply IH1; auto.
        -- simpl. intros i [H1 _]; auto.
        -- 
      
       apply prove_st_spec_ret.
    
     eapply prove_st_spec_bnd with 
      (P2:= fun tm i => tm_st_wf i t /\ 
        (forall vv, sub_rep vv x t1) /\ (forall vv, sub_rep vv tm t2))
      (Q1:= fun s1 tm s2 => 
        tm_st_wf s2 t /\
        tm_st_wf s2 tm /\
        (forall vv, sub_rep vv x t1) /\ (forall vv, sub_rep vv tm t2)).
      * eapply st_spec_weaken.
        1: { intros i [Hw H2]. apply Hw. }
        2: apply IH1; auto.
        intros s1 x1 s2. simpl. intros [Hwf1 [Hwf2 Hval1]].
         
       3: apply IH1; auto. all: simpl; auto.
        -- intros i [Hi H2]; auto.
        --  
    (Q1:=(fun (s1 : CoqBigInt.t) (t2 : tm) (s2 : CoqBigInt.t) =>
tm_st_wf s1 t /\
tm_st_wf s2 t2 /\ (forall vv : val, tm_rep vv t2 =
tm_rep (add_val v (tm_rep vv t) vv) t1)))
(Q2:=(fun (v2 : tm)(s2: CoqBigInt.t)(t3: tm) (s3: CoqBigInt.t) =>
  tm_st_wf s2 v2 /\
  tm_st_wf s3 t3 /\
  (forall vv, tm_rep vv t3 = tm_rep (add_val v (tm_rep vv t) vv) t3))).
  + apply IH2.
  + intros x. apply prove_st_spec_bnd with (P2:= fun tm i => tm_st_wf i t)
      (Q1:= (fun (s1 : CoqBigInt.t) (t3 : tm) (s2 : CoqBigInt.t) =>
tm_st_wf s1 t /\
tm_st_wf s2 t3 /\ (forall vv : val, tm_rep vv t3 =
tm_rep (add_val v (tm_rep vv t) vv) t2)))
(Q2:=(fun (v2 : tm)(s2: CoqBigInt.t)(t3: tm) (s3: CoqBigInt.t) =>
  tm_st_wf s2 v2 /\
  tm_st_wf s3 t3 /\
  (forall vv, tm_rep vv t3 = tm_rep (add_val v (tm_rep vv t) vv) t3))).
    * apply IH1; auto.
    * intros y. apply prove_st_spec_ret. simpl. 
  


(fun (s1 : CoqBigInt.t) (t2 : tm) (s2 : CoqBigInt.t) =>
  tm_st_wf s1 t /\
  tm_st_wf s2 t2 /\ (forall vv : val, tm_rep vv t2 =
  tm_rep (add_val v (tm_rep vv t) vv) t1))).
(*     
    
     (P2:=fun tm i =>
      tm_st_wf i t /\ tm_st_wf i tm /\
      forall vv, tm_rep vv tm = tm_rep (add_val v (tm_rep vv t) vv) t1). *)
    + apply IH2.
    + intros x. apply prove_st_spec_bnd with (P2:= fun tm i => tm_st_wf i t)
      (Q1:= (fun (s1 : CoqBigInt.t) (t3 : tm) (s2 : CoqBigInt.t) =>
tm_st_wf s1 t /\
tm_st_wf s2 t3 /\ (forall vv : val, tm_rep vv t3 =
tm_rep (add_val v (tm_rep vv t) vv) t2)))
(Q2:=()).
      * apply IH1; auto.
      * intros y. apply prove_st_spec_ret.


       simpl. 
      2: {}
     apply prove_st_spec_ret.

  
    + intros vv. unfold 
     simpl.
     split_all.

  
   eapply st_spec_weaken. 3: apply st_spec_ret.
    + simpl. auto.
    + simpl. intros i x f [Hif Hx]; subst. auto.
    all: auto.
  unfold sub_t.


  st_spec (fun i t1 => 
    tm_st_wf i t /\ tm_st_wf i t1) (fun (tm2: tm) => 
    forall vv, tm_rep vv tm2 = tm_rep (add_val v (tm_rep vv t) vv) tm1)
  tm1 (sub_t v t tm1).
Proof.
  unfold sub_t.
  apply tm_traverse_elim.
  - intros c. simpl. unfold st_spec, tm_st_wf; simpl; intros; auto.
  - intros x. simpl. unfold st_spec, tm_st_wf; simpl. intros i [Ht _]. 
    split; [split|]; auto.
    + intros y. (*we need to know that t does not introduce larger vars*) 
      destruct (var_dec v x); simpl; auto. contradiction.
    + intros vv. unfold add_val. destruct (var_dec v x); subst; simpl; auto.
  - intros t1 t2 IH1 IH2.
    eapply st_spec_bind.
    2: {
      eapply st_spec_bind.
      2: {

      } 
    }
    + apply IH2.
     with (P2 := fun _ => True).
    + 

  
  
   unfold st_spec in *; simpl in *. 



      * unfold add_val. destruct (var_dec v v); auto. contradiction.
      * unfold add_val. 
   st_spec. simpl.

    )
  st_prop tm_st_wf tm1 ()

  

  (const_case: forall (c: Z), ctr T)
  (var_case: forall (x: var), ctr T)
  (add_case: forall (t1 t2: tm) (r1 r2: T), ctr T)
  (mult_case: forall (t1 t2: tm) (r1 r2: T), ctr T)
  (*NOTE: recursive case 2 on [t_open_bound]*)
  (let_case: forall (t1: tm) (b: tm_bound) (r1 r2: T), ctr T).
  
   simpl.
   intros x.
  
  
   apply functional_extensionality. simpl.
  
   simpl.
  f_equal.

Lemma tm_traverse_eq (tm1: tm):
  tm_traverse tm1 =
  match tm1 with
  | Tconst c => const_case c
  | Tvar x => var_case x
  | Tadd t1 t2 =>
    v1 <- tm_traverse t1 ;;
    v2 <- tm_traverse t2 ;;
    add_case t1 t2 v1 v2
  | Tmult t1 t2 =>
    v1 <- tm_traverse t1 ;;
    v2 <- tm_traverse t2 ;;
    mult_case t1 t2 v1 v2
  | Tlet 


Equations tm_traverse (tm1: tm) : ctr T by wf (tm_size tm1) lt :=
  tm_traverse (Tconst c) := const_case c;
  tm_traverse (Tvar x) := var_case x;
  tm_traverse (Tadd t1 t2) :=
    v1 <- tm_traverse t1 ;;
    v2 <- tm_traverse t2 ;;
    add_case t1 t2 v1 v2;
  tm_traverse (Tmult t1 t2) :=
    v1 <- tm_traverse t1 ;;
    v2 <- tm_traverse t2 ;;
    mult_case t1 t2 v1 v2;
  tm_traverse (Tlet t1 b) :=
    v1 <- tm_traverse t1 ;;
    (*Need dependent types here to have enough information for the proof*)
    st_bind_dep _ _ _ (t_open_bound b)
      (fun y s Heq => 
        v2 <- (tm_traverse (snd y)) ;;
        let_case t1 b v1 v2).


  .


(*Safe substitution*)
From Equations Require Import Equations.
Require Import Lia.
Section SafeSub.
Variable (v: var) (t: tm).

(*Use Equations for now*)
Obligation Tactic := simpl; try lia.
Equations sub_t (tm1: tm) : ctr tm by wf (tm_size tm1) lt :=
  sub_t (Tconst c) := st_ret (Tconst c);
  sub_t (Tvar x) := st_ret (if var_dec x v then t else (Tvar x));
  sub_t (Tadd t1 t2) :=
    t1' <- sub_t t1 ;;
    t2' <- sub_t t2 ;;
    st_ret (Tadd t1' t2');
  sub_t (Tmult t1 t2) :=
    t1' <- sub_t t1 ;;
    t2' <- sub_t t2 ;;
    st_ret (Tmult t1' t2');
  sub_t (Tlet t1 b) :=
    t1' <- sub_t t1 ;;
   (*Need dependent types here to have enough information for the proof*)
    st_bind_dep _ _ _ (t_open_bound b)
      (fun y s Heq => sub_t (snd y)).
Next Obligation.
intros t1 [v1 t2] _ _ y s Hy; subst.
simpl.
rewrite tm_subst_unsafe_var_size. lia.
Defined.
Next Obligation.
intros t1 b _; destruct b; simpl; lia.
Defined.

End SafeSub.

From Coq Require Import Extraction.

Extraction sub_t.

(*Subst*)

unfold t_open_bound. simpl.

intros; subst. 
simpl.
intros t1 b IH t2 bound v2. simpl in *.



(*Use "Well Founded Recursion Done Right"*)
Lemma size_add1 t1 t2: (tm_size t1 < tm_size (Tadd t1 t2))%nat.
Proof. simpl; lia. Qed.
Lemma size_add2 t1 t2: (tm_size t2 < tm_size (Tadd t1 t2))%nat.
Proof. simpl; lia. Qed.
Lemma size_mult1 t1 t2: (tm_size t1 < tm_size (Tmult t1 t2))%nat.
Proof. simpl; lia. Qed.
Lemma size_mult2 t1 t2: (tm_size t2 < tm_size (Tmult t1 t2))%nat.
Proof. simpl; lia. Qed.
Check st_bind_dep.
Fixpoint sub_t (tm1: tm) (ACC: Acc lt (tm_size tm1)) : ctr tm :=
  match tm1 return Acc lt (tm_size tm1) -> ctr tm with
  | Tconst c => fun _ => st_ret (Tconst c)
  | Tvar x => fun _ => st_ret (if var_dec x v then t else (Tvar x))
  | Tadd t1 t2 => fun ACC => 
    t1' <- sub_t t1 (Acc_inv ACC (size_add1 _ _)) ;;
    t2' <- sub_t t2 (Acc_inv ACC (size_add2 _ _)) ;;
    st_ret (Tadd t1' t2')
  | Tmult t1 t2 => fun ACC =>
    t1' <- sub_t t1 (Acc_inv ACC (size_mult1 _ _)) ;;
    t2' <- sub_t t2 (Acc_inv ACC (size_mult2 _ _)) ;;
    st_ret (Tmult t1' t2')
  | Tlet t1 b => fun ACC =>
    t1' <- sub_t t1 (Acc_inv ACC _) ;;
    (*Need dependent types here to have enough information for the proof*)
    st_bind_dep _ _ _ (t_open_bound b)
      (fun y s Heq => sub_t (snd y) (Acc_inv ACC _))
  end ACC.
    
     (sub_t (snd ))
    y <-- s <-- Heq <-- (t_open_bound b) ;;
    sub_t (snd y) (Acc_inv ACC _)
  end ACC.


Obligation Tactic := simpl; try lia.
Equations sub_t (tm1: tm) : ctr tm by wf (tm_size tm1) lt :=
  sub_t (Tconst c) := st_ret (Tconst c);
  sub_t (Tvar x) := st_ret (if var_dec x v then t else (Tvar x));
  sub_t (Tadd t1 t2) :=
    t1' <- sub_t t1 ;;
    t2' <- sub_t t2 ;;
    st_ret (Tadd t1' t2');
  sub_t (Tmult t1 t2) :=
    t1' <- sub_t t1 ;;
    t2' <- sub_t t2 ;;
    st_ret (Tmult t1' t2');
  sub_t (Tlet t1 b) :=
    t1' <- sub_t t1 ;;
    y <- t_open_bound b ;;
    sub_t (snd y).
Next Obligation.
intros t1 b IH t2 bound v2. simpl in *.

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

  match tm1 with
  | Tconst c => st_ret tm1
  | Tvar x => st_ret (if var_dec x v then t else tm1)
  | Tadd t1 t2 => 
    t1' <- sub_t v t t1 ;;
    t2' <- sub_t v t t2 ;;
    st_ret (Tadd t1' t2')
  | Tmult t1 t2 =>
    t1' <- sub_t v t t1 ;;
    t2' <- sub_t v t t2 ;;
    st_ret (Tmult t1' t2')
  | Tlet t1 b =>
    t1' <- sub_t v t t1 ;;
    y <- t_open_bound b ;;
    let (x, t2) := y : var * tm in
    sub_t x t t2
  end.



    Definition t_open_bound (b: tm_bound) : ctr (var * tm) :=
  let (v, t) := b in
  v1 <- rename_var v ;;
  st_ret (v1, tm_subst_unsafe v (Tvar v1) t).
  
  Tadd (sub_t)



Print fmla.



(*let with bindings*)



Print fmla.

Print tm.




(*Open and Close Binders*)

(*TODO: implement open, close binders*)

(*Alpha equivalence*)

