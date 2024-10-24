Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.
From CoqCompat Require CoqBigInt.
From CoqCompat Require Export Monads CoqCtr.
Require Import Coq.Logic.FunctionalExtensionality. (*only used in 1 unneeded lemma*)

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
  i <- C.get tt ;;
  _ <- C.incr tt ;;
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
Section SafeTraverse.
Local Obligation Tactic := simpl; try lia.

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

(*Using funext, we can prove that this is equivalent 
  to the non-dependent version. We don't use this,
  but it gives us confidence that it is defined correctly*)

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

End SafeTraverse.

(*Safe substitution*)
Definition sub_t  (v: var) (t: tm) (tm1: tm) : ctr tm :=
  tm_traverse tm 
    (fun c => st_ret (Tconst c))
    (fun x => st_ret (if var_dec v x then t else (Tvar x)))
    (fun o t1 t2 r1 r2 =>  st_ret (Top o r1 r2))
    (fun t1 x t2 r1 r2 => st_ret (Tlet r1 (x, r2))) tm1.