From TermAPI Require Import TermAPI.
Local Open Scope Z_scope.
Import ListNotations.


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