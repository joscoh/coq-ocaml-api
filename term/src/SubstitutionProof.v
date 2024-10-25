From TermAPI Require Import TermAPI TermSemantics.
From CoqCompat Require Export StateHoare.
Require Import Coq.ZArith.BinInt.
Require Import Lia.
Local Open Scope Z_scope.

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

(*Now reason about state and substitution*)

(*Term well-formed wrt state - all variables have smaller indices*)
Definition tm_vars t := tm_fv t ++ tm_bnd t.
Definition tm_st_wf (i: CoqBigInt.t) (t: tm) : Prop :=
  forall v, In v (tm_vars t) -> snd v < i.
Definition var_st_wf (i: CoqBigInt.t) (v: var) : Prop :=
  snd v < i.

Lemma tm_st_wf_lt i j tm1:
  tm_st_wf i tm1 ->
  i <= j ->
  tm_st_wf j tm1.
Proof. unfold tm_st_wf. intros Hwf Hij v1 Hinv1.
  specialize (Hwf _ Hinv1). lia. 
Qed.

Lemma var_st_wf_lt i j v1:
  var_st_wf i v1 ->
  i <= j ->
  var_st_wf j v1.
Proof.
  unfold var_st_wf. lia.
Qed.

(*Prove correctness of substitution*)

(*First, results about [t_open_bound]*)

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
      (Q1:= fun i _ j => i <= j)
      (Q2:=fun _ i _ j => i < j)
      (Q3:=fun i _ j => i < j); auto; [| | intros; lia].
    * apply st_spec_get. intros; lia.
    * intros i.
      apply prove_st_spec_bnd with (P2:= fun _ _ => True) 
      (Q1:= fun i _ j => i < j)
      (Q2:=fun _ i _ j => i <= j)
      (Q3:=fun i _ j => i < j); auto; [| | intros; lia].
      -- (*incr*)
        apply C.st_spec_incr. intros.
        unfold CoqBigInt.succ. lia.
      -- intros _. apply prove_st_spec_ret. intros; lia.
  + intros x. apply prove_st_spec_ret. intros; lia.
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

(*[t_open_bound]*)
Lemma t_open_bound_wf (tm1: tm) (b: tm_bound):
  st_spec (fun i => tm_st_wf i tm1) (t_open_bound b) 
    (fun _ _ s2 => tm_st_wf s2 tm1).
Proof.
  apply tm_st_wf_preserved.
  apply st_spec_weaken with (P1:=fun _ => True)
  (Q1:=fun i _ j => i < j); auto; [intros; lia|].
  apply t_open_bound_st.
Qed.

Lemma t_open_bound_var_wf (v1: var) (b: tm_bound):
  st_spec (fun i => var_st_wf i v1) (t_open_bound b) 
    (fun _ _ s2 => var_st_wf s2 v1).
Proof.
  apply var_st_wf_preserved.
  apply st_spec_weaken with (P1:=fun _ => True)
  (Q1:=fun i _ j => i < j); auto; [intros; lia|].
  apply t_open_bound_st.
Qed.

Section SubCorrect.
Variable (v: var) (t: tm).
Definition sub_rep (vv: val) (tm1 tm2: tm) :=
  tm_rep vv tm1 = tm_rep (add_val v (tm_rep vv t) vv) tm2.

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

(*free vars of [tm_subst_unsafe]*)
Lemma in_fv_subst t1 x t2:
  forall y, In y (tm_fv (tm_subst_unsafe x t1 t2)) -> 
  In y (tm_fv t1) \/ In y (tm_fv t2).
Proof.
  intros y. induction t2 as [| v1 | o tm1 tm2 IH1 IH2 | tm1 [v1 tm2] IHtm1 IHb]; simpl; auto.
  - destruct (var_dec x v1); auto.
  - rewrite !in_app_iff; intros [Hin | Hin]; auto;
    [apply IH1 in Hin | apply IH2 in Hin]; destruct_or; auto.
  - rewrite !in_app_iff. simpl in *. intros [Hin | Hin];
    [apply IHtm1 in Hin; destruct_or; auto|].
    apply in_remove in Hin. 
    destruct Hin as [Hin Hy].
    destruct (var_dec x v1); subst; auto.
    + right. right. apply in_in_remove; auto.
    + apply IHb in Hin. destruct_or; auto.
      right. right. apply in_in_remove; auto.
Qed.

Lemma in_bnd_subst t1 x t2:
  forall y, In y (tm_bnd (tm_subst_unsafe x t1 t2)) -> 
  In y (tm_bnd t1) \/ In y (tm_bnd t2).
Proof.
  intros y. induction t2 as [| v1 | o tm1 tm2 IH1 IH2 | tm1 [v1 tm2] IHtm1 IHb]; simpl; auto.
  - destruct (var_dec x v1); auto.
  - rewrite !in_app_iff; intros [Hin | Hin]; auto;
    [apply IH1 in Hin | apply IH2 in Hin]; destruct_or; auto.
  - rewrite !in_app_iff. simpl in *.
    intros [Heq | [Hin | Hin]]; subst; auto;
    [apply IHtm1 in Hin; destruct_or; auto|].
    destruct (var_dec x v1); subst; auto.
    apply IHb in Hin; destruct_or; auto.
Qed.

Lemma in_vars_subst t1 x t2:
  forall y, In y (tm_vars (tm_subst_unsafe x t1 t2)) -> 
  In y (tm_vars t1) \/ In y (tm_vars t2).
Proof.
  intros y. unfold tm_vars. rewrite !in_app_iff.
  intros [Hinfv | Hinbnd]; [apply in_fv_subst in Hinfv | apply in_bnd_subst in Hinbnd];
  destruct_or; auto.
Qed.

(*The new variable is not in the vars of any wf term*)
Lemma t_open_bound_notin (t1: tm) (b: tm_bound):
  st_spec (fun i => tm_st_wf i t1)
    (t_open_bound b)
    (fun _ b2 _ => ~ In (fst b2) (tm_vars t1)).
Proof.
  unfold t_open_bound.
  destruct b as [v1 t2].
  apply prove_st_spec_bnd_nondep with (Q1:=fun v2 i =>
    tm_st_wf i t1 /\ ~ In v2 (tm_vars t1))
  (Q2:= fun _ b2 _ => ~ In (fst b2) (tm_vars t1)); auto.
  - (*rename var*)
    unfold rename_var, create_var.
    apply prove_st_spec_bnd with (Q1:=fun i x j =>
      x = i /\ x = j /\ tm_st_wf i t1)
    (P2:=fun x j => x = j /\ tm_st_wf j t1)
    (Q2:= fun _ _ v2 i => tm_st_wf i t1 /\ ~ In v2 (tm_vars t1)); auto.
    3: { intros; destruct_all; subst; auto. }
    + apply st_spec_get. auto.
    + intros i1. 
       apply prove_st_spec_bnd with (Q1:=fun i _ j =>
        i = i1 /\ i < j /\ tm_st_wf i t1)
      (P2:=fun _ j => i1 < j /\ tm_st_wf i1 t1)
      (Q2 := fun _ _ v2 i =>
        tm_st_wf i t1 /\ ~ In v2 (tm_vars t1)); auto.
      3: { intros; destruct_all; subst; auto. }
      * apply C.st_spec_incr. intros i [Hi Hwf]; subst; split_all; auto.
        (*TODO*) unfold CoqBigInt.succ; lia.
      * intros _. apply prove_st_spec_ret.
        intros i [Hi Hwf]; split; auto.
        -- eapply tm_st_wf_lt; eauto. lia.
        -- intros Hin. apply Hwf in Hin. simpl in Hin. lia.
  - intros v2. apply prove_st_spec_ret. simpl. intros i [Hin Hnotin]; auto.
Qed.

(*The new variable is not equal to any wf variable*)
Lemma t_open_bound_var_notin x (b: tm_bound):
  st_spec (fun i => var_st_wf i x)
    (t_open_bound b)
    (fun _ b2 _ => snd (fst b2) <> snd x).
Proof.
  unfold t_open_bound.
  destruct b as [v1 t2].
  apply prove_st_spec_bnd_nondep with (Q1:=fun v2 i => 
    var_st_wf i x /\ snd v2 <> snd x)
  (Q2:= fun _ b2 _ => snd (fst b2) <> snd x); auto.
  - (*rename var*)
    unfold rename_var, create_var.
    apply prove_st_spec_bnd with (Q1:=fun i y j =>
      y = i /\ y = j /\ var_st_wf i x)
    (P2:=fun y j => y = j /\ var_st_wf j x)
    (Q2:= fun _ _ v2 i => var_st_wf i x /\ snd v2 <> snd x); auto.
    3: { intros; destruct_all; subst; auto. }
    + apply st_spec_get. auto.
    + intros i1. 
      apply prove_st_spec_bnd with (Q1:=fun i _ j =>
        i = i1 /\ i < j /\ var_st_wf i x)
      (P2:=fun _ j => i1 < j /\ var_st_wf i1 x)
      (Q2 := fun _ _ v2 i =>
        i1 < i /\var_st_wf i1 x /\ snd v2 <> snd x); auto.
      3: { intros; destruct_all; subst; auto. }
      * apply C.st_spec_incr. intros i [Hi Hwf]; subst; split_all; auto.
        (*TODO*) unfold CoqBigInt.succ; lia.
      * intros _. apply prove_st_spec_ret. intros i [Hi Hwf].
        split_all; auto. simpl.
        intros Hc; subst. unfold var_st_wf in Hwf. lia.
      * intros; destruct_all; subst; auto; split; auto.
        eapply var_st_wf_lt; eauto. lia.
  - intros v2. apply prove_st_spec_ret. simpl. intros i [Hin Hnotin]; auto.
Qed.

(*Stronger spec for [t_open_bound]: it does substitution
  correctly*)
Lemma t_open_bound_rep (b: tm_bound):
  st_spec (fun i => tm_st_wf i (snd b) /\ var_st_wf i (fst b))
    (t_open_bound b)
    (fun _ b2 i =>
      tm_st_wf i (snd b2) /\ var_st_wf i (fst b2) /\
      forall vv, tm_rep vv (snd b2) = 
        tm_rep (add_val (fst b) (vv (fst b2)) vv) (snd b) 
    ).
Proof.
  unfold t_open_bound.
  destruct b as [v1 t1]. simpl.
  apply prove_st_spec_bnd_nondep with (Q1:=fun v2 i =>
    tm_st_wf i t1 /\ var_st_wf i v1 /\
    var_st_wf i v2 /\
    ~ In v2 (tm_bnd t1))
  (Q2:=(fun _ b2 i =>
    tm_st_wf i (snd b2) /\
    var_st_wf i (fst b2) /\
    (forall vv : val, tm_rep vv (snd b2) = 
      tm_rep (add_val v1 (vv (fst b2)) vv) t1)));
  auto.
  - (*rename_var*)
    unfold rename_var, create_var.
    eapply prove_st_spec_bnd with (Q1:= fun i x j =>
        x = i /\ x = j /\ tm_st_wf i t1 /\ var_st_wf i v1)
    (P2:=fun x j => x = j /\ tm_st_wf j t1 /\ var_st_wf j v1)
    (Q2:=fun _ _ v2 i => 
      tm_st_wf i t1 /\ var_st_wf i v1 /\ var_st_wf i v2 /\ ~ In v2 (tm_bnd t1)); auto;
    [apply st_spec_get; auto | | intros; destruct_all; subst; auto].
    (*Prove incr*)
    intros i1.
    apply prove_st_spec_bnd with (Q1:=fun i _ j =>
      i = i1 /\ i < j /\ tm_st_wf i1 t1 /\ var_st_wf i1 v1)
    (P2:=fun _ j => i1 < j /\ tm_st_wf i1 t1 /\ var_st_wf i1 v1)
    (Q2 := fun _ _ v2 i =>
      tm_st_wf i t1 /\ var_st_wf i v1 /\ var_st_wf i v2 /\ ~ In v2 (tm_bnd t1)); auto.
    3: { intros; destruct_all; subst; auto. }
    + (*incr*) apply C.st_spec_incr. intros i [Heq [Hwf1 Hwf2]]; subst. 
      split_all; auto. (*TODO*) unfold CoqBigInt.succ; lia.
    + (*create new var*)
      intros _. apply prove_st_spec_ret. intros j [Hij [Hwf1 Hwf2]].
      split_all; auto.
      * eapply tm_st_wf_lt; eauto. lia.
      * eapply var_st_wf_lt; eauto. lia.
      * (*Use wf assumption*)
        unfold tm_st_wf, tm_vars in Hwf1.
        setoid_rewrite in_app_iff in Hwf1.
        intros Hin.
        specialize (Hwf1 _ (ltac:(right; exact Hin))).
        simpl in Hwf1. (*contradiction*) lia.
  - (*Now we know variable not in, prove rep result*)
    intros v2. apply prove_st_spec_ret.
    intros i [Hwft1 [Hwfv1 [Hwfv2 Hnotin]]]. simpl.
    (*Prove wf for results*)
    split_all; auto.
    + unfold tm_st_wf. intros x.
      intros Hinx. apply in_vars_subst in Hinx.
      simpl in Hinx. destruct Hinx as [[Hx | []] | Hinx]; subst; auto.
    + (*And prove rep*)
      intros vv. rewrite tm_subst_unsafe_rep; simpl; auto.
      (*use notin assumption from ctr*)
      intros v3 [Hv23 | []]; subst; auto.
Qed.

(*Prove that resulting state from sub_t is larger*)
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

Lemma sub_rep_op o vv t1 t2 r1 r2:
  sub_rep vv r1 t1 ->
  sub_rep vv r2 t2 ->
  sub_rep vv (Top o r1 r2) (Top o t1 t2).
Proof.
  unfold sub_rep. simpl. intros; f_equal; auto.
Qed.

(*The correctness theorem for substitution: if the input
  terms and variables are well-formed wrt the current state,
  then everything is well-formed after and [sub_rep] holds*)
Theorem sub_t_correct (tm1: tm) :
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
    (*Now we need to *)
    apply prove_st_spec_dep_bnd_nondep with 
    (Q1:=fun b2 s2 => 
      (*Stuff not affected by [t_open_bound]*)
      (tm_st_wf s2 (snd b1) /\ var_st_wf s2 (fst b1) /\
      tm_st_wf s2 t /\ tm_st_wf s2 t1 /\
      tm_st_wf s2 r1 /\ var_st_wf s2 v /\
      (forall vv, sub_rep vv r1 t1)) /\
      (*Var not in*)
      ( ~ In (fst b2) (tm_vars t) /\
      ~ In (fst b2) (tm_vars (snd b1))) /\       (*TODO: do I need to know not in t1 also?*)
      (*Stuff from [t_open_bound_rep]*)
      (*Need 2 things from the bound: variable not in vars of t1*)
      (tm_st_wf s2 (snd b2) /\ var_st_wf s2 (fst b2) /\
      forall vv, tm_rep vv (snd b2) = 
        tm_rep (add_val (fst b1) (vv (fst b2)) vv) (snd b1)) /\
      (*The var is not our previous var*)
      (snd v <> snd (fst b2)))
      (Q2 := fun _ tm2 i => 
        tm_st_wf i t /\ tm_st_wf i t1 /\
        var_st_wf i (fst b1) /\ tm_st_wf i (snd b1) /\
        tm_st_wf i tm2 /\ var_st_wf i v /\ 
        (forall vv : val, sub_rep vv tm2 (Tlet t1 b1))); auto.
    + (*Prove [t_open_bound] part*)
      (*Need to duplicate 2 assumptions*)
      apply st_spec_weaken_pre with (P1:=fun i =>
        (*Not related to t_open_bound*)
          (tm_st_wf i (snd b1) /\ var_st_wf i (fst b1) /\
          tm_st_wf i t /\ tm_st_wf i t1 /\
          tm_st_wf i r1 /\ var_st_wf i v /\ (forall vv : val, sub_rep vv r1 t1)) /\
          (*Preconditions for spec*)
          (tm_st_wf i (snd b1) /\ var_st_wf i (fst b1)) /\
          (*Need for var*)
          (tm_st_wf i t /\ tm_st_wf i (snd b1)) /\
          (*Need for var neq*)
          (var_st_wf i v));
      [intros; destruct_all; split_all; auto|].
      apply st_spec_and.
      * repeat apply st_spec_and; try apply t_open_bound_wf; try apply t_open_bound_var_wf.
        apply st_spec_const; auto.
      * apply st_spec_weaken_post with (Q1:=fun _ r s2 =>
        (tm_st_wf s2 (snd r) /\
          var_st_wf s2 (fst r) /\
          (forall vv : val, tm_rep vv (snd r) = tm_rep (add_val (fst b1) (vv (fst r)) vv) (snd b1))) /\
          (~ In (fst r) (tm_vars t) /\ ~ In (fst r) (tm_vars (snd b1))) /\
          (snd (fst r) <> snd v));
        [ intros; destruct_all; split_all; auto|].
        apply st_spec_and; [apply t_open_bound_rep |].
        apply st_spec_and; [apply st_spec_and; apply t_open_bound_notin |
        ]. apply t_open_bound_var_notin.
    + (*Now we have [t_open_bound] info, apply 2nd IH*)
      intros b2 i2 Hb2.
      (*Again, weaken precondition to separate IH parts and non-IH parts*)
      apply st_spec_weaken_pre with (P1:= fun s2 =>
        (tm_st_wf s2 t /\ tm_st_wf s2 (snd b2) /\ var_st_wf s2 v) /\
        (*Non-IH parts*)
        (tm_st_wf s2 (snd b1) /\ var_st_wf s2 (fst b1) /\
        tm_st_wf s2 t1 /\ tm_st_wf s2 r1 /\ (forall vv : val, sub_rep vv r1 t1)) /\
        ~ In (fst b2) (tm_vars t) /\ ~ In (fst b2) (tm_vars (snd b1)) /\
        var_st_wf s2 (fst b2) /\
        (forall vv : val, tm_rep vv (snd b2) = tm_rep (add_val (fst b1) (vv (fst b2)) vv) (snd b1)) /\
        snd v <> snd (fst b2));      
        [intros; destruct_all; split_all; auto|].
      apply prove_st_spec_bnd_nondep with (Q1:=fun r2 i =>
      (*Stuff from IH*)
      (tm_st_wf i t /\ tm_st_wf i (snd b2) /\
        tm_st_wf i r2 /\ var_st_wf i v /\ 
        (forall vv : val, sub_rep vv r2 (snd b2))) /\
      (*Rest of stuff*)
      (tm_st_wf i (snd b1) /\ var_st_wf i (fst b1) /\
        tm_st_wf i t1 /\ tm_st_wf i r1 /\ (forall vv : val, sub_rep vv r1 t1)) /\
        ~ In (fst b2) (tm_vars t) /\ ~ In (fst b2) (tm_vars (snd b1)) /\
        var_st_wf i (fst b2) /\
        (forall vv : val, tm_rep vv (snd b2) = 
          tm_rep (add_val (fst b1) (vv (fst b2)) vv) (snd b1)) /\
        snd v <> snd (fst b2))
      (Q2:=(fun _  (tm2 : tm) (i : CoqBigInt.t) =>
        tm_st_wf i t /\
        tm_st_wf i t1 /\
        var_st_wf i (fst b1) /\
        tm_st_wf i (snd b1) /\
        tm_st_wf i tm2 /\ var_st_wf i v /\ 
        (forall vv : val, sub_rep vv tm2 (Tlet t1 b1)))); auto.
      1: {
        apply st_spec_and; [eapply IHb; eauto|].
        repeat (apply st_spec_and); try apply sub_t_wf;
        try apply sub_t_var_wf; apply st_spec_const; auto.
      }
      intros r2.
      apply prove_st_spec_ret.
      intros i3.
      (*And now finally, we have to prove the pure proposition about substitution*)
      destruct b1 as [v1 tma];
      destruct b2 as [v2 tmb]; simpl. clear IHb IHt1 Hb2 (*TODO: do we need Hb2*).
      intros [[Hwft [Hwftmb [Hwfr2 [Hwfv Hrep2]]]] 
        [[Hwftma [Hwfv1 [Hwft1 [Hwfr1 Hrep1]]]] 
        [Hnotint [Hnotina [Hwfv2 [Hrepb Hneqvar]]]]]].
      split_all; auto.
      1: { apply tm_st_wf_let_iff. split_all; auto. }
      (*rep is interesting part*)
      intros vv.
      unfold sub_rep in *. simpl.
      (*First, work on LHS*)
      (*Substitute IH1 in rep*)
      replace (tm_rep (add_val v2 (tm_rep vv r1) vv) r2) with
        (tm_rep (add_val v2 (tm_rep (add_val v (tm_rep vv t) vv) t1) vv) r2).
      2: {
        apply tm_rep_change_vv.
        intros x Hinx. unfold add_val at 1 3. destruct (var_dec v2 x); auto.
      }
      (*vv' = v -> [t]_v, vv*)
      remember (add_val v (tm_rep vv t) vv) as vv'.
      (*Use IH2*)
      rewrite Hrep2.
      (*Use fact that v2 notin fv of t to remove the (add_val v2)*)
      replace (tm_rep (add_val v2 (tm_rep vv' t1) vv) t) with
        (tm_rep vv t).
      2: {
        apply tm_rep_change_vv.
        intros x Hinx. unfold add_val. 
        destruct (var_dec v2 x); subst; auto.
        exfalso. apply Hnotint. unfold tm_vars; rewrite in_app_iff; auto.
      }
      (*Now use result of unsafe sub (here, in Hrepb)*)
      rewrite Hrepb.
      (*And lookup v2*)
      replace (add_val v (tm_rep vv t) (add_val v2 (tm_rep vv' t1) vv) v2) with
      (tm_rep vv' t1).
      2: {
        unfold add_val. destruct (var_dec v v2); subst; auto.
        - (*v <> v2 because v2 was fresh*) contradiction.
        - destruct (var_dec v2 v2); auto. contradiction.
      }
      (*Since v2 is not in tma, can remove from rep*)
      apply tm_rep_change_vv.
      intros x Hinx. subst. unfold add_val.
      destruct (var_dec v1 x); subst; simpl; auto.
      destruct (var_dec v x); subst; simpl; auto.
      destruct (var_dec v2 x); subst; auto.
      exfalso. apply Hnotina. unfold tm_vars. rewrite in_app_iff; auto.
Qed.

(*The more useful corollary: semantic and syntactic substitution
  coincide*)
Corollary sub_t_rep (tm1: tm):
  st_spec (fun i => tm_st_wf i t /\ tm_st_wf i tm1 /\ var_st_wf i v)
    (sub_t v t tm1)
    (fun _ t2 _ => forall vv, 
      tm_rep vv t2 = tm_rep (add_val v (tm_rep vv t) vv) tm1).
Proof.
  eapply st_spec_weaken_post. 2: apply sub_t_correct.
  simpl. unfold sub_rep. intros; destruct_all; auto.
Qed.

End SubCorrect.