From TermAPI Require Import TermAPI TermSemantics SubstitutionProof.
From CoqCompat Require Import Monads.
From CoqCompat Require CoqBigInt.
Import MonadNotations.
Local Open Scope state_scope.

(*Remove only the first let (we don't want recursion)*)
Definition elim_let (t: tm) : ctr tm :=
  match t with
  | Tlet t1 b =>
    y <- t_open_bound b ;;
    let (x, t2) := y : var * tm in
    sub_t x t1 t2
  | _ => st_ret t
  end.

(*We can use the result about [sub_t] to show that this is correct*)
Lemma elim_let_sound (t: tm):
  st_spec (fun i => tm_st_wf i t)
    (elim_let t)
    (fun _ t2 i => forall vv, tm_rep vv t2 = tm_rep vv t).
Proof.
  unfold elim_let. 
  destruct t as [| | | t1 b1]; simpl; try solve[apply prove_st_spec_ret; auto].
  apply prove_st_spec_bnd_nondep with (Q1:=fun y i =>
    tm_st_wf i t1 /\ ~ In (fst y) (tm_vars (snd b1)) /\ 
    tm_st_wf i (snd y) /\ var_st_wf i (fst y) /\
    
    (forall vv : val, tm_rep vv (snd y) = tm_rep (add_val (fst b1) (vv (fst y)) vv) (snd b1)))
  (Q2:=fun _ t2 _ => forall vv, tm_rep vv t2 =
      (let (x, t0) := b1 in tm_rep (add_val x (tm_rep vv t1) vv)
    t0)); auto.
  - (*t_open_bound*)apply st_spec_weaken_pre with (P1:=fun i =>
    (tm_st_wf i t1) /\
    (tm_st_wf i (snd b1)) /\
    (tm_st_wf i (snd b1)) /\
    (var_st_wf i (fst b1))) .
    1: { intros i. rewrite tm_st_wf_let_iff. intros; destruct_all; auto. }
    apply st_spec_and; [apply t_open_bound_wf |].
    apply st_spec_and; [apply t_open_bound_notin|].
    eapply st_spec_weaken_post; [|apply t_open_bound_rep].
    simpl. intros; destruct_all; auto.
  - (*substitution*)
    intros [v2 t2']. simpl.
    (*Idea: rep t2' is preserved*)
    eapply st_spec_weaken with
    (P1:=fun i => (tm_st_wf i t1 /\
    tm_st_wf i t2' /\
    var_st_wf i v2) /\ (~ In v2 (tm_vars (snd b1)) /\ 
      forall vv : val, tm_rep vv t2' = tm_rep (add_val (fst b1) (vv v2) vv) (snd b1)))
    (Q1:=fun _ t2 _ => (forall vv : val, tm_rep vv t2 = tm_rep (add_val v2 (tm_rep vv t1) vv) t2') /\
    (~ In v2 (tm_vars (snd b1)) /\ (forall vv : val, tm_rep vv t2' = tm_rep (add_val (fst b1) (vv v2) vv) (snd b1)))); auto.
    3: {
      apply st_spec_and; [apply sub_t_rep|apply st_spec_const]; auto.
    }
    + intros; destruct_all; auto.
    + (*Last bit: prove reps eq*)
      intros _ x _ [Hrep1 [Hnotin Hrep2]] vv.
      destruct b1 as [v1 t2]; simpl in *.
      rewrite Hrep1, Hrep2.
      apply tm_rep_change_vv.
      intros x1 Hinx1.
      unfold add_val. destruct (var_dec v2 v2); try contradiction.
      destruct (var_dec v2 x1); subst; auto.
      exfalso. apply Hnotin. apply in_app_iff; auto.
Qed.

(*Create and run computation in state monad*)

(*Use same example as OCaml client*)
Definition ex : ctr tm :=
  let one := t_const CoqBigInt.one in
  x <- create_var "x" ;;
  y <- create_var "y" ;;
  st_ret (t_let (t_add one one) (t_close_bound x 
    (t_let (t_add (t_var x) (t_var x)) (t_close_bound y
      (t_let (t_add (t_var y) (t_var y)) (t_close_bound x
        (t_var y)
      ))
    ))
  )).

Definition ex2 : ctr tm :=
  t <- ex ;;
  t1 <- elim_let t ;;
  t2 <- elim_let t1 ;;
  elim_let t2.

(*Now we evaluate according to our semantics*)
Lemma ex2_sem: forall vv,
  tm_rep vv (C.reset ex2) = 4%Z.
Proof.
  intros. reflexivity.
Qed.

(*This can be simplified fully*)
Eval vm_compute in (tm_rep (fun _ => 0%Z) (C.reset ex2)).