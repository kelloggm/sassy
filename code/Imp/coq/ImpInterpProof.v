(**
   Everett Maus (evmaus@uw.edu), 
   Jeffrey Hon (jhon@cs.washington.edu)
*)

Require Import List.
Require Import String.
Require Import ZArith.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Require Import StructTactics.
Require Import ImpSyntax.
Require Import ImpCommon.
Require Import ImpEval.
Require Import ImpSemanticsFacts.
Require Import ImpInterp.

Lemma interp_op1_eval_op1 :
  forall op v v',
    interp_op1 op v = Some v' ->
    eval_unop op v v'.
Proof.
  unfold interp_op1; intros.
  repeat break_match; subst;
    discriminate || solve_by_inversion' ee.
Qed.

Lemma eval_op1_interp_op1 :
  forall op v v',
    eval_unop op v v' ->
    interp_op1 op v = Some v'.
Proof.
  inversion 1; auto.
Qed.

Lemma interp_op2_eval_op2 :
  forall op v1 v2 v',
    interp_op2 op v1 v2 = Some v' ->
    eval_binop op v1 v2 v'.
Proof.
  unfold interp_op2; intros.
  repeat break_match; subst;
    discriminate || solve_by_inversion' ee || 
  inversion H; constructor; discriminate.
Qed.

Lemma eval_op2_interp_op2 :
  forall op v1 v2 v',
    eval_binop op v1 v2 v' ->
    interp_op2 op v1 v2 = Some v'.
Proof.
  inversion 1; auto.
  - simpl. break_match; congruence; auto.
  - simpl. break_match; congruence; auto.
Qed.

Lemma interp_e_eval_e :
  forall s h e v,
    interp_e s h e = Some v ->
    eval_e s h e v.
Proof.
  induction e; simpl; intros.
  - inv H; ee.
  - ee.
  - repeat break_match; try discriminate.
    ee. apply interp_op1_eval_op1; auto.
  - repeat break_match; try discriminate.
    ee. apply interp_op2_eval_op2; auto.
  - repeat break_match; try discriminate.
    + find_inversion. eapply eval_len_s; eauto.
    + find_inversion. eapply eval_len_a; eauto.
  - repeat break_match; try discriminate.
    + find_inversion. eapply eval_idx_s; eauto.
    + eapply eval_idx_a; eauto.
Qed.

Lemma eval_e_interp_e :
  forall s h e v,
    eval_e s h e v ->
    interp_e s h e = Some v.
Proof.
  induction 1; simpl; auto.
  - repeat break_match; try discriminate.
    find_inversion. apply eval_op1_interp_op1; auto.
  - repeat break_match; try discriminate.
    repeat find_inversion. apply eval_op2_interp_op2; auto.
  - break_match; try discriminate. find_inversion.
    break_match; try discriminate. find_inversion.
    reflexivity.
  - break_match; try discriminate.
    find_inversion. reflexivity.
  - break_match; try discriminate.
    find_inversion. repeat find_rewrite.
    do 2 (break_match; try omega). auto.
  - break_match; try discriminate. find_inversion.
    break_match; try discriminate. find_inversion.
    break_match; try omega.
    break_match; try discriminate.
    find_inversion; auto.
Qed.

Lemma interps_e_evals_e :
  forall s h es vs,
    interps_e s h es = Some vs ->
    evals_e s h es vs.
Proof.
  induction es; simpl; intros.
  - find_inversion. ee.
  - repeat break_match; try discriminate.
    find_inversion. ee.
    apply interp_e_eval_e; auto.
Qed.

Lemma evals_e_interps_e :
  forall s h es vs,
    evals_e s h es vs ->
    interps_e s h es = Some vs.
Proof.
  induction 1; simpl; intros; auto.
  find_apply_lem_hyp eval_e_interp_e.
  repeat find_rewrite. auto.
Qed.


Lemma interp_s_eval_s :
  forall fuel env s h p s' h',
    interp_s fuel env s h p = Some (s', h') ->
    eval_s env s h p s' h'.
Proof.
   induction fuel.
   -intros. inversion H.
   -unfold interp_s. intros.
    repeat break_match; discriminate || simpl.
    +solve_by_inversion' ee.
    +inversion H. 
      constructor. rewrite <- H2. 
     apply interp_e_eval_e.
     assumption.
    +inversion H.
      constructor.
      apply interp_e_eval_e.
      *assumption.
      *apply interp_e_eval_e. assumption.
      *assumption.
    +inversion H. subst. ee.
      *apply interp_e_eval_e. assumption.
      *apply interp_e_eval_e. assumption.
    +fold interp_s in Heqo2. find_inversion. ee.
      *instantiate (1:=e). 
       rewrite Heqo0.
       apply locate_inv in Heqo0.
       subst. reflexivity.
      *apply interps_e_evals_e. assumption.
      *apply interp_e_eval_e. assumption.
     +find_inversion. 
        apply extcall_ok in Heqp0. 
        constructor 6 with (vs:=l0).
       *assumption.
       *apply interps_e_evals_e. assumption.
       *assumption.
     +fold interp_s in H. subst.
       constructor.
       *apply interp_e_eval_e. assumption.
       *apply IHfuel. assumption.
     +fold interp_s in H. subst.
       constructor 8.
       *apply interp_e_eval_e. assumption.
       *apply IHfuel. assumption.
     +fold interp_s in H. fold interp_s in Heqo0. subst.
       ee. apply interp_e_eval_e. assumption.
     +subst. find_inversion. constructor.
          apply interp_e_eval_e. assumption.
     +fold interp_s in H. fold interp_s in Heqo. subst.
        ee.
Qed.

Lemma interp_p_eval_p :
  forall n funcs main ret h' v',
    interp_p n (Prog funcs main ret) = Some (h', v') ->
    eval_p (Prog funcs main ret) h' v'.
Proof.
  unfold interp_p; intros.
  repeat break_match; try discriminate.
  repeat find_inversion.
  find_apply_lem_hyp interp_s_eval_s.
  find_apply_lem_hyp interp_e_eval_e.
  ee.
Qed.
