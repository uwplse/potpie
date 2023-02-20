From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.
From Coq Require Import ZArith.
Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangEval DanTrick.LogicProp DanTrick.StackPure DanTrick.StackLangTheorems DanTrick.StackSemanticsMutInd.
Require Export DanTrick.StackFrameBase.

Lemma geq_one_implies_successor :
  forall n,
    n >= 1 ->
    exists n',
      n = S n'.
Proof.
  destruct n; intros; [inversion H | ].
  exists n. reflexivity.
Qed.

Lemma geq_two_implies_succ2 :
  forall n,
    n >= 2 ->
    exists n',
      n = S (S n').
Proof.
  destruct n; intros; [inversion H | ].
  assert (n >= 1) by intuition.
  apply geq_one_implies_successor in H0.
  destruct H0. exists x.
  rewrite H0. reflexivity.
Qed.

Lemma successor_minus_one_same :
  forall n,
    S n - 1 = n.
Proof.
  induction n; intros.
  - reflexivity.
  - rewrite <- IHn. simpl. reflexivity.
Qed.


Definition frame_rule_mut_ind_theorem (P: aexp_stack -> fun_env_stk -> nat -> Prop) (P0: list aexp_stack -> fun_env_stk -> nat -> Prop) (P1: bexp_stack -> fun_env_stk -> nat -> Prop) (P2: imp_stack -> fun_env_stk -> nat -> nat -> Prop): Prop :=
  (forall (a : aexp_stack) (fenv : fun_env_stk) (frame : nat),
      aexp_frame_rule a fenv frame ->
      P a fenv frame) /\
    (forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat),
        args_frame_rule args fenv frame ->
        P0 args fenv frame) /\
    (forall (b: bexp_stack) (fenv: fun_env_stk) (frame: nat),
        bexp_frame_rule b fenv frame ->
        P1 b fenv frame) /\
    (forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
        imp_frame_rule i fenv frame frame' ->
        P2 i fenv frame frame').

Definition frame_rule_mut_ind_theorem_P (P: aexp_stack -> fun_env_stk -> nat -> Prop): forall (a: aexp_stack) (f20: fun_env_stk) (n: nat), aexp_frame_rule a f20 n -> Prop :=
    fun (a: aexp_stack) (fenv: fun_env_stk) (frame: nat) =>
    fun (_: aexp_frame_rule a fenv frame) =>
      P a fenv frame.

Definition frame_rule_mut_ind_theorem_P0 (P0: list aexp_stack -> fun_env_stk -> nat -> Prop): forall (l: list aexp_stack) (f20: fun_env_stk) (n: nat), args_frame_rule l f20 n -> Prop :=
  fun (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat) =>
  fun (_: args_frame_rule args fenv frame) =>
    P0 args fenv frame.
Definition frame_rule_mut_ind_theorem_P1 (P1: bexp_stack -> fun_env_stk -> nat -> Prop): forall (b: bexp_stack) (f20: fun_env_stk) (n: nat), bexp_frame_rule b f20 n -> Prop :=
  fun (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) =>
  fun (_: bexp_frame_rule b fenv frame) =>
    P1 b fenv frame.

Definition frame_rule_mut_ind_theorem_P2 (P2: imp_stack -> fun_env_stk -> nat -> nat -> Prop): forall (i: imp_stack) (f20: fun_env_stk) (n n0: nat), imp_frame_rule i f20 n n0 -> Prop :=
  fun (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat) =>
  fun (_: imp_frame_rule i fenv frame frame') =>
    P2 i fenv frame frame'.

Ltac frame_rule_mutual_induction P P0 P1 P2 P_def P0_def P1_def P2_def :=
  pose (frame_rule_mut_ind_theorem_P P_def) as P;
  pose (frame_rule_mut_ind_theorem_P0 P0_def) as P0;
  pose (frame_rule_mut_ind_theorem_P1 P1_def) as P1;
  pose (frame_rule_mut_ind_theorem_P2 P2_def) as P2;
  apply (stack_frame_rule_mut_ind P P0 P1 P2);
  unfold P, P0, P1, P2;
  unfold frame_rule_mut_ind_theorem_P, frame_rule_mut_ind_theorem_P0, frame_rule_mut_ind_theorem_P1, frame_rule_mut_ind_theorem_P2;
  unfold P_def, P0_def, P1_def, P2_def.


Theorem frame_implies_pure_rel_old :
  (forall (a : aexp_stack) (fenv : fun_env_stk) (frame : nat),
      aexp_frame_rule a fenv frame ->
      aexp_stack_pure_rel a fenv) /\
    (forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat),
        args_frame_rule args fenv frame ->
        args_stack_pure_rel args fenv) /\
    (forall (b: bexp_stack) (fenv: fun_env_stk) (frame: nat),
        bexp_frame_rule b fenv frame ->
        bexp_stack_pure_rel b fenv) /\
    (forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
        imp_frame_rule i fenv frame frame' ->
        never_assigns_out_of_max_stack i frame frame' fenv).
Proof.
  pose (fun (a: aexp_stack) (fenv: fun_env_stk) (frame: nat) =>
        fun (_: aexp_frame_rule a fenv frame) =>
          aexp_stack_pure_rel a fenv) as P.
  pose (fun (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat) =>
        fun (_: args_frame_rule args fenv frame) =>
          args_stack_pure_rel args fenv) as P0.
  pose (fun (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) =>
        fun (_: bexp_frame_rule b fenv frame) =>
          bexp_stack_pure_rel b fenv) as P1.
  pose (fun (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat) =>
        fun (_: imp_frame_rule i fenv frame frame') =>
          never_assigns_out_of_max_stack i frame frame' fenv) as P2.
  apply (stack_frame_rule_mut_ind P P0 P1 P2); unfold P, P0, P1, P2; intros.
  - econstructor.
  - econstructor.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor.
    + eassumption.
    + assumption.
    + rewrite Nat.add_comm. assumption.
    + assumption.
  - econstructor.
  - econstructor; assumption.
  - constructor.
  - constructor.
  - econstructor. assumption.
  - econstructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - assert (frame + 1 = S frame) by intuition.
    rewrite H.
    constructor.
  - assert (exists n, frame = S n) by (apply geq_one_implies_successor in g; assumption).
    destruct H.
    rewrite H. rewrite successor_minus_one_same. constructor.
  - econstructor; eassumption.
  - constructor; eassumption.
  - econstructor; assumption.
Qed.

Lemma aexp_frame_implies_pure' :
  forall (a: aexp_stack) (fenv: fun_env_stk) (frame: nat),
    aexp_frame_rule a fenv frame ->
    aexp_stack_pure a fenv.
Proof.
  pose proof (frame_implies_pure_rel_old) as H.
  destruct H as (AEXP & _ ).
  intros.
  eapply AEXP in H.
  eapply aexp_stack_pure_backwards in H. assumption.
Qed.

Lemma aexp_frame_implies_pure :
  forall (a: aexp_stack) (fenv: fun_env_stk) (frame: nat) (stk stk': stack) (v: nat),
    aexp_frame_rule a fenv frame ->
    aexp_stack_sem a fenv stk (stk', v) ->
    stk = stk'.
Proof.
  pose proof (aexp_frame_implies_pure') as H.
  unfold aexp_stack_pure in H.
  intros.
  eapply H; eassumption.
Qed.

Lemma bexp_frame_implies_pure' :
  forall (b: bexp_stack) (fenv: fun_env_stk) (frame: nat),
    bexp_frame_rule b fenv frame ->
    bexp_stack_pure b fenv.
Proof.
  pose proof (frame_implies_pure_rel_old) as H.
  destruct H as (_ & _ & BEXP & _).
  intros. eapply BEXP in H. pose proof (stack_pure) as H'.
  destruct H' as (_ & _ & BEXP' & _).
  eapply BEXP' in H. assumption.
Qed.

Lemma bexp_frame_implies_pure :
  forall (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) (stk stk': stack) (v: bool),
    bexp_frame_rule b fenv frame ->
    bexp_stack_sem b fenv stk (stk', v) ->
    stk = stk'.
Proof.
  pose proof (bexp_frame_implies_pure') as H.
  unfold bexp_stack_pure in H.
  intros. eapply H; eassumption.
Qed.

Lemma args_frame_implies_pure :
  forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat) (stk stk': stack) (vals: list nat),
    args_frame_rule args fenv frame ->
    args_stack_sem args fenv stk (stk', vals) ->
    stk = stk'.
Proof.
  pose proof (stack_pure) as H.
  destruct H as (_ & _ & _ & ARGS).
  intros.
  pose proof (frame_implies_pure_rel_old) as PURE.
  destruct PURE as (_ & ARGS' & _).
  eapply ARGS' in H. eapply ARGS in H; [ | eassumption ].
  eassumption.
Qed.



Lemma imp_frame_implies_never_assigns_out_of_max_stack :
  (forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
        imp_frame_rule i fenv frame frame' ->
        never_assigns_out_of_max_stack i frame frame' fenv).
Proof.
  pose proof (PURE := frame_implies_pure_rel_old).
  destruct PURE as (_ & _ & _ & IMP).
  apply IMP.
Qed.

Lemma imp_frame_implies_untouched_stack :
  forall i fenv max_stack_begin max_stack_end,
    imp_frame_rule i fenv max_stack_begin max_stack_end ->
    forall stk stk',
      imp_stack_sem i fenv stk stk' ->
      skipn max_stack_begin stk = skipn max_stack_end stk'.
Proof.
  intros.
  eapply imp_frame_implies_never_assigns_out_of_max_stack in H.
  eapply frame_stk.
  eassumption.
  assumption.
Qed.

Lemma le_ge_sym :
  forall (m n: nat),
    m <= n <-> n >= m.
Proof.
  lia.
Qed.

Lemma skipn_nil_implies_n_geq_length :
  forall A (l: list A) (n: nat),
    skipn n l = nil ->
    n >= Datatypes.length l.
Proof.
  induction l; intros.
  -  simpl. lia.
  - simpl. induction n.
    + inversion H.
    + apply le_ge_sym.
      apply Peano.le_n_S.
      apply le_ge_sym.
      apply IHl.
      simpl in H. assumption.
Qed.

Lemma imp_frame_implies_stack_decomposition :
  forall i fenv frame frame' stk stk',
    imp_frame_rule i fenv frame frame' ->
    imp_stack_sem i fenv stk stk' ->
    Datatypes.length stk >= frame ->
    Datatypes.length stk' >= frame' ->
    exists x x' y,
      (stk = x ++ y) /\ (stk' = x' ++ y) /\ Datatypes.length x = frame /\ Datatypes.length x' = frame'.
Proof.
  intros.
  apply imp_frame_implies_untouched_stack with (stk := stk) (stk' := stk') in H; [ | assumption ].
  exists (firstn frame stk).
  exists (firstn frame' stk').
  exists (skipn frame stk).
  split; [ | split; [ | split ]].
  - symmetry. apply firstn_skipn.
  - symmetry. rewrite H. apply firstn_skipn.
  - apply firstn_length_le.
    apply le_ge_sym. assumption.
  - apply firstn_length_le. apply le_ge_sym. assumption.
Qed.

Lemma frame_implies_rest_stk_untouched_le :
  forall i frame frame' fenv stk stk1 stk2,
    imp_frame_rule i fenv frame (frame + frame') ->
    frame = Datatypes.length stk1 ->
    frame' + frame <= Datatypes.length stk ->
    imp_stack_sem i fenv (stk1 ++ stk2) stk ->
    exists stk1',
      Datatypes.length stk1' = frame + frame' /\  stk = stk1' ++ stk2.
Proof.
  intros. rewrite Nat.add_comm.
  pose proof (imp_frame_implies_never_assigns_out_of_max_stack _ _ _ _ H).
  eapply imp_stack_pure_stack_decomposition; eauto.
  + rewrite Nat.add_comm. apply H3.
  + eapply imp_frame_implies_untouched_stack; eauto.
    rewrite Nat.add_comm. auto.
Qed.

Lemma same_after_popping_calculate_length :
  forall (stk stk': stack) (n: nat),
    same_after_popping stk' stk n ->
    Datatypes.length stk' = Datatypes.length stk - n.
Proof.
  intros stk stk' n. revert stk stk'.
  dependent induction n; intros; invs H.
  - auto with arith.
  - simpl. apply IHn. auto.
Qed.

Lemma stack_mutated_at_index_preserves_length :
  forall stk stk' k c,
    stack_mutated_at_index stk' k c stk ->
    Datatypes.length stk' = Datatypes.length stk.
Proof.
  intros.
  invs H.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Local Definition P_stack_length_same (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack) : Prop :=
  forall frame frame',
    imp_frame_rule i fenv frame frame' ->
    Datatypes.length stk - frame = Datatypes.length stk' - frame'.

Local Definition P0_stack_length_same (a: aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'n: stack * nat) : Prop :=
  forall stk' n frame,
    stk'n = (stk', n) ->
    aexp_frame_rule a fenv frame ->
    Datatypes.length stk = Datatypes.length stk'.

Local Definition P1_stack_length_same (b: bexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'v: stack * bool) : Prop :=
  forall stk' v frame,
    stk'v = (stk', v) ->
    bexp_frame_rule b fenv frame ->
    Datatypes.length stk = Datatypes.length stk'.

Local Definition P2_stack_length_same (args: list aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'vals: stack * (list nat)) : Prop :=
  forall stk' vals frame,
    stk'vals = (stk', vals) ->
    args_frame_rule args fenv frame ->
    Datatypes.length stk = Datatypes.length stk'.


Lemma n_plus_one_eq_n_false:
  forall (P: Prop) (n: nat),
    n + 1 = n -> P.
Proof.
  induction n; intros.
  - invs H.
  - invs H. eapply IHn in H1. assumption.
Qed.


      
Lemma stack_length_same :
  stack_sem_mut_ind_theorem P_stack_length_same P0_stack_length_same P1_stack_length_same P2_stack_length_same.
Proof.
  stack_sem_mutual_induction P P0 P1 P2 P_stack_length_same P0_stack_length_same P1_stack_length_same P2_stack_length_same; intros.
  - invs H. reflexivity.
  - invs H0. eapply stack_mutated_at_index_preserves_length in s. rewrite s.
    assert (stk = stk') by (eapply aexp_frame_implies_pure; [ eapply H8 | eassumption ]). subst. reflexivity.
  - invs H. rewrite Nat.add_1_r. simpl. reflexivity.
  - invs H. simpl. destruct frame; [ invs H0 | ].
    simpl. rewrite Nat.sub_0_r.  reflexivity.
  - invs H1.
    eapply H in H4. eapply H0 in H8. rewrite H8 in H4. assumption.
  - invs H1. specialize (H stk' true).
    eapply H in H5; [ | reflexivity ]. rewrite H5. clear H5. eapply H0 in H9. eassumption.
  - invs H1. specialize (H stk' false). eapply H in H5; [ | reflexivity ]. rewrite H5. clear H5. eapply H0 in H10. eassumption.
  - invs H0. specialize (H stk' false). eapply H in H3; [ | reflexivity ].
    rewrite H3. reflexivity.
  - invs H2. specialize (H stk1 true). eapply H in H5; [ | reflexivity ]. rewrite H5 in *. clear H5.
    eapply H0 in H9. rewrite H9 in *. clear H9. eapply H1 in H2. assumption.
  - invs H. reflexivity.
  - invs H. reflexivity.
  - invs H1. invs H2. eapply H in H5; [ | reflexivity]. eapply H0 in H8; [ | reflexivity ]. rewrite H5. rewrite H8. reflexivity.
  - invs H1. invs H2. eapply H in H5; [ | reflexivity ]. eapply H0 in H8; [ | reflexivity ]. rewrite H5. rewrite H8. reflexivity.
  - invc H2. invs H3. eapply H in H5; [ | eauto ]. eapply H0 in H7. eapply H1 in H10; [ | eauto ]. rewrite H5 in *. clear H5. rewrite H10 in *. clear H10. eapply args_stack_sem_preserves_length in a. rewrite app_length in H7. rewrite e3 in H7. rewrite <- a in H7. rewrite minus_plus in H7.
    eapply same_after_popping_calculate_length in s.
    rewrite e3 in s.
    rewrite <- s in H7. assumption.
  - invs H. reflexivity.
  - invs H. reflexivity.
  - invs H0. invs H1. eapply H in H3; [ | eauto ]. assumption.
  - invs H1. invs H2. eapply H in H5; [ | eauto ]. eapply H0 in H8; [ | eauto ]. rewrite H5. rewrite H8. reflexivity.
  - invc H1. invs H2. eapply H in H4; [ | eauto ]. eapply H0 in H7; [ | eauto ]. rewrite H4. rewrite H7. reflexivity.
  - invc H1. invs H2. eapply H in H4; [ | eauto ]. eapply H0 in H7; [ | eauto ]. rewrite H4. rewrite H7. reflexivity.
  - invc H1. invs H2. eapply H in H4; [ | eauto ]. eapply H0 in H7; [ | eauto ]. rewrite H4. rewrite H7. reflexivity.
  - invs H. reflexivity.
  - invc H1. invs H2. eapply H in H4; [ | eauto ]. eapply H0 in H7; [ | eauto]. rewrite H4. rewrite H7. reflexivity.
Qed.

Lemma imp_stack_len_same :
   (forall (i : imp_stack) (fenv : fun_env_stk) (stk stk' : stack),
   imp_stack_sem i fenv stk stk' ->
   forall frame frame' : nat,
   imp_frame_rule i fenv frame frame' ->
   Datatypes.length stk - frame = Datatypes.length stk' - frame').
Proof.
  pose proof (stack_length_same).
  destruct H. eapply H.
Qed.

Lemma aexp_stack_len_same :
  (forall (a : aexp_stack) (fenv : fun_env_stk) (stk : stack)
     (stk'n : stack * nat),
   aexp_stack_sem a fenv stk stk'n ->
   forall (stk' : stack) (n frame : nat),
   stk'n = (stk', n) ->
   aexp_frame_rule a fenv frame ->
   Datatypes.length stk = Datatypes.length stk').
Proof.
  pose proof (stack_length_same).
  destruct H. destruct H0. eapply H0.
Qed.

Lemma bexp_stack_len_same :
  (forall (b : bexp_stack) (fenv : fun_env_stk) (stk : stack)
     (stk'v : stack * bool),
   bexp_stack_sem b fenv stk stk'v ->
   forall (stk' : stack) (v : bool) (frame : nat),
   stk'v = (stk', v) ->
   bexp_frame_rule b fenv frame ->
   Datatypes.length stk = Datatypes.length stk').
Proof.
  pose proof (stack_length_same).
  destruct H. destruct H0. destruct H1. eapply H1.
Qed.

Lemma args_stack_len_same :
  (forall (args : list aexp_stack) (fenv : fun_env_stk) 
     (stk : stack) (stk'vals : stack * list nat),
   args_stack_sem args fenv stk stk'vals ->
   forall (stk' : stack) (vals : list nat) (frame : nat),
   stk'vals = (stk', vals) ->
   args_frame_rule args fenv frame ->
   Datatypes.length stk = Datatypes.length stk').
Proof.
  pose proof (stack_length_same).
  destruct H. destruct H0. destruct H1. unfold P_stack_length_same in H2. eapply H2.
Qed.

Section frame_relative_section.


  Definition int_diff_nats (n1 n2: nat): Z :=
    ((Z.of_nat n1) - (Z.of_nat n2))%Z.
  
  Lemma neq_pred :
    forall frame,
      frame >= 1 ->
      frame <> frame - 1.
  Proof.
    destruct frame; intros.
    - invs H.
    - rewrite Nat.sub_succ. rewrite Nat.sub_0_r. unfold not. intros.
      symmetry in H0. eapply Nat.neq_succ_diag_r in H0. assumption.
  Qed.

  Lemma frame_relative :
    forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
      imp_frame_rule i fenv frame frame' ->
      forall (f f': nat),
        imp_frame_rule i fenv f f' ->
        int_diff_nats f' f = int_diff_nats frame' frame.
  Proof.
    unfold int_diff_nats. induction i; intros.
    - invs H0. invs H. lia.
    - invs H. invs H0. lia.
    - invs H. invs H0. lia.
    - invs H. invs H0. lia.
    - invs H. invs H0. eapply IHi1 in H3; [ | eapply H4 ].
      eapply IHi2 in H7; [ | eapply H9 ]. eapply Z.sub_move_r in H7. eapply Z.sub_move_r in H3.
      rewrite <- H3 in H7. rewrite Z.opp_sub_distr in H7. rewrite Z.opp_sub_distr in H7. rewrite Z.add_opp_r in H7.
      rewrite Z.add_opp_l in H7.
      repeat rewrite Z.sub_sub_distr in H7.
      rewrite <- Z.sub_add_distr in H7.
      rewrite (Z.add_comm (Z.of_nat frame'0) (Z.of_nat frame)) in H7.
      rewrite Z.sub_add_distr in H7.
      rewrite Z.sub_add in H7.
      symmetry in H7.
      eapply Z.sub_move_r in H7. assumption.
    - invs H. invs H0. eapply IHi1 in H8; [ | eapply H11 ].
      symmetry in H8. assumption.
    - invs H. invs H0. repeat rewrite Z.sub_diag. reflexivity.
  Qed.

  Lemma exists_nat_pos :
    forall (p: positive),
    exists (n: nat),
      Z.pos p = Z.of_nat n.
  Proof.
    destruct p.
    - exists (Z.to_nat (Z.pos (p~1))).
      erewrite Z2Nat.id.
      reflexivity.
      lia.
    - exists (Z.to_nat (Z.pos (p~0))).
      erewrite Z2Nat.id.
      reflexivity.
      lia.
    - exists 1. simpl. reflexivity.
  Qed.

  Lemma frame_relative'' :
    forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
      imp_frame_rule i fenv frame frame' ->
      forall (f f': nat),
        imp_frame_rule i fenv f f' ->
        frame <= frame' -> f <= f'.
  Proof.
    intros. pose proof (frame_relative).
    specialize (H2 i fenv frame frame' H f f' H0).
    destruct (int_diff_nats f' f) eqn:?; unfold int_diff_nats in *.
    - 
      symmetry in H2.
      eapply Zminus_eq in H2.
      eapply Zminus_eq in Heqz.
      pose proof (f_equal Z.to_nat Heqz).
      repeat rewrite Nat2Z.id in H3.
      lia.
    - eapply Z.sub_move_r in Heqz.
      pose proof (exists_nat_pos p).
      destruct H3. rewrite H3 in Heqz.
      rewrite <- Nat2Z.inj_add in Heqz.
      pose proof (f_equal Z.to_nat Heqz). repeat rewrite Nat2Z.id in H4.
      rewrite H4. rewrite Nat.add_comm. lia.
    - destruct f', f.
      simpl in Heqz. invs Heqz. simpl in Heqz.
      assert (Z.of_nat frame <= Z.of_nat frame')%Z.
      lia.
      assert (0 <= Z.of_nat frame' - Z.of_nat frame)%Z by lia.
      eapply Z_of_nat_complete in H4. destruct H4.
      rewrite H4 in H2. unfold Z.of_nat in H2. destruct x.
      invs H2. invs H2.
      lia. pose proof (Zlt_neg_0 p).
      rewrite <- Heqz in H3. pose proof Z.lt_sub_0.
      specialize (H4 (Z.of_nat (S f')) (Z.of_nat (S f))).
      apply H4 in H3. lia.
  Qed.

  Lemma frame_relative_leq :
    forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
      imp_frame_rule i fenv frame frame' ->
      forall (f f': nat),
        imp_frame_rule i fenv f f' ->
        frame >= frame' -> f >= f'.
  Proof.
    intros. pose proof (frame_relative).
    specialize (H2 i fenv frame frame' H f f' H0).
    destruct (int_diff_nats f' f) eqn:?; unfold int_diff_nats in *.
    - symmetry in H2.
      eapply Zminus_eq in H2.
      eapply Zminus_eq in Heqz.
      pose proof (f_equal Z.to_nat Heqz).
      repeat rewrite Nat2Z.id in H3.
      lia.
    - assert (Z.of_nat frame >= Z.of_nat frame')%Z by lia.
      assert (0 >= Z.of_nat frame' - Z.of_nat frame)%Z by lia.
      pose proof (Z_of_nat_complete).
      specialize (H5 (Z.pos p)).
      assert (0 <= Z.pos p)%Z by lia.
      pose proof (H7 := H6).
      apply H5 in H6.
      destruct H6. rewrite H2 in H6.
      pose proof Z.le_sub_0.
      specialize (H8 (Z.of_nat frame') (Z.of_nat frame)).
      assert (Z.of_nat frame' - Z.of_nat frame <= 0)%Z by lia.
      apply H8 in H9.
      assert (Z.of_nat frame >= Z.of_nat frame')%Z by lia.
      assert (Z.of_nat frame' = Z.of_nat frame)%Z by lia.
      rewrite H11 in H2. rewrite Z.sub_diag in H2. invs H2.
    - pose proof (Zlt_neg_0).
      specialize (H3 p).
      rewrite <- Heqz in H3.
      assert (Z.of_nat f' < Z.of_nat f)%Z by lia.
      lia.
  Qed.

End frame_relative_section.

Local Definition P_frame_expansion (a: aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  forall frame',
    frame <= frame' ->
    aexp_frame_rule a fenv frame'.

Local Definition P0_frame_expansion (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  forall frame',
    frame <= frame' ->
    args_frame_rule args fenv frame'.

Local Definition P1_frame_expansion (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) : Prop :=
  forall frame',
    frame <= frame' ->
    bexp_frame_rule b fenv frame'.

Local Definition P2_frame_expansion (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat): Prop :=
  forall frame'',
    frame <= frame'' ->
    imp_frame_rule i fenv frame'' (frame'' + frame' - frame).

Lemma frame_expansion :
  frame_rule_mut_ind_theorem P_frame_expansion P0_frame_expansion P1_frame_expansion P2_frame_expansion.
Proof.
  frame_rule_mutual_induction P P0 P1 P2 P_frame_expansion P0_frame_expansion P1_frame_expansion P2_frame_expansion; intros.
  - constructor.
  - constructor; lia.
  - constructor.
    + eapply H. eassumption.
    + eapply H0. eassumption.
  - constructor.
    + apply H. assumption.
    + apply H0. assumption.
  - econstructor.
    + apply H. assumption.
    + eassumption.
    + eassumption.
    + eassumption.
  - constructor.
  - constructor; [ eapply H | eapply H0 ]; eassumption.
  - econstructor.
  - constructor.
  - constructor. eapply H. assumption.
  - constructor; [ eapply H | eapply H0 ]; eassumption.
  - constructor; [ eapply H | eapply H0 ]; eassumption.
  - constructor; [ eapply H | eapply H0 ]; eassumption.
  - constructor; [ eapply H | eapply H0 ]; eassumption.
  - rewrite Nat.add_sub. constructor.
  - rewrite Nat.add_sub. constructor. lia. lia. eapply H. assumption.
  - rewrite <- Nat.add_sub_assoc.
    rewrite minus_plus. constructor. lia.
  - rewrite Nat.add_sub_assoc.
    rewrite Nat.add_sub_swap.
    rewrite <- Nat.add_sub_assoc.
    rewrite Nat.sub_diag. rewrite Nat.add_0_r. econstructor.
    lia. lia. lia. lia.
  - econstructor.
    + eapply H. eassumption.
    + assert (frame''0 + frame' - frame + frame'' - frame' = frame''0 + frame'' - frame).
      rewrite Nat.add_sub_swap.
      rewrite Nat.add_sub_swap.
      pose proof plus_minus.
      pose proof minus_plus.
      remember (frame''0 - frame) as sth.
      rewrite (Nat.add_comm sth frame').
      rewrite minus_plus. rewrite Heqsth. rewrite Nat.add_sub_swap. reflexivity.
      auto. auto.
      assert (frame''0 - frame >= 0) by lia.
      rewrite Nat.add_sub_swap.
      rewrite Nat.add_comm. lia. auto.  rewrite <- H2. eapply H0.
      rewrite Nat.add_sub_swap.
      rewrite Nat.add_comm. lia. auto.
  - constructor.
    + eapply H. assumption.
    + eapply H0. assumption.
    + eapply H1. assumption.
  - rewrite Nat.add_comm. rewrite minus_plus. econstructor.
    + eapply H. assumption.
    + specialize (H0 frame''). eapply H0 in H1. rewrite Nat.add_comm in H1. rewrite minus_plus in H1. assumption.
Qed.

Lemma aexp_frame_expansion :
  (forall (a : aexp_stack) (fenv : fun_env_stk) (frame : nat),
   aexp_frame_rule a fenv frame ->
   forall frame' : nat, frame <= frame' -> aexp_frame_rule a fenv frame').
Proof.
  pose proof frame_expansion. destruct H. apply H.
Qed.

Lemma args_frame_expansion :
  (forall (args : list aexp_stack) (fenv : fun_env_stk) (frame : nat),
   args_frame_rule args fenv frame ->
   forall frame' : nat,
     frame <= frame' -> args_frame_rule args fenv frame').
Proof.
  pose proof frame_expansion. destruct H. destruct H0. apply H0.
Qed.

Lemma bexp_frame_expansion :
  (forall (b : bexp_stack) (fenv : fun_env_stk) (frame : nat),
   bexp_frame_rule b fenv frame ->
   forall frame' : nat, frame <= frame' -> bexp_frame_rule b fenv frame').
Proof.
  pose proof frame_expansion. destruct H. destruct H0. destruct H1. apply H1.
Qed.

Lemma imp_frame_expansion :
  (forall (i : imp_stack) (fenv : fun_env_stk) (frame frame' : nat),
   imp_frame_rule i fenv frame frame' ->
   forall frame'' : nat,
   frame <= frame'' ->
   imp_frame_rule i fenv frame'' (frame'' + frame' - frame)).
Proof.
  pose proof frame_expansion. destruct H. destruct H0. destruct H1. apply H2.
Qed.

Lemma frame_diff_equal :
  forall (i : imp_stack) (fenv : fun_env_stk) (frame frame' : nat),
    imp_frame_rule i fenv frame frame' ->
    forall f f' : nat,
      imp_frame_rule i fenv f f' ->
      (frame' >= frame /\ frame' - frame = f' - f) \/ (frame' <= frame /\ frame - frame' = f - f').
Proof.
  intros.
  pose proof (frame_relative).
  pose proof le_ge_dec.
  specialize (H2 frame' frame).
  specialize (H1 i fenv frame frame' H f f' H0).
  destruct H2.
  - right. split; [ assumption | ].
    unfold int_diff_nats in H1.
    symmetry in H1.
    lia.
  - left. split; [ assumption | ].
    unfold int_diff_nats in H1. lia.
Qed.

Lemma frame_diff_equal' :
  forall (i : imp_stack) (fenv : fun_env_stk) (frame frame' : nat),
    imp_frame_rule i fenv frame frame' ->
    forall f f' : nat,
      imp_frame_rule i fenv f f' ->
      (frame' >= frame /\
         exists diff,
           frame' = frame + diff /\ f' = f + diff) \/
        (frame' <= frame /\
           exists diff,
             frame' + diff = frame /\ f' + diff = f).
Proof.
  intros.
  pose proof (frame_diff_equal i fenv frame frame' H f f' H0).
  destruct H1.
  - left. destruct H1. split.
    + assumption.
    + exists (frame' - frame).
      split.
      * rewrite Nat.add_sub_assoc; [ | assumption].
        rewrite minus_plus. reflexivity.
      * assert (frame' = f' - f + frame).
        lia.
        rewrite H3.
        rewrite Nat.add_sub. rewrite Nat.add_sub_assoc.
        rewrite minus_plus. reflexivity.
        eapply frame_relative''.
        eapply H. eassumption. assumption.
  - right. destruct H1. split. assumption.
    exists (frame - frame'). split.
    + rewrite Nat.add_sub_assoc; [ | assumption ].
      rewrite minus_plus. reflexivity.
    + rewrite Nat.add_sub_assoc; [ | assumption ].
      assert (frame = f - f' + frame') by lia.
      rewrite H3. rewrite <- Nat.add_sub_assoc.
      * rewrite Nat.add_sub. rewrite Nat.add_sub_assoc.
        rewrite minus_plus. reflexivity.
        eapply frame_relative_leq.
        eapply H. eapply H0. eassumption.
      * rewrite <- H3. auto.
Qed.


Lemma frame_is_enough :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
    imp_frame_rule i fenv frame frame' ->
    frame' <= frame ->
    forall f f': nat,
      imp_frame_rule i fenv f f' ->
      f >= frame - frame'.
Proof.
  intros.
  pose proof (frame_diff_equal).
  specialize (H2 i fenv frame frame' H f f' H1).
  destruct H2.
  - destruct H2.
    assert (frame' = frame) by lia.
    rewrite H4. rewrite Nat.sub_diag. lia.
  - destruct H2.
    rewrite H3. lia.
Qed.

Lemma frames_equal :
  forall (i : imp_stack) (fenv : fun_env_stk) (frame frame' : nat),
    imp_frame_rule i fenv frame frame' ->
    forall f f' : nat,
      imp_frame_rule i fenv f f' ->
      frame = frame' ->
      f = f'.
Proof.
  intros.
  pose proof frame_relative''.
  pose proof frame_relative_leq.
  specialize (H2 i fenv frame frame' H f f' H0).
  specialize (H3 i fenv frame frame' H f f' H0).
  assert (frame <= frame') by lia.
  assert (frame >= frame') by lia.
  specialize (H2 H4).
  specialize (H3 H5).
  lia.
Qed.

Lemma frame_deterministic :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame' frame'': nat),
    imp_frame_rule i fenv frame frame' ->
    imp_frame_rule i fenv frame frame'' ->
    frame' = frame''.
Proof.
  induction i; intros.
  - invs H. invs H0. reflexivity.
  - invs H. invs H0. reflexivity.
  - invs H. invs H0. reflexivity.
  - invs H. invs H0. reflexivity.
  - invs H. invs H0. specialize (IHi1 fenv frame frame'0 frame'1 H3 H4).
    subst frame'0. clear H4.
    specialize (IHi2 fenv frame'1 frame' frame'' H7 H9). subst frame'. reflexivity.
  - invs H. invs H0. specialize (IHi1 fenv frame frame' frame'' H8 H11).
    assumption.
  - invs H. invs H0. reflexivity.
Qed.

Lemma frame_deterministic' :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame' frame'': nat),
    imp_frame_rule i fenv frame frame'' ->
    imp_frame_rule i fenv frame' frame'' ->
    frame = frame'.
Proof.
  induction i; intros; invs H; invs H0.
  - reflexivity.
  - reflexivity.
  - repeat rewrite Nat.add_1_r in H1. invs H1. reflexivity.
  - destruct frame', frame; invs H1; invs H3.
    reflexivity.
    simpl in H2. rewrite Nat.sub_0_r in H2. subst. reflexivity.
    rewrite Nat.sub_succ in H2. rewrite Nat.sub_succ in H2. simpl in H2. rewrite Nat.sub_0_r in H2. symmetry in H2. subst. reflexivity.
    repeat rewrite Nat.sub_succ in H2. repeat rewrite Nat.sub_0_r in H2. subst. reflexivity.
  - specialize (IHi2 fenv frame'0 frame'1 frame'' H7 H9). subst.
    specialize (IHi1 fenv frame frame' frame'1 H3 H4). subst. reflexivity.
  - specialize (IHi1 fenv frame frame' frame'' H8 H11). subst. reflexivity.
  - reflexivity.
Qed.

Lemma frame_relative''' :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
    imp_frame_rule i fenv frame frame' ->
    forall (f f': nat),
      imp_frame_rule i fenv f f' ->
      (frame' >= frame /\ f' = f + frame' - frame) \/
        (frame' <= frame /\ f' + frame - frame' = f).
Proof.
  intros. pose proof (frame_diff_equal).
  specialize (H1 _ _ _ _ H _ _ H0).
  destruct H1.
  - left. destruct H1. assert (frame' = f' - f + frame) by lia.
    rewrite H3.
    split.
    + rewrite <- H3. auto.
    + rewrite <- Nat.add_sub_assoc.
      * rewrite Nat.add_sub. rewrite Nat.add_sub_assoc.
        rewrite minus_plus.
        auto.
        pose proof (frame_relative'').
        eapply H4. eapply H. eapply H0. auto.
      * rewrite <- H3. auto.
  - right. destruct H1. assert (frame = f - f' + frame') by lia.
    split.
    + auto.
    + rewrite H3. rewrite <- Nat.add_sub_assoc.
      * rewrite Nat.add_sub. rewrite Nat.add_sub_assoc. rewrite minus_plus. reflexivity.
        pose proof (frame_relative_leq).
        eapply H4. eapply H. auto. auto.
      * rewrite <- H3. auto.
Qed.

Lemma frame_diff_cant_be_bigger_than_start :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
    imp_frame_rule i fenv frame frame' ->
    forall (f f': nat),
      imp_frame_rule i fenv f f' ->
      (frame' >= frame /\ f' >= f) \/
        (frame' < frame /\ frame - frame' <= f).
Proof.
  intros.
  pose proof (frame_relative''').
  pose proof (le_gt_dec frame frame').
  specialize (H1 _ _ _ _ H _ _ H0).
  destruct H2.
  - left. split. auto.
    assert (f <= f').
    eapply frame_relative''. eapply H. assumption. assumption. assumption.
  - right. split. auto.
    destruct H1.
    + destruct H1. assert (frame <= frame') by lia.
      eapply le_not_gt in H3. congruence.
    + destruct H1. lia.
Qed.

Lemma frame_relative' :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
    imp_frame_rule i fenv frame frame' ->
    forall (f f': nat),
      imp_frame_rule i fenv f f' ->
      imp_frame_rule i fenv f (f + frame' - frame).
Proof.
  induction i; intros.
  - invs H. invs H0. rewrite Nat.add_comm. rewrite minus_plus. constructor.
  - invs H. invs H0. rewrite Nat.add_comm. rewrite minus_plus. constructor; assumption.
  - invs H0. invs H. rewrite Nat.add_assoc.
    assert (f + frame + 1 - frame = f + 1) by lia.
    rewrite H1.
    assumption.
  - invs H0. invs H. rewrite Nat.add_sub_assoc. assert (f + frame - 1 - frame = f - 1) by lia.
    rewrite H3.
    assumption. assumption.
  - pose proof (frame_relative''').
    specialize (H1 (Seq_Stk i1 i2) fenv frame frame' H f f' H0).
    destruct H1.
    + destruct H1.  rewrite H2 in H0. assumption.
    + destruct H1. rewrite <- H2.
      rewrite Nat.sub_add.
      rewrite Nat.add_sub.
      rewrite <- H2 in H0. assumption.
      assert (f' + frame = f + frame') by lia.
      lia.
  - invs H. invs H0. specialize (IHi1 fenv frame frame' H8 f f' H11).
    specialize (IHi2 fenv frame frame' H9 f f' H12). econstructor; assumption.
  - invs H. rewrite Nat.add_sub. invs H0. assumption.
Qed.

