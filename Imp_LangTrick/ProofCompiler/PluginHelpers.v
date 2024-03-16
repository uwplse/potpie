From Coq Require Import List String Arith.
From Imp_LangTrick Require Import StackLanguage StackLogic StackLogicBase StackLogicGrammar StkHoareTree StackFrameReflection.

Theorem empty_facts_valid :
  fact_env_valid nil init_fenv_stk.
Proof.
  unfold fact_env_valid.
  intros. inversion H.
Defined.

Lemma increase_absstack_okay :
  forall (size: nat) (m m': MetavarPred) (fenv: fun_env_stk),
    aimpstk (AbsAnd (BaseState (AbsStkSize size) m') (BaseState AbsStkTrue m))
    (AbsAnd (BaseState (AbsStkSize size) m') (BaseState (AbsStkSize size) m)) fenv.
Proof.
  intros. unfold aimpstk. intros.
  invs H. invs H2. invs H5.
  econstructor; econstructor; eassumption.
Defined.

Local Open Scope nat_scope. 
Fixpoint maximum_stack_size_implied (A: AbsState): nat :=
  match A with
  | BaseState s m =>
      match s with
      | AbsStkTrue => 0
      | AbsStkSize k => k
      end
  | AbsAnd a1 a2 =>
      Nat.max (maximum_stack_size_implied a1)
              (maximum_stack_size_implied a2)
  | AbsOr a1 a2 =>
      Nat.min (maximum_stack_size_implied a1)
              (maximum_stack_size_implied a2)
  end.

Lemma absand_distributive :
  forall (a1 a2 a3: AbsState) (fenv: fun_env_stk) stk,
    absstate_match_rel (AbsAnd (AbsAnd a1 a2) a3) fenv stk <->
      absstate_match_rel (AbsAnd (AbsAnd a1 a3) (AbsAnd a2 a3)) fenv stk.
Proof.
  intros. split; intros.
  - invs H. invs H2. econstructor; econstructor; eauto.
  - invs H. invs H2. invs H5. econstructor; [ econstructor | ]; eauto.
Defined.

From Coq Require Import Psatz.

Lemma absstack_max_is_min_stk_size :
  forall (a: AbsState) (fenv: fun_env_stk) stk,
    absstate_match_rel a fenv stk ->
    maximum_stack_size_implied a <= Datatypes.length stk.
Proof.
  induction a; simpl; intros.
  - invs H. invs H2. lia. lia.
  - invs H. eapply IHa1 in H2. eapply IHa2 in H5. lia.
  - invs H.
    + eapply IHa1 in H4. lia.
    + eapply IHa2 in H4. lia.
Defined.

Lemma increase_absstack_okay' :
  forall (size: nat) (a: AbsState) (m: MetavarPred) (fenv: fun_env_stk),
    size <= maximum_stack_size_implied a ->
    aimpstk (AbsAnd a (BaseState AbsStkTrue m))
            (AbsAnd a (BaseState (AbsStkSize size) m))
            fenv.
Proof.
  intros size a. revert size. induction a; unfold aimpstk; intros.
  - simpl in H. destruct s.
    + invs H. invs H0. invs H3. invs H6. econstructor; eauto.
      econstructor. econstructor. Psatz.lia.
      eassumption.
    + invs H0. invs H3. invs H6. econstructor; eauto.
      econstructor. invs H4. econstructor. Psatz.lia.
      eassumption.
  - simpl in H. invs H0. invs H3. invs H6.
    eapply absand_distributive.
    econstructor.
    + econstructor.
      eassumption.
      econstructor.
      eapply absstack_max_is_min_stk_size in H3. simpl in H3. econstructor. lia.
      eassumption.
    + eapply absstack_max_is_min_stk_size in H3. simpl in H3. econstructor; eauto.
      econstructor; eauto. econstructor; lia.
  - simpl in H. invs H0.
    + econstructor; eauto.
      invs H6. econstructor.
      * eapply absstack_max_is_min_stk_size in H3. simpl in H3. econstructor.
        lia.
      * eassumption.
Defined.

Lemma fact_env_valid_means_aimpstk :
  forall P Q n fact_env fenv,
    nth_error fact_env n = Some (P, Q) ->
    fact_env_valid fact_env fenv ->
    aimpstk P Q fenv.
Proof.
  intros P Q  n fact_env. revert P Q n.
  induction fact_env; intros.
  - rewrite nth_error_nil_None in H. invs H.
  - destruct n.
    + simpl in H. invs H.
      unfold fact_env_valid in H0. specialize (H0 P Q (or_introl (eq_refl (P, Q)))).
      eauto.
    + simpl in H. eapply IHfact_env; eauto.
      unfold fact_env_valid in *.
      intros. eapply H0. right. eauto.
Qed.

             
