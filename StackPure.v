From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangEval DanTrick.LogicProp DanTrick.StackLangTheorems.
Scheme Equality for list.

Definition aexp_stack_pure (a: aexp_stack) (fenv: fun_env_stk): Prop :=
  forall stk stk' n,
    aexp_stack_sem a fenv stk (stk', n) ->
    stk = stk'.

Definition bexp_stack_pure (b: bexp_stack) (fenv: fun_env_stk): Prop :=
  forall stk stk' v,
    bexp_stack_sem b fenv stk (stk', v) ->
    stk = stk'.





Inductive never_assigns_out_of_max_stack: imp_stack -> nat -> nat -> fun_env_stk -> Prop :=
| NASkip :
  forall n fenv,
    never_assigns_out_of_max_stack (Skip_Stk) n n fenv
| NAAssign :
  forall n fenv k a,
    k <= n ->
    aexp_stack_pure_rel a fenv ->
    never_assigns_out_of_max_stack (Assign_Stk k a) n n fenv
| NAPush :
  forall n fenv,
    never_assigns_out_of_max_stack Push_Stk n (S n) fenv
| NAPop :
  forall n fenv,
    never_assigns_out_of_max_stack Pop_Stk (S n) n fenv
| NAIf :
  forall n n' fenv b then_branch else_branch,
    bexp_stack_pure_rel b fenv ->
    never_assigns_out_of_max_stack then_branch n n' fenv ->
    never_assigns_out_of_max_stack else_branch n n' fenv ->
    never_assigns_out_of_max_stack (If_Stk b then_branch else_branch) n n' fenv
| NASeq :
  forall n n' n'' fenv i1 i2,
    never_assigns_out_of_max_stack i1 n n' fenv ->
    never_assigns_out_of_max_stack i2 n' n'' fenv ->
    never_assigns_out_of_max_stack (Seq_Stk i1 i2) n n'' fenv
| NAWhile :
  forall n fenv b loop_body,
    bexp_stack_pure_rel b fenv ->
    never_assigns_out_of_max_stack loop_body n n fenv ->
    never_assigns_out_of_max_stack (While_Stk b loop_body) n n fenv
with bexp_stack_pure_rel: bexp_stack -> fun_env_stk -> Prop :=
| PureTrueStk :
  forall fenv,
    bexp_stack_pure_rel True_Stk fenv
| PureFalseStk :
  forall fenv,
    bexp_stack_pure_rel False_Stk fenv
| PureNegStk :
  forall fenv b,
    bexp_stack_pure_rel b fenv ->
    bexp_stack_pure_rel (Neg_Stk b) fenv
| PureAndStk :
  forall fenv b1 b2,
    bexp_stack_pure_rel b1 fenv ->
    bexp_stack_pure_rel b2 fenv ->
    bexp_stack_pure_rel (And_Stk b1 b2) fenv
| PureOrStk :
  forall fenv b1 b2,
    bexp_stack_pure_rel b1 fenv ->
    bexp_stack_pure_rel b2 fenv ->
    bexp_stack_pure_rel (Or_Stk b1 b2) fenv
| PureLeqStk :
  forall fenv a1 a2,
    aexp_stack_pure_rel a1 fenv ->
    aexp_stack_pure_rel a2 fenv ->
    bexp_stack_pure_rel (Leq_Stk a1 a2) fenv
| PureEqStk :
  forall fenv a1 a2,
    aexp_stack_pure_rel a1 fenv ->
    aexp_stack_pure_rel a2 fenv ->
    bexp_stack_pure_rel (Eq_Stk a1 a2) fenv
with aexp_stack_pure_rel: aexp_stack -> fun_env_stk -> Prop :=
| PureConstStk :
  forall fenv n,
    aexp_stack_pure_rel (Const_Stk n) fenv
| PureVarStk :
  forall fenv k,
    aexp_stack_pure_rel (Var_Stk k) fenv
| PurePlusStk :
  forall fenv a1 a2,
    aexp_stack_pure_rel a1 fenv ->
    aexp_stack_pure_rel a2 fenv ->
    aexp_stack_pure_rel (a1 +s a2) fenv
| PureMinusStk :
  forall fenv a1 a2,
    aexp_stack_pure_rel a1 fenv ->
    aexp_stack_pure_rel a2 fenv ->
    aexp_stack_pure_rel (a1 -s a2) fenv
| PureAppStk :
  forall fenv func f args,
    func = fenv f ->
    args_stack_pure_rel args fenv ->
    never_assigns_out_of_max_stack (Body func) (Args func) ((Return_pop func) + (Args func)) fenv ->
    aexp_stack_pure_rel (Return_expr func) fenv ->
    aexp_stack_pure_rel (App_Stk f args) fenv
with args_stack_pure_rel : list aexp_stack -> fun_env_stk -> Prop :=
| PureArgsNil :
  forall fenv,
    args_stack_pure_rel nil fenv
| PureArgsCons :
  forall fenv arg args,
    aexp_stack_pure_rel arg fenv ->
    args_stack_pure_rel args fenv ->
    args_stack_pure_rel (arg :: args) fenv.

Scheme never_assigns_ind := Induction for never_assigns_out_of_max_stack Sort Prop
with aexp_stack_pure_ind := Induction for aexp_stack_pure_rel Sort Prop
with bexp_stack_pure_ind := Induction for bexp_stack_pure_rel Sort Prop
with args_stack_pure_ind := Induction for args_stack_pure_rel Sort Prop.

Combined Scheme pure_stack_mut_ind from never_assigns_ind, aexp_stack_pure_ind, bexp_stack_pure_ind, args_stack_pure_ind.
                                                             




Ltac smart_unfold :=
  match goal with
  | [ |- aexp_stack_pure _ _ ] =>
      unfold aexp_stack_pure in *; unfold bexp_stack_pure in *; intros
  | [ |- bexp_stack_pure _ _ ] =>
      unfold bexp_stack_pure in *; unfold aexp_stack_pure in *; intros
  | [ |- _ ] =>
      idtac
  end.



                        

Theorem stack_pure :
  (forall (i: imp_stack) (max_stack_begin max_stack_end: nat) (fenv: fun_env_stk),
      never_assigns_out_of_max_stack i max_stack_begin max_stack_end fenv ->
      forall stk stk',
        imp_stack_sem i fenv stk stk' ->
        skipn max_stack_begin stk = skipn max_stack_end stk')
  /\
    (forall (a: aexp_stack) (fenv: fun_env_stk),
        aexp_stack_pure_rel a fenv ->
        aexp_stack_pure a fenv)
  /\
    (forall (b: bexp_stack) (fenv: fun_env_stk),
        bexp_stack_pure_rel b fenv ->
        bexp_stack_pure b fenv)
  /\ (forall (args: list aexp_stack) (fenv: fun_env_stk),
        args_stack_pure_rel args fenv ->
        forall stk stk' vals,
          args_stack_sem args fenv stk (stk', vals) ->
          stk = stk').
Proof.
  pose (fun (i: imp_stack) (max_stack_begin max_stack_end: nat) (fenv: fun_env_stk) =>
        fun (H: never_assigns_out_of_max_stack i max_stack_begin max_stack_end fenv) =>
          forall stk stk',
            imp_stack_sem i fenv stk stk' ->
            skipn max_stack_begin stk = skipn max_stack_end stk') as P.
  pose (fun (a: aexp_stack) (fenv: fun_env_stk) =>
        fun (H: aexp_stack_pure_rel a fenv) =>
          aexp_stack_pure a fenv) as P0.
  pose (fun (b: bexp_stack) (fenv: fun_env_stk) =>
        fun (H: bexp_stack_pure_rel b fenv) =>
          bexp_stack_pure b fenv) as P1.
  pose (fun (args: list aexp_stack) (fenv: fun_env_stk) =>
        fun (H: args_stack_pure_rel args fenv) =>
          forall stk stk' vals,
            args_stack_sem args fenv stk (stk', vals) ->
            stk = stk') as P2.
  apply (pure_stack_mut_ind P P0 P1 P2); unfold aexp_stack_pure, bexp_stack_pure; unfold P, P0, P1, P2 in *; intros; smart_unfold.
  - invc H. reflexivity.
  - invc H0.
    unfold aexp_stack_pure in H.
    specialize (H stk stk'0 c).
    apply H in H5. rewrite <- H5 in *.
    clear H5.
    apply skip_n_of_mutated_stack with (k := k) (n := n) (c := c) (stk'0 := stk) (stk' := stk'); assumption.
  - invs H. simpl. reflexivity.
  - invs H. simpl. reflexivity.
  - invs H2.
    + eapply H0 in H10.
      unfold bexp_stack_pure in H.
      eapply H in H9.
      subst.
      assumption.
    + eapply H1 in H10.
      unfold bexp_stack_pure in H.
      eapply H in H9.
      subst. assumption.
  - invc H1.
    eapply H in H4. eapply H0 in H8.
    rewrite H4. rewrite H8. reflexivity.
  - unfold bexp_stack_pure in H.
    dependent induction H1.
    + assert (stk = stk').
      eapply H.
      eassumption.
      subst. reflexivity.
    + eapply H in H1.
      eapply H0 in H1_.
      rewrite H1 in *.
      rewrite H1_.
      eapply IHimp_stack_sem2.
      * eassumption.
      * eapply H.
      * eassumption.
      * apply H0.
      * reflexivity.
  - invc H. reflexivity.
  - invc H. reflexivity.
  - invc H1.
    eapply H in H7.  eapply H0 in H9.
    rewrite H7. rewrite H9. reflexivity.
  - invc H1. eapply H in H7. eapply H0 in H9.
    rewrite H7. rewrite H9. reflexivity.
  - invc H2.
    pose proof (H13 := H12).
    eapply H in H12. subst.
    eapply H0 in H15. subst.
    eapply H1 in H16.
    eapply args_stack_sem_preserves_length in H13.
    rewrite H16 in *.
    clear H16.
    rewrite List.skipn_app in H15.
    rewrite H11 in H15. rewrite H13 in H15.
    rewrite skipn_all in H15.
    simpl in H15.
    rewrite Nat.sub_diag in H15.
    simpl in H15.
    eapply same_after_popping_skipn.
    + eassumption.
    + rewrite <- H13.
      rewrite Nat.add_comm.
      rewrite H11 in H17. assumption.
  - invc H. reflexivity.
  - invc H. reflexivity.
  - invc H0. apply H in H6. assumption.
  - invc H1.
    eapply H in H8. eapply H0 in H9.
    rewrite H8. rewrite H9. reflexivity.
  - invc H1.
    eapply H in H8. eapply H0 in H9.
    rewrite H8. rewrite H9. reflexivity.
  - invc H1.
    eapply H in H8. eapply H0 in H9.
    rewrite H8. rewrite H9. reflexivity.
  - invc H1.
    eapply H in H8. eapply H0 in H9.
    rewrite H8. rewrite H9. reflexivity.
  - invc H. reflexivity.
  - invc H1. eapply H0 in H9.
    unfold aexp_stack_pure in H.
    eapply H in H7. rewrite H7. rewrite H9.
    reflexivity.
Qed.

      
  
            

Lemma aexp_stack_pure_backwards :
  forall a fenv,
    aexp_stack_pure_rel a fenv -> aexp_stack_pure a fenv.
Proof.
  unfold aexp_stack_pure.
  pose proof (PURE := stack_pure).
  destruct PURE as (_ & AEXP & _).
  apply AEXP.
Qed.

Lemma aexp_stacks_same :
  forall (a : aexp_stack) (fenv : fun_env_stk) (stk stk' : stack) (n : nat),
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk', n) ->
    stk = stk'.
Proof.
  pose proof (aexp_stack_pure_backwards).
  intros.
  eapply H; eassumption.
Qed.

Lemma bexp_stacks_same :
  forall (b: bexp_stack) (fenv : fun_env_stk) (stk stk' : stack) (v: bool),
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b fenv stk (stk', v) ->
    stk = stk'.
Proof.
  pose proof (stack_pure).
  destruct H as (_ & _ & BEXP & _).
  intros.
  eapply BEXP; eassumption.
Qed.


Lemma args_stack_pure_implication :
  forall args fenv,
    args_stack_pure_rel args fenv ->
    (forall stk stk' vals,
        args_stack_sem args fenv stk (stk', vals) ->
        stk = stk').
Proof.
  pose proof (PURE := stack_pure).
  destruct PURE as (_ & _ & _ & ARGS).
  apply ARGS.
Qed.

    
    
Lemma frame_stk :
  forall (i: imp_stack) (max_stack_begin max_stack_end: nat) (fenv: fun_env_stk),
    never_assigns_out_of_max_stack i max_stack_begin max_stack_end fenv ->
    forall stk stk',
      imp_stack_sem i fenv stk stk' ->
      skipn max_stack_begin stk = skipn max_stack_end stk'.
Proof.
  pose proof (PURE := stack_pure).
  destruct PURE as (IMP & _).
  apply IMP.
Qed.

Lemma stack_mutation_app :
  forall stk0 stk1 stk2 k c,
    stack_mutated_at_index stk2 k c (stk0 ++ stk1) ->
    k <= Datatypes.length stk0 ->
    exists stk0' stk0'',
      stk2 = stk0' ++ (c :: stk0'') ++ stk1.
Proof.
  induction stk0; intros.
  - invs H. invs H0. simpl in H0. invs H0. invs H1.
  - invs H.
    + exists nil. exists stk0. simpl. reflexivity.
    + eapply IHstk0 in H9.
      * destruct H9. destruct H1.
        exists (a :: x).
        exists x0.
        rewrite H1. simpl. reflexivity.
      * simpl in H0. intuition.
Qed.

Lemma imp_stack_pure_stack_decomposition :
  forall i fenv stk0 stk1 stk2 n0 n1,
    imp_stack_sem i fenv (stk0 ++ stk1) stk2 ->
    never_assigns_out_of_max_stack i n0 (n1 + n0) fenv ->
    List.length stk0 = n0 ->
    n1 + n0 <= List.length stk2 ->
    skipn n0 (stk0 ++ stk1) = skipn (n1 + n0) stk2 ->
    exists stk3,
      List.length stk3 = n1 + n0 /\
      stk2 = (stk3 ++ stk1).
Proof.
  induction i; intros.
  - invs H. exists stk0. split.
    + invs H0. reflexivity.
    + reflexivity.
  - invs H. invs H0.
    enough (stk0 ++ stk1 = stk').
    + subst.
      assert (forall stk2 stk2' k c,
                 stack_mutated_at_index stk2' k c stk2 ->
                 Datatypes.length stk2' = Datatypes.length stk2).
      {
        intros.
        invs H1.
        - reflexivity.
        - simpl. f_equal. assumption.
      }

      pose proof (MUT := H1 (stk0 ++ stk1) stk2 k c H12). eapply stack_mutation_app in H12.
      * destruct H12 as [stk0' [ stk0'' H12]].
        exists (stk0' ++ (c :: stk0'')). rewrite H12 in MUT. repeat rewrite app_length in MUT. rewrite Nat.add_assoc in MUT. apply Nat.add_cancel_r in MUT.
        split.
        -- rewrite app_length. assumption.
        -- rewrite <- app_assoc. assumption.
      * assumption.
    + inversion H0. eapply aexp_stacks_same. eapply H13. eassumption.
  - invs H. invs H0. exists (0 :: stk0). split; reflexivity.
  - invs H.  invs H0. destruct stk0.
    + simpl in H4. destruct n; invs H1.
    + simpl in H4. exists stk0. simpl in H1. invs H1.
      destruct n1. invs H6. invs H4. simpl. split; [assumption | reflexivity].
      rewrite <- H6. inversion H4. split; [ assumption | reflexivity ].
  - invs H. invs H0. rewrite skipn_app in H3. rewrite Nat.sub_diag in H3. simpl in H3. rewrite skipn_all in H3. simpl in H3. exists (firstn (n1 + Datatypes.length stk0) stk2). split.
    + rewrite firstn_length_le. reflexivity.
      assumption.
    + rewrite H3.
      rewrite firstn_skipn. reflexivity.
  - invs H; invs H0.
    + rewrite skipn_app in H3. rewrite skipn_all in H3. rewrite Nat.sub_diag in H3. simpl in H3. exists (firstn (n1 + Datatypes.length stk0) stk2).
      split.
      * rewrite firstn_length_le. reflexivity.
        assumption.
      * rewrite H3. rewrite firstn_skipn. reflexivity.
    + rewrite skipn_app in H3. rewrite skipn_all in H3. rewrite Nat.sub_diag in H3. simpl in H3. exists (firstn (n1 + Datatypes.length stk0) stk2).
      split.
      * rewrite firstn_length_le. reflexivity.
        assumption.
      * rewrite H3. rewrite firstn_skipn. reflexivity.
  - invs H0; invs H.
    + rewrite skipn_app in H3. rewrite skipn_all in H3. rewrite Nat.sub_diag in H3. simpl in H3. assert (stk0 ++ stk1 = stk2) by (eapply bexp_stacks_same; eassumption).
      exists stk0. rewrite <- H8. symmetry in H1. split; assumption.
    + rewrite skipn_app in H3. rewrite skipn_all in H3. rewrite Nat.sub_diag in H3. simpl in H3.
      exists (firstn (n1 + Datatypes.length stk0) stk2).
      split.
      * rewrite <- H8.
        rewrite firstn_length_le. assumption. rewrite H8. assumption.
      * rewrite H3. rewrite firstn_skipn. reflexivity.
Qed.

Lemma stack_mutated_at_index_preserved_by_superlist :
  forall (stk stk' other: stack) (k c: nat),
    stack_mutated_at_index stk' k c stk ->
    stack_mutated_at_index (stk' ++ other) k c (stk ++ other).
Proof.
  induction stk; intros.
  - invs H.
  - invs H.
    + simpl. constructor. reflexivity.
    + simpl. constructor.
      * assumption.
      * rewrite app_length. rewrite <- Nat.add_succ_l. apply le_plus_trans. assumption.
      * repeat rewrite app_length. rewrite H4. reflexivity.
      * eapply IHstk. assumption.
      * reflexivity.
Qed.

