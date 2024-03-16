From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick.Stack Require Import StackLanguage StackLangTheorems StackFrame.

Require Import Imp_LangTrick.LogicProp.LogicProp.

Scheme Equality for list.

Definition aexp_stack_pure (a: aexp_stack) (fenv: fun_env_stk): Prop :=
  forall stk stk' n,
    aexp_stack_sem a fenv stk (stk', n) ->
    stk = stk'.

Definition bexp_stack_pure (b: bexp_stack) (fenv: fun_env_stk): Prop :=
  forall stk stk' v,
    bexp_stack_sem b fenv stk (stk', v) ->
    stk = stk'.





Inductive bexp_stack_pure_rel: bexp_stack -> fun_env_stk -> Prop :=
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
    1 <= k ->
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
    imp_frame_rule (Body func) fenv (Args func) ((Return_pop func) + (Args func)) ->
    aexp_frame_rule (Return_expr func) fenv ((Return_pop func) + (Args func)) ->
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

Scheme aexp_stack_pure_ind := Induction for aexp_stack_pure_rel Sort Prop
with bexp_stack_pure_ind := Induction for bexp_stack_pure_rel Sort Prop
with args_stack_pure_ind := Induction for args_stack_pure_rel Sort Prop.

Combined Scheme pure_stack_mut_ind from aexp_stack_pure_ind, bexp_stack_pure_ind, args_stack_pure_ind.


Ltac smart_unfold :=
  match goal with
  | [ |- aexp_stack_pure _ _ ] =>
      unfold aexp_stack_pure in *; unfold bexp_stack_pure in *; intros
  | [ |- bexp_stack_pure _ _ ] =>
      unfold bexp_stack_pure in *; unfold aexp_stack_pure in *; intros
  | [ |- _ ] =>
      idtac
  end.



Definition frame_implies_pure_rel_thm_P (a: aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  aexp_stack_pure_rel a fenv.

Definition frame_implies_pure_rel_thm_P0 (args: list aexp_stack) (fenv: fun_env_stk) (_: nat) : Prop :=
  args_stack_pure_rel args fenv.

Definition frame_implies_pure_rel_thm_P1 (b: bexp_stack) (fenv: fun_env_stk) (_: nat) : Prop :=
  bexp_stack_pure_rel b fenv.

Definition frame_implies_pure_rel_thm_P2 (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat) : Prop :=
  imp_frame_rule i fenv frame frame'.

Theorem frame_implies_pure_rel :
  frame_rule_mut_ind_theorem frame_implies_pure_rel_thm_P frame_implies_pure_rel_thm_P0 frame_implies_pure_rel_thm_P1 frame_implies_pure_rel_thm_P2.
Proof.
  frame_rule_mutual_induction P P0 P1 P2 frame_implies_pure_rel_thm_P frame_implies_pure_rel_thm_P0 frame_implies_pure_rel_thm_P1 frame_implies_pure_rel_thm_P2; intros.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - econstructor.
    + eassumption.
    + assumption.
    + rewrite Nat.add_comm. assumption.
    + rewrite Nat.add_comm. assumption.
    + assumption.
  - constructor.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Theorem args_frame_implies_args_pure :
  forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat),
    args_frame_rule args fenv frame ->
    args_stack_pure_rel args fenv.
Proof.
  pose proof (frame_implies_pure_rel).
  unfold frame_rule_mut_ind_theorem in H. unfold frame_implies_pure_rel_thm_P0 in H.
  destruct H as (_ & ARGS & _).
  apply ARGS.
Qed.

Theorem aexp_frame_implies_aexp_pure :
  forall (a: aexp_stack) (fenv: fun_env_stk) (frame: nat),
    aexp_frame_rule a fenv frame ->
    aexp_stack_pure_rel a fenv.
Proof.
  pose proof (frame_implies_pure_rel).
  unfold frame_rule_mut_ind_theorem in H. unfold frame_implies_pure_rel_thm_P in H.
  destruct H as (AEXP & _).
  apply AEXP.
Qed.

                    

                        

Theorem stack_pure :
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
  apply (pure_stack_mut_ind P0 P1 P2); unfold aexp_stack_pure, bexp_stack_pure; unfold P0, P1, P2 in *; intros; smart_unfold.
  - invc H. reflexivity.
  - invc H. reflexivity.
  - invc H1.
    eapply H in H7.  eapply H0 in H9.
    rewrite H7. rewrite H9. reflexivity.
  - invc H1. eapply H in H7. eapply H0 in H9.
    rewrite H7. rewrite H9. reflexivity.
  - invc H1.
    pose proof (H12 := H11).
    eapply H in H11. subst.
    eapply args_stack_sem_preserves_length in H12.
    eapply frame_implies_rest_stk_untouched_le in H14.
    shelve.
    {
      rewrite Nat.add_comm in i.
      eassumption.
    }
    {
      rewrite H12 in H10. assumption.
    }
    eapply same_after_popping_implies_geq_popped_length; eauto.
    rewrite Nat.add_comm. rewrite (H0 stk2 stk3 n H15).
    eauto.
    Unshelve.
    
    destruct H14. destruct H1.
    subst.
    apply H0 in H15. rewrite <- H15 in H16.
    eapply same_after_popping_length in H16; [ | assumption].
    symmetry in H16. assumption.
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
  pose proof (PURE := stack_pure).
  destruct PURE as (AEXP & _).
  apply AEXP.
Qed.


Lemma args_stack_pure_implication :
  forall args fenv,
    args_stack_pure_rel args fenv ->
    (forall stk stk' vals,
        args_stack_sem args fenv stk (stk', vals) ->
        stk = stk').
Proof.
  pose proof (PURE := stack_pure).
  destruct PURE as (_ & _ & ARGS).
  apply ARGS.
Qed.

Lemma bexp_stack_pure_implication :
  forall b fenv,
    bexp_stack_pure_rel b fenv ->
    bexp_stack_pure b fenv.
Proof.
  pose proof (PURE := stack_pure).
  destruct PURE as (_ & BEXP & _).
  apply BEXP.
Qed.



    
Lemma frame_stk :
  forall (i: imp_stack) (max_stack_begin max_stack_end: nat) (fenv: fun_env_stk),
    imp_frame_rule i fenv max_stack_begin max_stack_end ->
    forall stk stk',
      imp_stack_sem i fenv stk stk' ->
      skipn max_stack_begin stk = skipn max_stack_end stk'.
Proof.
  intros.
  eapply imp_frame_implies_untouched_stack; eassumption.
Qed.
