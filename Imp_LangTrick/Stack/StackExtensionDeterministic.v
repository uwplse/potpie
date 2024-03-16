From Coq Require Import String List Peano Arith Program.Equality Nat
Psatz Arith.PeanoNat Program.Equality.

From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems CompilerCorrect StackFrame1 StackPure.

(*
 * 
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.

Lemma same_after_popping_extend : 
  forall stk' n stk rho, 
  same_after_popping stk stk' n ->
  same_after_popping (stk ++ rho) (stk' ++ rho) n.
Proof.
  induction stk'; intros.
  - invs H. constructor. apply eq_refl.
  - invs H.
    + invs H. constructor. apply eq_refl.
    + specialize (IHstk' n0 stk rho H4).
      assert (((a :: stk') ++ rho) = (a :: stk' ++ rho)) by auto.
      rewrite H0.  
      constructor.
      apply IHstk'.
Qed.       


Check imp_stack_mutind. 

Lemma stk_determ_extend : 
  (forall a fenv stk stk',
    imp_stack_sem a fenv stk (stk') ->
      forall rho,
        imp_stack_sem a fenv (stk++rho) ((stk'++rho)))
  /\
  (forall a fenv stk stk',
      aexp_stack_sem a fenv stk stk' ->
      forall rho stk'' n,
        stk' = (stk'', n) ->
        aexp_stack_sem a fenv (stk++rho) ((stk''++rho), n))
  /\
  (forall a fenv stk stk',
      bexp_stack_sem a fenv stk (stk') ->
      forall rho stk'' n,
        stk' = (stk'', n) ->
        bexp_stack_sem a fenv (stk++rho) ((stk''++rho), n))
  /\
  (forall a fenv stk stk',
    args_stack_sem a fenv stk stk' ->
    forall rho stk'' ns,
      stk' = (stk'', ns) ->
      args_stack_sem a fenv (stk++rho) ((stk''++rho, ns)))
.
Proof.
  pose (fun a fenv stk stk'=> 
    (fun (i : imp_stack_sem a fenv stk stk') => 
      forall rho, 
        imp_stack_sem a fenv (stk++rho) ((stk'++rho)))) 
    as P.
  pose (fun a fenv stk stk' => 
    (fun (i0 : aexp_stack_sem a fenv stk stk') =>
          forall rho stk'' n,
            stk' = (stk'', n) ->
              aexp_stack_sem a fenv (stk++rho) ((stk''++rho), n))) 
      as P0.  
  pose (fun a fenv stk stk' => 
    (fun (i1 : bexp_stack_sem a fenv stk stk') =>
          forall rho stk'' n,
            stk' = (stk'', n) ->
              bexp_stack_sem a fenv (stk++rho) ((stk''++rho), n))) 
      as P1.  
  pose (fun a fenv stk stk' => 
    (fun (i1 : args_stack_sem a fenv stk stk') =>
          forall rho stk'' n,
            stk' = (stk'', n) ->
              args_stack_sem a fenv (stk++rho) ((stk''++rho), n))) 
      as P2.  
  apply (imp_stack_mutind P P0 P1 P2); unfold P, P0, P1, P2 in *; intros.
  - constructor.
  - econstructor.
    + apply l. 
    + invs s.
      --rewrite app_length. simpl. lia.
      --rewrite app_length. simpl. lia.
    + apply (H rho stk' c eq_refl). 
    + apply stack_mutated_at_index_preserved_by_superlist.
      apply s.  
  - rewrite e. constructor. apply eq_refl. 
  - rewrite e. econstructor. exists.
  - econstructor.
    apply H. apply H0.
  - econstructor.
    apply H. exists. apply H0.
  - eapply Stack_if_false.
    apply H. exists. apply H0. 
  - eapply Stack_while_done. apply H. apply eq_refl.
  - eapply Stack_while_step.
    + apply H. exists.
    + apply H0.
    + apply H1.
  - invs H. constructor.
  - invs H. constructor; try assumption.
    + rewrite app_length. lia.
    + pose proof (nth_error_app1 stk'' rho).
      specialize (H0 (i - 1)). 
      destruct H0. lia. apply e.
  - specialize (H rho stk1 n1 eq_refl).
    specialize (H0 rho stk2 n2 eq_refl).
    pose proof Stack_plus fenv (stk++rho) a1 a2 (stk1++rho) (stk2++rho) n1 n2 H H0.
    invs H1. assumption.
  - specialize (H rho stk1 n1 eq_refl).
    specialize (H0 rho stk2 n2 eq_refl).
    pose proof Stack_minus fenv (stk++rho) a1 a2 (stk1++rho) (stk2++rho) n1 n2 H H0.
    invs H1. assumption.
  - econstructor. 
    + apply e.
    + apply e0.
    + apply e1.
    + apply e2.
    + apply e3.
    + apply H. exists.
    + specialize (H0 rho). 
      assert (((vals ++ stk1) ++ rho) = (vals ++ stk1 ++ rho)) by (symmetry;apply app_assoc).
      rewrite <- H3. apply H0.
    + invs H2. apply H1. 
      exists.
    + apply same_after_popping_extend. invs H2. assumption.
  - invs H. apply Stack_true.
  - invs H. apply Stack_false.
  - econstructor.
    + invs H0. apply H. exists.
    + invs H0. apply eq_refl.
  - econstructor. 
    + apply H. exists.
    + invs H1. apply H0. exists.
    + invs H1. apply eq_refl.
  - econstructor. 
    + apply H. exists.
    + invs H1. apply H0. exists.
    + invs H1. apply eq_refl.
  - econstructor.
    + apply H. exists.
    + invs H1. apply H0. exists.
    + invs H1. apply eq_refl.
  - econstructor.
    + apply H. exists.
    + invs H1. apply H0. exists.
    + invs H1. apply eq_refl.
  - invs H. constructor.
  - invs H1. econstructor.
    + apply H. exists.
    + apply H0. apply eq_refl.
Qed. 


Lemma aexp_stk_determ_extend : 
  forall a n stk fenv rho,
    aexp_stack_sem a fenv stk (stk, n) ->
    aexp_stack_sem a fenv (stk++rho) ((stk++rho), n).
Proof. 
  intros. 
  pose proof stk_determ_extend.
  destruct H0. destruct H1. 
  clear H2.
  apply (H1 a fenv stk (stk, n) H rho stk n eq_refl).    
Qed. 

Lemma bexp_stk_determ_extend : 
  forall a n stk fenv rho,
    bexp_stack_sem a fenv stk (stk, n) ->
    bexp_stack_sem a fenv (stk++rho) ((stk++rho), n).
Proof. 
  intros. 
  pose proof stk_determ_extend.
  destruct H0. destruct H1. destruct H2. 
  clear H3.
  apply (H2 a fenv stk (stk, n) H rho stk n eq_refl).    
Qed. 

Lemma args_stk_determ_extend : 
(forall a ns fenv stk stk' rho,
args_stack_sem a fenv stk (stk', ns) ->
args_stack_sem a fenv (stk++rho) ((stk'++rho, ns))).
Proof.
  intros. pose proof stk_determ_extend.
  destruct H0. destruct H1. destruct H2. 
  apply (H3 a fenv stk (stk', ns) H rho stk' ns eq_refl).
Qed.

Lemma nat_args_stk_determ_extend : 
forall a_list fenv stk rho vals, 
  (eval_prop_args_rel
    (fun (natexpr : aexp_stack) (natval : nat) =>
    aexp_stack_sem natexpr fenv stk (stk, natval)) a_list vals) ->
  (eval_prop_args_rel
  (fun (natexpr : aexp_stack) (natval : nat) =>
   aexp_stack_sem natexpr fenv (stk ++ rho) (stk ++ rho, natval)) a_list vals).
Proof. 
  induction a_list; intros.
  - invs H. constructor.
  - invs H. specialize (IHa_list fenv stk rho vals0 H5). 
    constructor. apply (aexp_stk_determ_extend a val stk fenv rho H3).
    apply IHa_list.
Qed. 

Lemma bool_args_stk_determ_extend :
forall a_list fenv stk rho vals, 
(eval_prop_args_rel (fun (boolexpr : bexp_stack) (boolval : bool) =>
bexp_stack_sem boolexpr fenv (stk) (stk, boolval))
a_list vals) ->
(eval_prop_args_rel (fun (boolexpr : bexp_stack) (boolval : bool) =>
bexp_stack_sem boolexpr fenv (stk ++ rho) (stk ++ rho, boolval))
a_list vals).
Proof. 
  induction a_list; intros.
  - invs H. constructor.
  - invs H. specialize (IHa_list fenv stk rho vals0 H5). 
    constructor. apply (bexp_stk_determ_extend a val stk fenv rho H3).
    apply IHa_list.
Qed.  
