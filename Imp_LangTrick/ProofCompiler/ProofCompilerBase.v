From Coq Require Import String List Peano Arith Program.Equality Nat
Psatz Arith.PeanoNat Program.Equality.

From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems CompilerCorrect StackFrame1
     StackExtensionDeterministic FunctionWellFormed
CompilerAssumptionLogicTrans.
From Imp_LangTrick Require Import LogicPropHints ParamsWellFormed.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.

Lemma stk_extensible_stk : 
  forall s fenv stk rho,
  meta_match_rel s fenv stk ->
  meta_match_rel s fenv (stk++rho).
Proof. 
  induction s.
  - induction l; intros.
    + constructor; constructor.
    + invs H. invs H1.
    + invs H. invs H2. invs H1.
      constructor. 
      --pose proof bexp_stk_determ_extend a v stk fenv rho H6.
        econstructor.
        apply H0. apply H7.
      --apply H2.
    + invs H. invs H2. invs H1.
      constructor.
      --pose proof bexp_stk_determ_extend a1 v1 stk fenv rho H8.
        pose proof bexp_stk_determ_extend a2 v2 stk fenv rho H9.
        econstructor. apply H0. apply H3. apply H10.
      --apply H2.
    + invs H. invs H1. invs H2. 
      assert (meta_match_rel (MetaBool l1) fenv stk) by
      (constructor; try apply H5; try apply H7).
      assert (meta_match_rel (MetaBool l2) fenv stk) by
      (constructor; try apply H6; try apply H8).
      constructor. 
      --pose proof IHl1 fenv stk rho H0.
        invs H4.
        pose proof IHl2 fenv stk rho H3.
        invs H9. 
        constructor; assumption.
      --assumption.
    + invs H. invs H1; invs H2. 
      --assert (meta_match_rel (MetaBool l1) fenv stk) by
        (constructor; try apply H4; try apply H6).
        pose proof IHl1 fenv stk rho H0. invs H3.  
        constructor.
        ++apply RelOrPropLeft. assumption.
        ++assumption.
      -- assert (meta_match_rel (MetaBool l2) fenv stk) by
        (constructor; try apply H4; try apply H7).
        pose proof IHl2 fenv stk rho H0. invs H3.  
        constructor.
        ++apply RelOrPropRight. assumption.
        ++assumption.
    + invs H. invs H2. invs H1.
      constructor.
      --pose proof bexp_stk_determ_extend a1 v1 stk fenv rho H10.
        pose proof bexp_stk_determ_extend a2 v2 stk fenv rho H11.
        pose proof bexp_stk_determ_extend a3 v3 stk fenv rho H12.
        econstructor. apply H0. apply H3. apply H4. apply H13. 
      --apply H2.
    + invs H. invs H1. 
      constructor.
      --econstructor. 
        apply (bool_args_stk_determ_extend a_list fenv stk rho vals H5).
        apply H6.
      --apply H2.
  - induction l; intros.
    + constructor; constructor.
    + invs H. invs H1.
    + invs H. invs H2. invs H1.
      constructor. 
      --pose proof aexp_stk_determ_extend a v stk fenv rho H6.
        econstructor.
        apply H0. apply H7.
      --apply H2.
    + invs H. invs H2. invs H1.
      constructor.
      --pose proof aexp_stk_determ_extend a1 v1 stk fenv rho H8.
        pose proof aexp_stk_determ_extend a2 v2 stk fenv rho H9.
        econstructor. apply H0. apply H3. apply H10.
      --apply H2.
    + invs H. invs H1. invs H2. 
      assert (meta_match_rel (MetaNat l1) fenv stk) by
      (constructor; try apply H5; try apply H7).
      assert (meta_match_rel (MetaNat l2) fenv stk) by
      (constructor; try apply H6; try apply H8).
      constructor. 
      --pose proof IHl1 fenv stk rho H0.
        invs H4.
        pose proof IHl2 fenv stk rho H3.
        invs H9. 
        constructor; assumption.
      --assumption.
    + invs H. invs H1; invs H2. 
      --assert (meta_match_rel (MetaNat l1) fenv stk) by
        (constructor; try apply H4; try apply H6).
        pose proof IHl1 fenv stk rho H0. invs H3.  
        constructor.
        ++apply RelOrPropLeft. assumption.
        ++assumption.
      -- assert (meta_match_rel (MetaNat l2) fenv stk) by
        (constructor; try apply H4; try apply H7).
        pose proof IHl2 fenv stk rho H0. invs H3.  
        constructor.
        ++apply RelOrPropRight. assumption.
        ++assumption.
    + invs H. invs H2. invs H1.
      constructor.
      --pose proof aexp_stk_determ_extend a1 v1 stk fenv rho H10.
        pose proof aexp_stk_determ_extend a2 v2 stk fenv rho H11.
        pose proof aexp_stk_determ_extend a3 v3 stk fenv rho H12.
        econstructor. apply H0. apply H3. apply H4. apply H13. 
      --apply H2.
    + invs H. invs H1. 
      constructor.
      --econstructor. 
        apply (nat_args_stk_determ_extend a_list fenv stk rho vals H5).
        apply H6.
      --apply H2.
Qed. 

Lemma stk_extensible_state : 
  forall s fenv stk rho,
  absstate_match_rel s fenv stk ->
  absstate_match_rel s fenv (stk ++ rho).
Proof. 
  induction s; intros. 
  - invs H. 
    pose proof stk_extensible_stk m fenv stk rho H5.
    constructor.
    invs H2.
    + constructor.
    + constructor. rewrite app_length. lia.
    + assumption.
  - invs H. constructor.
    + apply IHs1. assumption.
    + apply IHs2. assumption.
  - invs H.
    + apply RelAbsOrLeft. apply IHs1. assumption.
    + apply RelAbsOrRight. apply IHs2. assumption.
Qed. 

Lemma imp_Imp_Lang_wf_inversion_assign :
  forall (idents: list ident) (x: ident) (a: aexp_Imp_Lang),
    imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp idents)
                                       (var_map_wf_wrt_bexp idents)
                                       (ASSIGN_Imp_Lang x a) ->
    (var_map_wf_wrt_aexp idents a).
Proof.
  intros.
  invs H.
  assumption.
Qed.

Definition AbsEnv_prop_wf (idents: list ident) (d: AbsEnv) : Prop :=
  AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d.
