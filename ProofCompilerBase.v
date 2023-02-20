From Coq Require Import String List Peano Arith Program.Equality Nat
Psatz Arith.PeanoNat Program.Equality.

From DanTrick Require Import StackLogic DanLogHoare DanTrickLanguage EnvToStack StackLanguage DanLogProp LogicProp StackLangTheorems StackLogicBase.
From DanTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From DanTrick Require Export ProofSubstitution ImpVarMapTheorems DanLogSubstAdequate.
From DanTrick Require Import DanImpHigherOrderRel DanImpHigherOrderRelTheorems CompilerCorrect StackFrame1
     StackExtensionDeterministic FunctionWellFormed CompilerAssumptionLogicTrans.
From DanTrick Require Import LogicPropHints ParamsWellFormed StkTruncate.

(*
 * 
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Ltac inversion_match_rel :=
  match goal with
    | [ H: logic_transrelation _ _ _ (?AbsStateConst ?s1 ?m1) |- _ ] =>
        invs H;
        idtac;
        match goal with
        | [ H1: absstate_match_rel (AbsAnd (?AbsStateConst ?s1 ?m1)
                                           _) _ _ |- _ ] =>
            invs H1;
            idtac;
            match goal with
            | [ H3: absstate_match_rel (AbsStateConst s1 m1) _ _ |- _ ] =>
                invs H3
            end
            ;
            try match goal with
                | [ H4: absstack_match_rel _ _ |- _ ] =>
                    invs H4
                end
        end
    end.

Lemma hl_dan_implication_helper :
  forall s1 ARG b idents n_args fenv d my_fun,
    logic_transrelation n_args idents d s1 ->
    ARG = AbsAnd
            s1
            (BaseState
               AbsStkTrue
               (MetaBool
                  (UnaryProp bool bexp_stack
                             my_fun
                             (compile_bexp
                                b
                                (ident_list_to_map idents)
                                (Datatypes.length idents))))
            ) ->
    (ARG --->>>
         BaseState (AbsStkSize (Datatypes.length idents + n_args))
         (MetaBool
            (UnaryProp bool bexp_stack my_fun
                       (compile_bexp b
                                     (ident_list_to_map idents)
                                     (Datatypes.length idents))))) 
    (compile_fenv fenv).
Proof.
  induction s1; unfold aimpstk; intros; subst.
  - inversion_match_rel.
    econstructor.
    econstructor. intuition.
    invs H7. assumption.
  - inversion_match_rel.
    econstructor.
    + remember_all_in H8.
      match (type of H8) with
      | absstate_match_rel ?ARG0 ?ARG ?stk =>
          assert (absstate_match_rel (AbsAnd s1_1 ARG0) ARG stk) by (econstructor; eassumption)
      end.
      
      eapply IHs1_1 in H6; [ | ereflexivity ].
      unfold aimpstk in H6. specialize (H6 stk).
      rewrite HeqARG0 in H0.
      rewrite HeqARG in H0.
      eapply H6 in H0.
      invs H0. assumption.
    + invs H8. assumption.
  - inversion_match_rel.
    + remember_all_in H8. rewrite HeqARG in *; clear HeqARG.
      match (type of H8) with
      | absstate_match_rel ?ARG0 ?ARG ?stk =>
          assert (absstate_match_rel (AbsAnd s1_1 ARG0) ARG stk) by (econstructor; eassumption)
      end.
      eapply IHs1_1 in H0. eassumption.
      eassumption.
      rewrite HeqARG0. reflexivity.
    + remember_all_in H8.
      rewrite HeqARG in *. clear HeqARG.
      assert (absstate_match_rel (AbsAnd s1_2 ARG0) (compile_fenv fenv) stk) by (econstructor; assumption).
      eapply IHs1_2 in H0. eassumption.
      eassumption. rewrite HeqARG0. reflexivity.
Qed.

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

Lemma stk_long_boi :
  forall s1 d1 n_args idents stk fenv func_list,
  logic_transrelation n_args idents d1 s1 ->
  List.NoDup idents ->
  AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) d1 ->
  FunctionWellFormed.fenv_well_formed' func_list fenv ->
  absstate_match_rel s1 (compile_fenv fenv) stk ->
  n_args + (Datatypes.length idents) = Datatypes.length stk
  \/
  Datatypes.length stk > n_args + (Datatypes.length idents)
  .
Proof. 
  induction s1; intros.
  - invs H. invs H3. invs H6. lia.
  - invs H. invs H3. invs H1. 
    apply (IHs1_1 d0 n_args idents stk fenv func_list H9 H0 H12 H2 H6).
  - invs H. invs H3; invs H1. 
    + apply (IHs1_1 d0 n_args idents stk fenv func_list H9 H0 H11 H2 H8).
    + apply (IHs1_2 d2 n_args idents stk fenv func_list H10 H0 H12 H2 H8).
Qed. 

 Lemma aimpdan_to_aimpstk :
   forall (d1 d2: AbsEnv) (fenv: fun_env) (s1 s2: AbsState) (fenv': fun_env_stk) (n_args: nat) (idents: list ident)
     (func_list: list fun_Dan),
   forall (OKfuncs: funcs_okay_too func_list fenv')
     (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
     (Translate1: logic_transrelation n_args idents d1 s1)
     (Translate2: logic_transrelation n_args idents d2 s2),
   forall (WF1: log_Dan_wf func_list fenv d1),
   forall (WFMap1: log_Dan_wf_map idents d1),
   forall (WF2 : log_Dan_wf func_list fenv d2),
   forall (WFMap2 : log_Dan_wf_map idents d2),
   forall (TERMINATOR1 : log_terminates_always fenv n_args d1),
   forall (ILLBEBACK : log_terminates_always fenv n_args d2),
   forall (NoDups : List.NoDup idents),
   forall (FenvWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
   forall (AimpDan : (aimpDan d1 d2 fenv)),
   forall (CompFenv: fenv' = compile_fenv fenv),
   forall (VarWf1: AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d1),
   forall (VarWf2 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d2),
     (aimpstk s1 s2 fenv').
Proof.
  unfold aimpDan, aimpstk.
  intros.
  match goal with
  | [H: absstate_match_rel _ _ _ |- _ ] =>
      rename H into AbsMatch1
  end.
  pose proof (StackToEnv' := stk_to_env idents stk n_args).
  subst fenv'.
  pose proof (StkLong := stk_long_boi s1 d1 n_args idents stk fenv func_list Translate1 NoDups VarWf1 FenvWF AbsMatch1).
  destruct StkLong as [StkLong | StkLong].
  - rewrite Nat.add_comm in StkLong.
    rewrite StkLong in StackToEnv'.  
    specialize (StackToEnv' eq_refl NoDups).
    destruct StackToEnv' as [x [x0 Other]].
    destruct Other as [State2Stack X0Len].
    pose proof (DLRImplies := AimpDan x0 x).
    pose proof (CompBwd := log_sound_backwards d1 s1 n_args idents func_list Translate1 fenv (compile_fenv fenv) eq_refl FenvWF WF1 WFMap1 TERMINATOR1 x x0 X0Len stk State2Stack nil).
    assert (ConcatNil : (stk++nil) = (stk)) by apply app_nil_r.
    rewrite <- ConcatNil in AbsMatch1.   
    pose proof (DLR1 := CompBwd AbsMatch1).
    pose proof (DLR2 := DLRImplies DLR1).
    pose proof (CompFwd := log_sound_forward d2 s2 n_args idents func_list Translate2 fenv _ OKfuncs OKparams eq_refl FenvWF WF2 WFMap2 x x0 X0Len stk State2Stack DLR2 nil).
    rewrite ConcatNil in CompFwd.
    assumption.
  - pose proof (Truncate := stk_truncate d1 s1 stk n_args idents fenv func_list NoDups Translate1 VarWf1 WF1 OKparams AbsMatch1 StkLong TERMINATOR1 OKfuncs FenvWF).
    destruct Truncate as [x Truncate]. destruct Truncate as [x0 Truncate]. destruct Truncate as [StkDecomp Other]. destruct Other as [XLenIsNumArgs AbsMatch].
    rewrite Nat.add_comm in XLenIsNumArgs. 
    pose proof (Stk2Env := stk_to_env idents x n_args XLenIsNumArgs NoDups).
    destruct Stk2Env as [x1 Stk2Env]. destruct Stk2Env as [x2 Stk2Env].
    destruct Stk2Env as [StateToStack LenIsNumArgs]. 
    pose proof (CompBwd := log_sound_backwards d1 s1 n_args idents func_list Translate1 fenv (compile_fenv fenv) eq_refl FenvWF WF1 WFMap1 TERMINATOR1 x1 x2 LenIsNumArgs x StateToStack nil).
    assert (ConcatNil : (x++nil) = (x)) by apply app_nil_r.
    rewrite ConcatNil in *.
    specialize (CompBwd AbsMatch).
    specialize (AimpDan x2 x1 CompBwd).
    pose proof (CompFwd := log_sound_forward d2 s2 n_args idents func_list Translate2 fenv _ OKfuncs OKparams eq_refl FenvWF WF2 WFMap2 x1 x2).
    rewrite LenIsNumArgs in CompFwd.
    specialize (CompFwd eq_refl x StateToStack AimpDan nil). 
    rewrite ConcatNil in *.
    pose proof (StkExtend := stk_extensible_state s2 (compile_fenv fenv ) x x0 CompFwd).
    rewrite StkDecomp. assumption.
Qed.   

Lemma logic_transrelation_to_compiled :
  forall (n_args: nat) (idents: list ident) (d: AbsEnv),
    logic_transrelation n_args idents d (comp_logic n_args idents d).
Proof.
  intros.
  eapply log_comp_adequacy.
  reflexivity.
Qed.

Lemma imp_Dan_wf_inversion_assign :
  forall (idents: list ident) (x: ident) (a: aexp_Dan),
    imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp idents)
                                       (var_map_wf_wrt_bexp idents)
                                       (ASSIGN_Dan x a) ->
    (var_map_wf_wrt_aexp idents a).
Proof.
  intros.
  invs H.
  assumption.
Qed.

Definition AbsEnv_prop_wf (idents: list ident) (d: AbsEnv) : Prop :=
  AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d.
