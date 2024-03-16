From Coq Require Import String List Peano Arith Program.Equality.
From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel ProofCompilerHelpers Imp_LangHoareWF.
From Imp_LangTrick Require Import ProofCompilerBase Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import FunctionWellFormed
CompilerAssumptionLogicTrans.
From Imp_LangTrick Require Import Imp_LangLogicHelpers FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompilableCodeCompiler StackUpdateAdequacy ProofCompCodeCompAgnosticMod.

(*
 * This is the file for the proof compiler, which compiles
 * proofs in Imp_LangTrickLogic to proofs in StackLogic.
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.


Module CompilerAgnosticProofCompiler(PC: ProofCompilableType) <: CompilerAgnosticProofCompilerType.
  Module PC := PC.
  (* The Code Compiler (CC) and Specification Compiler (SC) *)
  Module CC := PC.CC.
  Module SC := PC.SC.

  Definition comp_code := CC.compile_imp.
  


  Ltac rename_fresh_until_no_match :=
    match goal with
    | [ H: AbsEnv_prop_rel (var_map_wf_wrt_aexp ?map) (var_map_wf_wrt_bexp ?map) ?d |- _ ] =>
        let HWF := fresh "WF" in
        pose proof (HWF := H); clear H; revert HWF; rename_fresh_until_no_match
    | _ => intros
    end.

  Program Definition hl_compile_skip (P : AbsEnv)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (map : list ident)
          (func_list: list fun_Imp_Lang)
          (args : nat)
          (AIMPWF : aimp_always_wf func_list map args P SKIP_Imp_Lang P fenv facts (hl_Imp_Lang_skip P facts fenv))
          (s2 s1 : AbsState)
          (fenv0 : fun_env_stk)
          (i' : imp_stack)
          (H : SC.comp_logic args map P = s1)
          (H0 : SC.comp_logic args map P = s2)
          (H1 : i' = comp_code SKIP_Imp_Lang map args)
          (Hcheck : CC.check_imp SKIP_Imp_Lang = true)
          (* (H2 : fenv0 = compile_fenv fenv) *)
          (H3 H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
          (IMPWF : imp_rec_rel (var_map_wf_wrt_imp map) SKIP_Imp_Lang)
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2 facts' fenv0.
  Proof.
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end;
      match goal with
      | [ H: aimp_always_wf ?idents ?i |- _ ] =>
          let AIMPWF := fresh "AIMPWF" in
          pose proof (AIMPWF := H); clear H; unfold aimp_always_wf in *
      | _ => idtac
      end.
    pose proof (H' := PC.skip_compilation_okay args map).
    assert (H: CC.compile_imp SKIP_Imp_Lang map args = Skip_Stk).
    {
      unfold CC.compile_imp. eapply H'. unfold CC.check_imp in Hcheck. eassumption.
    }
    rewrite H.
    econstructor.
    unfold PC.valid_imp_trans_def in IRONHIDE. apply (proj2 IRONHIDE).
  Defined.


  Print hl_compile_skip.
  
  (*
   * To eventually decouple the essence of proof compilation from its
   * correctness proof, I'm looking at some proof terms and trying to tease
   * apart the details of what is happening and document it. In doing so,
   * I'll probably simplify the terms a bit.
   *)

  Example stupid:
    forall (A: Type) (a b c: A) (H: a = b) (H': b = c),
      a = c.
  Proof.
    intros.
    rewrite H. assumption.
  Defined.
  Print stupid.
  Print eq_ind_r.

   Example testing' :
    forall P args map s1 s2 facts' fenv0 i',
    forall (H : SC.comp_logic args map P = s1)
      (H0 : SC.comp_logic args map P = s2)
      (H1: hl_stk s1 i' s2 facts' fenv0),
      (hl_stk (SC.comp_logic args map P) i' (SC.comp_logic args map P) facts' fenv0).
  Proof.
    intros. rewrite H at 1. rewrite H0. eassumption.
  Defined.
  Print testing'.

  Example testing :
    forall P args map s1 s2 facts' fenv0 i',
    forall (H : SC.comp_logic args map P = s1)
      (H0 : SC.comp_logic args map P = s2)
      (H1: hl_stk (SC.comp_logic args map P) i' (SC.comp_logic args map P) facts' fenv0),
      hl_stk s1 i' s2 facts' fenv0.
  Proof.
    intros. rewrite <- H. rewrite <- H0. eassumption.
  Defined.

  Print testing.

  Print eq_rect_r.

  Eval compute in (fun map args => comp_code SKIP_Imp_Lang map args).
  Eval compute in (fun map => compile_imp SKIP_Imp_Lang (ident_list_to_map map) (Datatypes.length map)).

  Program Definition hl_compile_assign (P : AbsEnv)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (x : string)
          (a : aexp_Imp_Lang)
          (funcs: list fun_Imp_Lang)
          (map : list ident)
          (args : nat)
          (AIMPWF : aimp_always_wf funcs map args (Imp_LangLogSubst.subst_AbsEnv x a P) (x <- a) P fenv facts (hl_Imp_Lang_assign P facts fenv x a))
          (fenv0 : fun_env_stk)
          (s2 s1 : AbsState)
          (i' : imp_stack)
          (FENV_WF : fenv_well_formed' funcs fenv)
          (FUN_APP : fun_app_imp_well_formed fenv funcs (x <- a))
          (OKfuncs: funcs_okay_too funcs fenv0)
          (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs)
          (H : SC.comp_logic args map (Imp_LangLogSubst.subst_AbsEnv x a P) = s1)
          (Hcheck_pf: PC.check_proof fenv funcs (Imp_LangLogSubst.subst_AbsEnv x a P) P
                                     (x <- a) facts map args (hl_Imp_Lang_assign P facts fenv x a))
          (Hcheck_logic: SC.check_logic P = true)
          (Hcheck : CC.check_imp (x <- a) = true)
          (H0 : SC.comp_logic args map P = s2)
          (H1 : i' = comp_code (x <- a) map args)
          (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (Imp_LangLogSubst.subst_AbsEnv x a P))
          (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
          (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (x <- a))
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2  facts' fenv0.
  Proof.
    revert H.
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end;
      match goal with
      | [ H: aimp_always_wf ?idents ?i |- _ ] =>
          let AIMPWF := fresh "AIMPWF" in
          pose proof (AIMPWF := H); clear H; unfold aimp_always_wf in *
      | _ => idtac
      end.
    unfold CC.compile_imp. erewrite PC.assign_compilation_commutes.
    eapply hl_stk_assign.
    - invs IRONHIDE. eapply (proj2 H1).
    - invs Hcheck_pf; try solve [ invs Hi | invs H0 ];
      invs Hi.
      eapply H8; try eassumption.
      + invs FUN_APP. eassumption.
      + invs AIMPWF. invs HSkip. invs Heq0. eassumption.
        invs Heq0. invs heq. invs Heq0. invs H. invs H.
      + invs AIMPWF.
        * invs HSkip.
        * invs Heq0. smart_unfold_wf_imp_in  IMPWF.
          invs WF'. eassumption.
        * invs Heq0.
        * invs heq.
        * invs Heq0.
        * invs H.
        * invs H.
    - invs Hcheck_pf; try solve [invs Hi | invs H0 ];
      invs Hi. erewrite H9. eapply state_update_adequacy_forwards.
      eassumption. eassumption.
      eassumption.
      reflexivity. reflexivity.
      
      invs IMPWF. unfold_wf_imp_in H11. invs WF'. eassumption.
      invs IMPWF. unfold_wf_imp_in H11. eapply WF''. econstructor. eapply String.eqb_refl.
      reflexivity.
    - eassumption.
  Defined.

  Lemma inv_fun_app_imp_assign :
    forall fenv funcs x a,
      fun_app_imp_well_formed fenv funcs (x <- a) ->
      fun_app_well_formed fenv funcs a.
  Proof.
    intros. inversion H. assumption.
  Defined.

  Lemma inv_imp_forall_assign :
    forall map x a,
      imp_forall_relation_on_aexps_bexps
        (var_map_wf_wrt_aexp map)
        (var_map_wf_wrt_bexp map) (x <- a) ->
      var_map_wf_wrt_aexp map a.
  Proof.
    intros. invs H.
    assumption.
  Defined.

  Lemma imp_rec_rel_assign :
    forall (map: list ident) (x: ident) (a: aexp_Imp_Lang),
      imp_rec_rel (var_map_wf_wrt_imp map) (x <- a) ->
      var_map_wf_wrt_imp map (x <- a).
  Proof.
    intros. invs H. assumption.
  Defined.

  Lemma var_map_wf_wrt_imp_assign :
    forall map x a,
      var_map_wf_wrt_imp map (x <- a) ->
      imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) (x <- a) /\
        forall x0 : ident, imp_has_variable x0 (x <- a) -> In x0 map.
  Proof.
    intros. invs H.
    assumption.
  Defined.

  Lemma imp_lang_log_subst_adequacy_simple :
    forall x a P,
      Imp_LangLogSubst.subst_AbsEnv_rel x a P (Imp_LangLogSubst.subst_AbsEnv x a P).
  Proof.
    intros. apply imp_lang_log_subst_adequacy.
    reflexivity.
  Defined.

  Lemma invs_fun_app_imp_well_formed_assign :
    forall fenv funcs x a,
      fun_app_imp_well_formed fenv funcs (x <- a) ->
      fun_app_well_formed fenv funcs a.
  Proof.
    intros. invs H. assumption.
  Defined.

  Program Definition hl_compile_seq  (P Q R : AbsEnv)
          (i1 i2 : imp_Imp_Lang)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (hl1 : hl_Imp_Lang P i1 R facts fenv)
          (hl2 : hl_Imp_Lang R i2 Q facts fenv)
          (funcs: list fun_Imp_Lang)
          (args : nat)
          (IHhl1 : fact_env_valid facts fenv ->
                   forall funcs : list fun_Imp_Lang,
                     fenv_well_formed' funcs fenv ->
                     forall (map : list ident) (args : nat) (i' : imp_stack),
                       aimp_always_wf funcs map args P i1 R fenv facts hl1 ->
                       fun_app_imp_well_formed fenv funcs i1 ->
                       forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
                         funcs_okay_too funcs fenv0 ->
                         Forall
                           (fun func : fun_Imp_Lang =>
                              all_params_ok (Imp_LangTrickLanguage.Args func)
                                            (Imp_LangTrickLanguage.Body func)) funcs ->
                         PC.check_proof fenv funcs P R i1 facts map args hl1 ->
                         SC.comp_logic args map P = s1 ->
                         SC.comp_logic args map R = s2 ->
                         SC.check_logic P = true ->
                         SC.check_logic R = true ->
                         i' = CC.compile_imp i1 map args ->
                         CC.check_imp i1 = true ->
                         AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) P ->
                         AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) R ->
                         imp_rec_rel (var_map_wf_wrt_imp map) i1 ->
                         PC.valid_imp_trans_def facts facts' fenv fenv0 map args ->
                         hl_stk s1 i' s2 facts' fenv0)
          (IHhl2 : fact_env_valid facts fenv ->
                   forall funcs : list fun_Imp_Lang,
                     fenv_well_formed' funcs fenv ->
                     forall (map : list ident) (args : nat) (i' : imp_stack),
                       aimp_always_wf funcs map args R i2 Q fenv facts hl2 ->
                       fun_app_imp_well_formed fenv funcs i2 ->
                       forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
                         funcs_okay_too funcs fenv0 ->
                         Forall
                           (fun func : fun_Imp_Lang =>
                              all_params_ok (Imp_LangTrickLanguage.Args func)
                                            (Imp_LangTrickLanguage.Body func)) funcs ->
                         PC.check_proof fenv funcs R Q i2 facts map args hl2 ->
                         SC.comp_logic args map R = s1 ->
                         SC.comp_logic args map Q = s2 ->
                         SC.check_logic R = true ->
                         SC.check_logic Q = true ->
                         i' = CC.compile_imp i2 map args ->
                         CC.check_imp i2 = true ->
                         AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) R ->
                         AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) Q ->
                         imp_rec_rel (var_map_wf_wrt_imp map) i2 ->
                         PC.valid_imp_trans_def facts facts' fenv fenv0 map args ->
                         hl_stk s1 i' s2 facts' fenv0)
          (map : list ident)
          (FENV_WF : fenv_well_formed' funcs fenv)
          (FUN_APP : fun_app_imp_well_formed fenv funcs (i1 ;; i2))
          (AIMPWF : aimp_always_wf funcs map args P (i1;; i2) Q fenv facts (hl_Imp_Lang_seq P Q R facts fenv i1 i2 hl1 hl2))
          (fenv0 : fun_env_stk)
          (FUNCS_OK: funcs_okay_too funcs fenv0)
          (FORALL_FUNCS: Forall
                           (fun func : fun_Imp_Lang =>
                              all_params_ok (Imp_LangTrickLanguage.Args func)
                                            (Imp_LangTrickLanguage.Body func)) funcs)
          (s2 s1 : AbsState)
          (i' : imp_stack)
          (H : SC.comp_logic args map P = s1)
          (H0 : SC.comp_logic args map Q = s2)
          (Hcheck_pf : PC.check_proof fenv funcs P Q (i1;; i2) facts map args
         (hl_Imp_Lang_seq P Q R facts fenv i1 i2 hl1 hl2))
          (Hcheck_logicP : SC.check_logic P = true)
          (Hcheck_logicQ : SC.check_logic Q = true)
          (Hcheck : CC.check_imp (i1 ;; i2) = true)
          (H1 : i' = CC.compile_imp (i1;; i2) map args)
          (* (H2 : fenv0 = compile_fenv fenv) *)
          (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
          (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q)
          (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (i1;; i2)) 
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2 facts' fenv0.
  Proof.
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end;
      match goal with
      | [ H: aimp_always_wf ?idents ?i |- _ ] =>
          let AIMPWF := fresh "AIMPWF" in
          pose proof (AIMPWF := H); clear H; unfold aimp_always_wf in *
      | _ => idtac
      end.
    erewrite PC.sequence_compilation_commutes.
    econstructor.
    + invs IRONHIDE. apply (proj2 H0).  
    + eapply IHhl1; try eassumption; try ereflexivity.
      * invs_aimpwf_helper AIMPWF. eassumption.
      * invs FUN_APP; assumption.
      * invs Hcheck_pf; try solve [invs Hi].
        -- invs Hi. specialize (UIP_imp_refl _ Hi). intros. rewrite H6 in H. simpl in H. invs H. inversion_sigma_helper  H10. inversion_sigma_helper H9. eassumption.
        -- invs H.
        -- invs H.
      * invs Hcheck_pf; try solve [invs Hi | invs H].
        invs Hi. erewrite (UIP_imp_refl _ Hi) in H. simpl in H. invs H. inversion_sigma_helper H9. eassumption.
      * eapply PC.sequence_check_implies_all_check with (i2 := i2). eassumption.
        
      * invs_aimpwf_helper AIMPWF.
        assumption.
      * invs IMPWF.
        eassumption.
    + eapply IHhl2; try eassumption; try reflexivity.
      * invs_aimpwf_helper AIMPWF. eassumption.
      * invs FUN_APP. assumption.
      * invs Hcheck_pf; try solve [invs Hi | invs H].
        invs Hi. erewrite (UIP_imp_refl _ Hi) in H. simpl in H. invs H. inversion_sigma_helper H8. inversion_sigma_helper H9. eassumption.
      * invs Hcheck_pf; try solve [invs Hi | invs H ].
        invs Hi. erewrite (UIP_imp_refl _ Hi) in H. simpl in H. invs H. inversion_sigma_helper H8. eassumption.
      * eapply PC.sequence_check_implies_all_check. eassumption.
      * 
        invs_aimpwf_helper AIMPWF.
        assumption.
      * invs IMPWF. eassumption.
    + assumption.
  Defined.
  
  Lemma inv_fun_app_imp_seq :
    forall fenv funcs i1 i2,
      fun_app_imp_well_formed fenv funcs (i1 ;; i2) ->
      fun_app_imp_well_formed fenv funcs i1 /\
        fun_app_imp_well_formed fenv funcs i2.
  Proof.
    intros. invs H. split; assumption.
  Qed.

  Lemma inv_aimpwf_if :
    forall b i1 i2 P Q funcs map args fenv facts hl1 hl2,
      aimp_always_wf funcs map args P (when b then i1 else i2 done) Q fenv facts
                     (hl_Imp_Lang_if P Q b i1 i2 facts fenv hl1 hl2) ->
      aimp_always_wf funcs map args (afalseImp_Lang b P) i2 Q fenv facts hl2 /\
        aimp_always_wf funcs map args (atrueImp_Lang b P) i1 Q fenv facts hl1.
  Proof.
    intros. unfold aimp_always_wf in H. inversion H.
    - inversion HSkip.
    - inversion Heq.
    - inversion Heq.
    - invs heq. specialize (UIP_imp_refl _ heq).
      intros. subst. simpl in H0. invs H0.
      inversion_sigma_helper H13. inversion_sigma_helper H14.
      unfold aimp_always_wf. split; try split; try split; assumption.
    - inversion Heq.
    - inversion H0.
    - inversion H0. 
  Qed.

  Lemma inv_imp_rec_rel_seq :
    forall map i1 i2,
      imp_rec_rel (var_map_wf_wrt_imp map) (i1;; i2) ->
      imp_rec_rel (var_map_wf_wrt_imp map) i1 /\
        imp_rec_rel (var_map_wf_wrt_imp map) i2 /\
        var_map_wf_wrt_imp map (i1;; i2).
  Proof.
    intros. inversion H. unfold Imp_LangImpHigherOrderRel.phi_t in phi. subst.
    split; [ | split ]; auto.
  Qed.

  Lemma inv_imp_rec_rel_if :
    forall map b i1 i2,
      imp_rec_rel (var_map_wf_wrt_imp map)
                  (when b then i1 else i2 done) ->
      imp_rec_rel (var_map_wf_wrt_imp map) i1 /\
        imp_rec_rel (var_map_wf_wrt_imp map) i2 /\
        var_map_wf_wrt_imp map (when b then i1 else i2 done).
  Proof.
    intros. inversion H. subst.
    split; [ | split ]; auto.
  Qed.

  Lemma inv_fun_app_imp_if :
    forall fenv funcs b i1 i2,
      fun_app_imp_well_formed fenv funcs (when b then i1 else i2 done) ->
      fun_app_bexp_well_formed fenv funcs b /\
        fun_app_imp_well_formed fenv funcs i1 /\
        fun_app_imp_well_formed fenv funcs i2.
  Proof.
    intros. invs H.
    split; [ | split ]; eassumption.
  Qed.


  Program Definition hl_compile_if  (P Q : AbsEnv)
          (b : bexp_Imp_Lang)
          (i1 i2 : imp_Imp_Lang)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (hl1 : hl_Imp_Lang (atrueImp_Lang b P) i1 Q facts fenv)
          (hl2 : hl_Imp_Lang (afalseImp_Lang b P) i2 Q facts fenv)
          (funcs: list fun_Imp_Lang)
          (args : nat)
          (IHhl1 : fact_env_valid facts fenv ->
          forall funcs : list fun_Imp_Lang,
          fenv_well_formed' funcs fenv ->
          forall (map : list ident) (args : nat) (i' : imp_stack),
          aimp_always_wf funcs map args (atrueImp_Lang b P) i1 Q fenv
            facts hl1 ->
          fun_app_imp_well_formed fenv funcs i1 ->
          forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
          funcs_okay_too funcs fenv0 ->
          Forall
            (fun func : fun_Imp_Lang =>
             all_params_ok (Imp_LangTrickLanguage.Args func)
                           (Imp_LangTrickLanguage.Body func)) funcs ->
          PC.check_proof fenv funcs (atrueImp_Lang b P) Q i1 facts map args hl1 ->
          SC.comp_logic args map (atrueImp_Lang b P) = s1 ->
          SC.comp_logic args map Q = s2 ->
          SC.check_logic (atrueImp_Lang b P) = true ->
          SC.check_logic Q = true ->
          i' = CC.compile_imp i1 map args ->
          CC.check_imp i1 = true ->
          AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
            (var_map_wf_wrt_bexp map) (atrueImp_Lang b P) ->
          AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
            (var_map_wf_wrt_bexp map) Q ->
          imp_rec_rel (var_map_wf_wrt_imp map) i1 ->
          PC.valid_imp_trans_def facts facts' fenv fenv0 map args ->
          hl_stk s1 i' s2 facts' fenv0)
  (IHhl2 : fact_env_valid facts fenv ->
          forall funcs : list fun_Imp_Lang,
          fenv_well_formed' funcs fenv ->
          forall (map : list ident) (args : nat) (i' : imp_stack),
          aimp_always_wf funcs map args (afalseImp_Lang b P) i2 Q fenv
            facts hl2 ->
          fun_app_imp_well_formed fenv funcs i2 ->
          forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
          funcs_okay_too funcs fenv0 ->
          Forall
            (fun func : fun_Imp_Lang =>
             all_params_ok (Imp_LangTrickLanguage.Args func)
                           (Imp_LangTrickLanguage.Body func)) funcs ->
          PC.check_proof fenv funcs (afalseImp_Lang b P) Q i2 facts map args hl2 ->
          SC.comp_logic args map (afalseImp_Lang b P) = s1 ->
          SC.comp_logic args map Q = s2 ->
          SC.check_logic (afalseImp_Lang b P) = true ->
          SC.check_logic Q = true ->
          i' = CC.compile_imp i2 map args ->
          CC.check_imp i2 = true ->
          AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
            (var_map_wf_wrt_bexp map) (afalseImp_Lang b P) ->
          AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
            (var_map_wf_wrt_bexp map) Q ->
          imp_rec_rel (var_map_wf_wrt_imp map) i2 ->
          PC.valid_imp_trans_def facts facts' fenv fenv0 map args ->
          hl_stk s1 i' s2 facts' fenv0)
          (map : list ident)
          
          (FENV_WF : fenv_well_formed' funcs fenv)
          (FUN_APP : fun_app_imp_well_formed fenv funcs (when b then i1 else i2 done))
          (AIMPWF : aimp_always_wf funcs map args P (when b then i1 else i2 done) Q fenv facts (hl_Imp_Lang_if P Q b i1 i2 facts fenv hl1 hl2))
          (fenv0 : fun_env_stk)
          (OKfuncs: funcs_okay_too funcs fenv0)
          (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs)
          (s2 s1 : AbsState)
          (i': imp_stack)
          (H : SC.comp_logic args map P = s1)
          (H0 : SC.comp_logic args map Q = s2)
          (Hcheck_pf : PC.check_proof fenv funcs P Q (when b then i1 else i2 done) facts map args
         (hl_Imp_Lang_if P Q b i1 i2 facts fenv hl1 hl2))
          (Hcheck_logicP : SC.check_logic P = true)
          (Hcheck_logicQ : SC.check_logic Q = true)
          (H1 : i' = CC.compile_imp (when b then i1 else i2 done) map args)
          (Hcheck: CC.check_imp (when b then i1 else i2 done) = true)
          (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
          (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q)
          (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (when b then i1 else i2 done))
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2 facts' fenv0.
  Proof.
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end.
    simpl.
    unfold CC.compile_imp in *.
    apply inv_imp_rec_rel_if in IMPWF.
    apply inv_fun_app_imp_if in FUN_APP.
    destruct FUN_APP as (FUN_B & FUN_I1 & FUN_I2).
    destruct IMPWF as (IMPWF1 & IMPWF2 & IMPWF).
    erewrite PC.if_compilation_commutes.
    econstructor.
    - destruct IRONHIDE.
      apply (proj2 H0).
    - invs Hcheck_pf; try solve [invs Hi | invs H ]; invs Hi.
      eapply H4; try eassumption.
      unfold_wf_imp_in IMPWF. invs WF'. eassumption.
    - eapply hl_stk_consequence_STKONLY.
      * eapply IHhl1; try eassumption.
        -- invs_aimpwf_helper AIMPWF.
           invs H4; eassumption.
        -- invs Hcheck_pf; try solve [invs Hi | invs H].
           invs Hi. erewrite (UIP_imp_refl _ Hi) in H. simpl in H. invs H.
           inversion_sigma_helper H10. inversion_sigma_helper H11. assumption.
        -- reflexivity.
        -- reflexivity.
        -- unfold atrueImp_Lang. eapply PC.spec_lp_conjunction_check.
           ++ eassumption.
           ++ eapply PC.if_check_implies_condition_then_else_check; eassumption.
        -- reflexivity.
        -- eapply PC.if_check_implies_condition_then_else_check in Hcheck. eapply (proj1 (proj2 Hcheck)).
        -- unfold atrueImp_Lang. econstructor.
           assumption.
           econstructor.
           econstructor.
           econstructor.
           
           unfold_wf_imp_in IMPWF.
           invs WF'. eassumption.
      * unfold atrueImp_Lang. simpl.
        
        unfold atruestk.
        unfold SC.comp_logic. rewrite PC.spec_conjunction_commutes.
        rewrite Nat.add_comm.
        eapply PC.size_change_implication_okay.
        -- eassumption.
        -- eassumption.
        -- reflexivity.
        -- eassumption.
        -- eapply PC.if_check_implies_condition_then_else_check; eassumption.
        -- reflexivity.
        -- eapply PC.spec_lp_conjunction_check. eassumption. eapply PC.if_check_implies_condition_then_else_check; eassumption.
        -- eassumption.
        -- eapply PC.if_check_implies_condition_then_else_check; eassumption.
      * eapply self_implication.
    - eapply hl_stk_consequence_STKONLY.
      + eapply IHhl2; try eassumption.
        * invs_aimpwf_helper AIMPWF.
          eassumption.
        * invs Hcheck_pf; try (invs Hi); try solve [invs H].
          erewrite (UIP_imp_refl _ Hi) in H. simpl in H. invs H. inversion_sigma_helper H10. inversion_sigma_helper H11. eassumption.
        * reflexivity.
        * reflexivity.
        * unfold afalseImp_Lang. eapply PC.spec_lp_conjunction_check. eassumption. eapply PC.if_check_implies_condition_then_else_check; eassumption.
        * reflexivity.
        * eapply PC.if_check_implies_condition_then_else_check in Hcheck.
          eapply (proj2 (proj2 Hcheck)).
        * unfold afalseImp_Lang. econstructor.
          -- eassumption.
          -- econstructor. econstructor. econstructor.
             unfold_wf_imp_in  IMPWF. invs WF'. eassumption.
      + unfold afalseImp_Lang.
        erewrite PC.spec_conjunction_commutes.  unfold SC.comp_logic.
        rewrite Nat.add_comm.
        eapply PC.size_change_implication_okay.
        * eassumption.
        * eassumption.
        * reflexivity.
        * eassumption.
        * eapply PC.if_check_implies_condition_then_else_check; eassumption.
        * unfold afalsestk. reflexivity.
        * eapply PC.spec_lp_conjunction_check.
          -- eassumption.
          -- eapply PC.if_check_implies_condition_then_else_check. eassumption.
        * eassumption.
        * eapply PC.if_check_implies_condition_then_else_check. eassumption.
      + eapply self_implication.
    - eassumption.
  Defined.

  Lemma inv_imp_forall_if_get_cond :
    forall map b i1 i2,
      imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) (when b then i1 else i2 done) ->
      var_map_wf_wrt_bexp map b.
  Proof.
    intros. invs H.
    assumption.
  Qed.

  Lemma inv_fun_app_imp_if_get_cond :
    forall fenv funcs b i1 i2,
      fun_app_imp_well_formed fenv funcs (when b then i1 else i2 done) ->
      fun_app_bexp_well_formed fenv funcs b.
  Proof.
    intros. invs H.
    assumption.
  Qed.

  Lemma var_map_wf_wrt_imp_if_imp_forall :
    forall map b i1 i2,
      var_map_wf_wrt_imp map (when b then i1 else i2 done) ->
      imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp map)
                                         (var_map_wf_wrt_bexp map) (when b then i1 else i2 done).
  Proof.
    intros. unfold var_map_wf_wrt_imp in H.
    destruct H as (_ & ? & _).
    assumption.
  Qed.


  Lemma inv_impwf_while :
    forall map b i,
      imp_rec_rel (var_map_wf_wrt_imp map) (while b loop i done) ->
      imp_rec_rel (var_map_wf_wrt_imp map) i /\
        var_map_wf_wrt_imp map (while b loop i done).
  Proof.
    intros. invs H.
    split; assumption.
  Qed.

  Lemma inv_fun_app_imp_while :
    forall fenv funcs b i,
      fun_app_imp_well_formed fenv funcs (while b loop i done) ->
      fun_app_bexp_well_formed fenv funcs b /\
        fun_app_imp_well_formed fenv funcs i.
  Proof.
    intros; invs H; split; assumption.
  Qed.
  

  
  Program Definition hl_compile_while (P : AbsEnv)
          (b : bexp_Imp_Lang)
          (i : imp_Imp_Lang)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (hl : hl_Imp_Lang (atrueImp_Lang b P) i P facts fenv)
          (funcs: list fun_Imp_Lang)
          (args : nat)
          (IHhl : fact_env_valid facts fenv ->
                  forall funcs : list fun_Imp_Lang,
                    fenv_well_formed' funcs fenv ->
                    forall (map : list ident) (args : nat) (i' : imp_stack),
                      aimp_always_wf funcs map args (atrueImp_Lang b P) i P fenv facts
                                     hl ->
                      fun_app_imp_well_formed fenv funcs i ->
                      forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
                        funcs_okay_too funcs fenv0 ->
                        Forall
                          (fun func : fun_Imp_Lang =>
                             all_params_ok (Imp_LangTrickLanguage.Args func)
                                           (Imp_LangTrickLanguage.Body func)) funcs ->
                        PC.check_proof fenv funcs (atrueImp_Lang b P) P i facts map args hl ->
                        SC.comp_logic args map (atrueImp_Lang b P) = s1 ->
                        SC.comp_logic args map P = s2 ->
                        SC.check_logic (atrueImp_Lang b P) = true ->
                        SC.check_logic P = true ->
                        i' = CC.compile_imp i map args ->
                        CC.check_imp i = true ->
                        AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                        (var_map_wf_wrt_bexp map) (atrueImp_Lang b P) ->
                        AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                        (var_map_wf_wrt_bexp map) P ->
                        imp_rec_rel (var_map_wf_wrt_imp map) i ->
                        PC.valid_imp_trans_def facts facts' fenv fenv0 map args ->
                        hl_stk s1 i' s2 facts' fenv0)
          (map : list ident)
          (FENV_WF : fenv_well_formed' funcs fenv)
          (FUN_APP : fun_app_imp_well_formed fenv funcs (while b loop i done))
          (AIMPWF : aimp_always_wf funcs map args P (while b loop i done) (afalseImp_Lang b P) fenv facts (hl_Imp_Lang_while P b i facts fenv hl))
          (fenv0 : fun_env_stk)
          (OKfuncs: funcs_okay_too funcs fenv0)
          (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs)
          (i' : imp_stack)
          (s2 s1 : AbsState)
          (H : SC.comp_logic args map P = s1)
          (H0 : SC.comp_logic args map (afalseImp_Lang b P) = s2)
          (Hcheck_pf: PC.check_proof fenv funcs P (afalseImp_Lang b P)
                                     (while b loop i done) facts map args
                                     (hl_Imp_Lang_while P b i facts fenv hl))
          (Hcheck_logicP : SC.check_logic P = true)
          (Hcheck_logicbP : SC.check_logic (afalseImp_Lang b P) = true)
          (H1 : i' = comp_code (while b loop i done) map args)
          (Hcheck: CC.check_imp (while b loop i done) = true)
          (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
          (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (afalseImp_Lang b P))
          (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (while b loop i done))
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2 facts' fenv0.
  Proof.
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end.
    simpl.
    pose proof (Hcheck' := PC.while_check_implies_condition_loop_check b i Hcheck).
    destruct Hcheck' as (Hcheckb & Hchecki).
    pose proof (HchecktruebP := PC.spec_lp_conjunction_check P b (fun v => v = true) Hcheck_logicP Hcheckb).
    unfold afalseImp_Lang. rewrite PC.spec_conjunction_commutes; [ | eassumption .. ]. unfold SC.comp_logic. rewrite PC.while_compilation_commutes; [ | eassumption .. ].
    econstructor.
    - eapply hl_stk_while.
      + destruct IRONHIDE. apply (proj2 H0).
      + invs Hcheck_pf; try solve [invs Hi | invs H]. invs Hi.
        eapply H3; try eassumption.
        (* eapply PC.compiled_bexps_are_pure; try eassumption. *)
        invs FUN_APP. eassumption.
        invs IMPWF. unfold_wf_imp_in H11. invs WF'. eassumption.
      + unfold atruestk. eapply hl_stk_consequence_STKONLY.
        * eapply IHhl; try eassumption; try reflexivity.
          -- invs_aimpwf_helper AIMPWF. eassumption.
          -- invs FUN_APP. eassumption.
          -- invs Hcheck_pf; try invs Hi; try solve [invs H].
             rewrite (UIP_imp_refl _ Hi) in H. simpl in H.
             rewrite (Imp_LangLogPropDec.UIP_AbsEnv_refl _ HeqP) in H. simpl in H. invs H. inversion_sigma_helper H8. eassumption.
          -- unfold atrueImp_Lang. econstructor. eassumption.
             econstructor. econstructor. econstructor.
             invs IMPWF. unfold_wf_imp_in H3. invs WF'. eassumption.
          -- invs IMPWF. eassumption.
        * unfold atrueImp_Lang. unfold SC.comp_logic. rewrite PC.spec_conjunction_commutes. rewrite Nat.add_comm. eapply PC.size_change_implication_okay.
          -- eassumption.
          -- eassumption.
          -- reflexivity.
          -- eassumption.
          -- eassumption.
          -- reflexivity.
          -- eassumption.
          -- eassumption.
          -- eassumption.
        * eapply self_implication.
    - eapply self_implication.
    - unfold afalsestk. rewrite Nat.add_comm. eapply PC.size_change_implication_okay; [ eassumption | eassumption | reflexivity | .. ].
      + eassumption.
      + eassumption.
      + reflexivity.
  Defined.

  Lemma inv_aimpwf_while :
    forall funcs map args P b i fenv facts hl,
      aimp_always_wf funcs map args P (while b loop i done) (afalseImp_Lang b P) fenv facts (hl_Imp_Lang_while P b i facts fenv hl) ->
      aimp_always_wf funcs map args (atrueImp_Lang b P) i P fenv facts hl.
  Proof.
    intros. invs H.
    - inversion HSkip.
    - inversion Heq.
    - inversion Heq.
    - inversion heq.
    - invs Heq.
      specialize (UIP_imp_refl _ Heq).
      intros. subst. simpl in *.
      specialize (Imp_LangLogPropDec.UIP_AbsEnv_refl _ HeqP).
      intros. subst. simpl in H0.
      invs H0.
      inversion_sigma_helper H8.
      unfold aimp_always_wf. assumption.
    - invs H0.
    - invs H0.  
  Defined.

  Lemma inv_imp_rec_rel_while :
    forall map b i,
      imp_rec_rel (var_map_wf_wrt_imp map) (while b loop i done) ->
      imp_rec_rel (var_map_wf_wrt_imp map) i /\
        var_map_wf_wrt_imp map (while b loop i done).
  Proof.
    intros. invs H.
    split; assumption.
  Qed.

  Lemma atrueImp_Lang_well_formed :
    forall map P b i,
      AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                      (var_map_wf_wrt_bexp map) P ->
      var_map_wf_wrt_imp map (while b loop i done) ->
      AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map)
                      (atrueImp_Lang b P).
  Proof.
    intros.
    unfold_wf_imp_in H0.
    invs WF'.
    clear WF''. clear WF.
    constructor.
    - assumption.
    - constructor. constructor. constructor.
      assumption.
  Qed.

  Lemma fact_cert_implies_implication : 
    forall fenv facts,
      fact_env_valid facts fenv ->
      (forall n P P', 
          nth_error facts n = Some (P, P') ->
          aimpImp_Lang P P' fenv).
  Proof.
    intros. unfold fact_env_valid in H. apply H. apply (nth_error_In facts n H0).
  Qed.       

  Lemma fact'_cert_implies_implication : 
    forall fenv facts,
      StackLogic.fact_env_valid facts fenv ->
      (forall n P P', 
          nth_error facts n = Some (P, P') ->
          aimpstk P P' fenv).
  Proof.
    intros. unfold StackLogic.fact_env_valid in H. apply H. apply (nth_error_In facts n H0).
  Qed.       


  Program Definition hl_compile_consequence_pre (P Q P': AbsEnv)
          (c : imp_Imp_Lang)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (hl : hl_Imp_Lang P c Q facts fenv)
          n
          (e : nth_error facts n = Some (P', P))
          (a : aimpImp_Lang P' P fenv)
          (funcs: list fun_Imp_Lang)
          (args : nat)
          (IHhl : fact_env_valid facts fenv ->
                  forall funcs : list fun_Imp_Lang,
                    fenv_well_formed' funcs fenv ->
                    forall (map : list ident) (args : nat) (i' : imp_stack),
                      aimp_always_wf funcs map args P c Q fenv facts hl ->
                      fun_app_imp_well_formed fenv funcs c ->
                      forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
                        funcs_okay_too funcs fenv0 ->
                        Forall
                          (fun func : fun_Imp_Lang =>
                             all_params_ok (Imp_LangTrickLanguage.Args func)
                                           (Imp_LangTrickLanguage.Body func)) funcs ->
                        PC.check_proof fenv funcs P Q c facts map args hl ->
                        SC.comp_logic args map P = s1 ->
                        SC.comp_logic args map Q = s2 ->
                        SC.check_logic P = true ->
                        SC.check_logic Q = true ->
                        i' = CC.compile_imp c map args ->
                        CC.check_imp c = true ->
                        AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                        (var_map_wf_wrt_bexp map) P ->
                        AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                                        (var_map_wf_wrt_bexp map) Q ->
                        imp_rec_rel (var_map_wf_wrt_imp map) c ->
                        PC.valid_imp_trans_def facts facts' fenv fenv0 map args ->
                        hl_stk s1 i' s2 facts' fenv0)
          (map : list ident)
          (FENV_WF : fenv_well_formed' funcs fenv)
          (FUN_APP : fun_app_imp_well_formed fenv funcs c)
          (AIMPWF : aimp_always_wf funcs map args P' c Q fenv facts (hl_Imp_Lang_consequence_pre P Q P' c n facts fenv hl e a))
          (s2 s1 : AbsState)
          (i' : imp_stack)
          (fenv0: fun_env_stk)
          (OKfuncs: funcs_okay_too funcs fenv0)
          (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs)
          (H : SC.comp_logic args map P' = s1)
          (H0 : SC.comp_logic args map Q = s2)
          (Hcheck_pf : PC.check_proof fenv funcs P' Q c facts map args
                                      (hl_Imp_Lang_consequence_pre P Q P' c n facts fenv hl e a))
          (HcheckP' : SC.check_logic P' = true)
          (HcheckQ : SC.check_logic Q = true)
          (H1 : i' = CC.compile_imp c map args)
          (Hcheck : CC.check_imp c = true)
          (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P')
          (H5 : imp_rec_rel (var_map_wf_wrt_imp map) c)
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2 facts' fenv0.
  Proof. 
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end.
    pose proof IRONHIDE as Q1.
    pose proof (a' := a).
    pose proof (IMPWF' := IMPWF).
    eapply imp_rec_rel_var_map_wf_adequacy in IMPWF'.
    eapply imp_rec_rel_self in IMPWF.
    unfold aimp_always_wf in AIMPWF.
    destruct (inv_aimpwf_consequence_pre _ _ _ _ _ _ _ _ _ _ _ _ _ AIMPWF) as (lwf1 & lwf2 & lwf3 & lwf4 & lwf5 & lwf6 & rel1 & rel2 & rel3 & _).
    unfold PC.valid_imp_trans_def in IRONHIDE.
    destruct IRONHIDE as (P1 & P2).
    destruct P2 as (P3 & P4).
    enough (HcheckP: SC.check_logic P = true).
    pose proof P3 n P' P (PC.SC.comp_logic args map P') (PC.SC.comp_logic args map P) (HcheckP') (HcheckP) eq_refl eq_refl e as P5.
    pose proof (fact'_cert_implies_implication fenv0 facts' P4 n (PC.SC.comp_logic args map P') (PC.SC.comp_logic args map P) P5) as P10.

    eapply hl_stk_consequence_pre; try assumption.
    
    - eapply IHhl; try eassumption; try ereflexivity.    
      +  invs_aimpwf_helper AIMPWF; try (simpl in H; invs H).
         clear H17.
         inversion_sigma_helper H15.
         eassumption.
      + invs Hcheck_pf; try invs H. inversion_sigma_helper H8. eassumption.
      + invs_aimpwf_helper AIMPWF; try (simpl in H; invs H).
        clear H17. inversion_sigma_helper H15. eassumption.
    - eassumption.
    - invs Hcheck_pf; try invs H. inversion_sigma_helper H8. eassumption.
  Defined.

  Print hl_compile_consequence_pre.

  Program Definition hl_compile_consequence_post (P Q Q': AbsEnv)
          (c : imp_Imp_Lang)
          (fenv : fun_env)
          (facts : implication_env)
          (fact_cert : fact_env_valid facts fenv)
          facts'
          (hl : hl_Imp_Lang P c Q facts fenv)
          n
          (e : nth_error facts n = Some (Q, Q'))
          (a : aimpImp_Lang Q Q' fenv)
          (funcs: list fun_Imp_Lang)
          (args : nat)
          (IHhl :
            fact_env_valid facts fenv ->
            forall (funcs : list fun_Imp_Lang),
              fenv_well_formed' funcs fenv ->
              forall (map : list ident) (args : nat) (i' : imp_stack),
                aimp_always_wf funcs map args P c Q fenv facts hl ->
                fun_app_imp_well_formed fenv funcs c ->
                forall (fenv0 : fun_env_stk) (s2 s1 : AbsState),
                  funcs_okay_too funcs fenv0 ->
                  Forall
                    (fun func : fun_Imp_Lang =>
                       all_params_ok
                         (Imp_LangTrickLanguage.Args func)
                         (Imp_LangTrickLanguage.Body func)) funcs ->
                  PC.check_proof fenv funcs P Q c facts map args hl ->
                  SC.comp_logic args map P = s1 ->
                  SC.comp_logic args map Q = s2 ->
                  SC.check_logic P = true ->
                  SC.check_logic Q = true ->
                  i' = CC.compile_imp c map args ->
                  CC.check_imp c = true ->
                  AbsEnv_prop_rel (var_map_wf_wrt_aexp map) 
                                  (var_map_wf_wrt_bexp map) P ->
                  AbsEnv_prop_rel (var_map_wf_wrt_aexp map) 
                                  (var_map_wf_wrt_bexp map) Q ->
                  imp_rec_rel (var_map_wf_wrt_imp map) c ->
                  PC.valid_imp_trans_def
                    facts facts' fenv fenv0 map args ->
                  hl_stk s1 i' s2 facts' fenv0)
          (map : list ident)
          (FENV_WF : fenv_well_formed' funcs fenv)
          (FUN_APP : fun_app_imp_well_formed fenv funcs c)
          (AIMPWF : aimp_always_wf funcs map args P c Q' fenv facts (hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl e a))
          (s2 s1 : AbsState)
          (i' : imp_stack)
          (fenv0: fun_env_stk)
          (OKfuncs: funcs_okay_too funcs fenv0)
          (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs)
          (H : SC.comp_logic args map P = s1)
          (H0 : SC.comp_logic args map Q' = s2)
          (Hcheck_pf: PC.check_proof fenv funcs P Q' c facts map args
                                     (hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl e a))
          (HcheckP : SC.check_logic P = true)
          (HcheckQ' : SC.check_logic Q' = true)
          (H1 : i' = CC.compile_imp c map args)
          (Hcheck : CC.check_imp c = true)
          (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q')
          (H5 : imp_rec_rel (var_map_wf_wrt_imp map) c)
          (IRONHIDE : PC.valid_imp_trans_def facts facts' fenv fenv0 map args):
    hl_stk s1 i' s2 facts' fenv0.
  Proof. 
    pose proof IRONHIDE as Q1. 
    unfold comp_code in *; subst;
      rename_fresh_until_no_match;
      match goal with
      | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
          let IMPWF := fresh "IMPWF" in
          pose proof (IMPWF := H); clear H
      | _ => idtac
      end.
    unfold SC.comp_logic. unfold CC.compile_imp.
    pose proof (a' := a).
    pose proof (IMPWF' := IMPWF).
    eapply imp_rec_rel_var_map_wf_adequacy in IMPWF'.
    eapply imp_rec_rel_self in IMPWF.
    unfold aimp_always_wf in AIMPWF.
    destruct (inv_aimpwf_consequence_post _ _ _ _ _ _ _ _ _ _ _ _ _ AIMPWF) as (lwf1 & lwf2 & lwf3 & lwf4 & lwf5 & lwf6 & rel1 & rel2 & rel3 & _).
    unfold PC.valid_imp_trans_def in IRONHIDE.
    destruct IRONHIDE as (P1 & P3 & P4).
    enough (HcheckQ : SC.check_logic Q = true).
    pose proof P3 n Q Q' (SC.comp_logic args map Q) (SC.comp_logic args map Q') HcheckQ HcheckQ' eq_refl eq_refl e as P5.
    pose proof (fact'_cert_implies_implication fenv0 facts' P4 n (SC.comp_logic args map Q) (SC.comp_logic args map Q') P5) as P10.
    eapply hl_stk_consequence_post; try assumption.
    - eapply IHhl; try eassumption; try ereflexivity.    
      +  invs_aimpwf_helper AIMPWF; try (simpl in H; invs H).
         clear H17.
         inversion_sigma_helper H15.
         eassumption.
      + invs Hcheck_pf; try invs H. inversion_sigma_helper H8. eassumption.
      + invs_aimpwf_helper AIMPWF; try (simpl in H; invs H).
        eassumption.
    - eassumption.
    - invs Hcheck_pf; try invs H. inversion_sigma_helper H8. eassumption.
  Defined.

  Lemma inv_aimpwf_consequence_pre' :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      AbsEnv_prop_wf map P /\
        AbsEnv_prop_wf map Q' /\
        aimp_always_wf funcs map args P c Q' fenv facts hl.
  Proof.
    intros. unfold aimp_always_wf in H. inversion H.
    - subst. inversion H0.
    - subst. inversion H0.
    - subst. inversion H0.
    - subst. inversion H0.
    - subst. inversion H0.
    - invs H0.
      inversion_sigma_helper H19.
      split; [ | split ]; assumption.
    - invs H0.
  Qed.

  Lemma inv_aimpwf_consequence_post' :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts (hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      AbsEnv_prop_wf map P /\
        AbsEnv_prop_wf map Q /\
        aimp_always_wf funcs map args P c Q fenv facts hl.
  Proof.
    intros. unfold aimp_always_wf in H. inversion H.
    - subst. inversion H0.
    - subst. inversion H0.
    - subst. inversion H0.
    - subst. inversion H0.
    - subst. inversion H0.
    - invs H0.
    - invs H0.
      inversion_sigma_helper H19.
      split; [ | split ]; assumption.
  Qed.

  Lemma inv_aimpwf_consequence_pre_log_Imp_Lang_wf_P :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf funcs fenv P.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_log_Imp_Lang_wf_map_P :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf_map map P.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_params_ok_P :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      AbsEnv_prop_rel (all_params_ok_aexp args) (all_params_ok_bexp args) P.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_log_Imp_Lang_wf_P :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf funcs fenv P.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_params_ok_P :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      AbsEnv_prop_rel (all_params_ok_aexp args) (all_params_ok_bexp args) P.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_log_Imp_Lang_wf_map_P :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf_map map P.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_log_Imp_Lang_wf_P' :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf funcs fenv P'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_params_ok_P' :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      AbsEnv_prop_rel (all_params_ok_aexp args) (all_params_ok_bexp args) P'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_log_Imp_Lang_wf_map_P' :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf_map map P'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_log_Imp_Lang_wf_Q :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf funcs fenv Q'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_params_ok_Q :
    forall funcs map args P' c Q fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q fenv facts(hl_Imp_Lang_consequence_pre P Q P' c n facts fenv hl a imp) ->
      AbsEnv_prop_rel (all_params_ok_aexp args) (all_params_ok_bexp args) Q.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_pre_log_Imp_Lang_wf_map_Q :
    forall funcs map args P' c Q' fenv P facts hl n a imp,
      aimp_always_wf funcs map args P' c Q' fenv facts(hl_Imp_Lang_consequence_pre P Q' P' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf_map map Q'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_pre funcs map args P Q' P' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_log_Imp_Lang_wf_Q :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf funcs fenv Q.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_params_ok_Q :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      AbsEnv_prop_rel (all_params_ok_aexp args) (all_params_ok_bexp args) Q.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_log_Imp_Lang_wf_map_Q :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf_map map Q.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_log_Imp_Lang_wf_Q' :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf funcs fenv Q'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_params_ok_Q' :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      AbsEnv_prop_rel (all_params_ok_aexp args) (all_params_ok_bexp args) Q'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma inv_aimpwf_consequence_post_log_Imp_Lang_wf_map_Q' :
    forall funcs map args P c Q' fenv Q facts hl n a imp,
      aimp_always_wf funcs map args P c Q' fenv facts(hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
      log_Imp_Lang_wf_map map Q'.
  Proof.
    intros. pose proof (inv_aimpwf_consequence_post funcs map args P Q Q' c fenv n facts hl a imp H). intuition.
  Qed.

  Lemma imp_rec_rel_var_map_wf_nodup_idents :
    forall (idents: list ident) (c: imp_Imp_Lang),
      imp_rec_rel (var_map_wf_wrt_imp idents) c ->
      NoDup idents.
  Proof.
    intros. eapply imp_rec_rel_self in H.
    unfold_wf_imp_in H. eapply WF.
  Qed.
  

  
  Definition induction_P (d: AbsEnv) (i: imp_Imp_Lang) (d0: AbsEnv) (f: fun_env) (facts : implication_env) (fact_cert : fact_env_valid facts f) facts' (hl: hl_Imp_Lang d i d0 facts f): Type :=
    forall (funcs: list fun_Imp_Lang),
      fenv_well_formed' funcs f ->
      forall (map: list ident) (args : nat)
        (s1: AbsState) (i': imp_stack)
        (s2: AbsState) (fenv: fun_env_stk),
      forall (OKfuncs: funcs_okay_too funcs fenv)
        (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs),
        fun_app_imp_well_formed f funcs i ->
        aimp_always_wf funcs map args d i d0 f facts hl ->
        PC.check_proof f funcs d d0 i facts map args hl ->
        SC.comp_logic args map d = s1 ->
        SC.comp_logic args map d0 = s2 ->
        SC.check_logic d = true ->
        SC.check_logic d0 = true ->
        i' = CC.compile_imp i map args ->
        CC.check_imp i = true ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d0 ->
        imp_rec_rel (var_map_wf_wrt_imp map) i ->
        PC.valid_imp_trans_def facts facts' f fenv map args ->
        hl_stk s1 i' s2 facts' fenv.

  Program Definition hl_compile (d1 d2: AbsEnv) (i: imp_Imp_Lang) (fenv: fun_env) (facts : implication_env) (fact_cert : fact_env_valid facts fenv) facts'  (hl: hl_Imp_Lang d1 i d2 facts fenv): induction_P d1 i d2 fenv facts fact_cert facts' hl.
  Proof.
    unfold induction_P.
    intros ? ? ? ? ? ? ? ? ? ? ? AIMPWF. revert OKfuncs OKparams.
    revert fenv0 s2 s1. revert H0.
    dependent induction hl; intros.
    - eapply hl_compile_skip; try eassumption.
    - rename fact_env into facts. eapply hl_compile_assign; try eassumption.
    - eapply hl_compile_seq;[ | eapply IHhl1 | eapply IHhl2 | .. ]; try eassumption.
    - eapply hl_compile_if; try eassumption.
    - eapply hl_compile_while; try eassumption.
    - eapply hl_compile_consequence_pre; try eassumption.
    - eapply hl_compile_consequence_post; try eassumption.
  Defined.

  Definition proof_compiler := hl_compile.

End CompilerAgnosticProofCompiler.
