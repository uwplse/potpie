From Coq Require Import List Arith String Program.Equality.
From DanTrick Require Import DanTrickLanguage StackLanguage StackLangTheorems ProofCompiler.
From DanTrick Require Import DanLogSubst DanLogProp DanLogHoare StackLogic.
From DanTrick Require Import LogicTranslationBase EnvToStack LogicProp ProofCompilerHelpers DanImpHigherOrderRel DanHoareWF LogicTranslationAdequate.
From DanTrick Require Import ProofCompMod ProofCompilerPostHelpers.
From DanTrick Require Import FunctionWellFormed CompilerAssumptionLogicTrans.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Definition hl_compile := Tests.hl_compile.

Module Simplest'.
  Definition program: imp_Dan :=
    SKIP_Dan.

  Definition precond: AbsEnv :=
    AbsEnvLP (Dan_lp_bool (TrueProp bool bexp_Dan)).
  Definition postcond: AbsEnv := precond.

  Definition fenv: fun_env := init_fenv.

  Definition hoare_triple: hl_Dan precond program postcond fenv :=
    hl_Dan_skip precond fenv.

  Definition idents: list ident := nil.

  Definition num_args := 0.

  Definition funcs := (init_fenv "id") :: nil.
End Simplest'.

Module SimplestTargetOther := TargetProgram(Simplest').




Module Simplest.
  Definition program: imp_Dan :=
    SKIP_Dan.

  Definition cond: AbsEnv :=
    AbsEnvLP (Dan_lp_bool (TrueProp bool bexp_Dan)).

  Definition fenv: fun_env := init_fenv.

  Definition hoare_triple: hl_Dan cond program cond fenv :=
    hl_Dan_skip cond fenv.

  Definition idents: list ident := nil.

  Definition num_args := 0.

  Definition funcs := (init_fenv "id") :: nil.
End Simplest.



Module SimplestTarget.
  Definition program: imp_stack :=
    Skip_Stk.

  Definition cond : AbsState :=
    BaseState (AbsStkSize 0) (MetaBool (TrueProp bool bexp_stack)).

  Definition fenv: fun_env_stk := compile_fenv Simplest.fenv.

  Definition hoare_triple: hl_stk cond program cond fenv :=
    hl_stk_skip cond fenv.
End SimplestTarget.

Require Import TranslationPure.
Require Import ParamsWellFormed.

Module SimplestCompile <: CompileType.
  Module SOURCE := Simplest'.
  Module TARGET := SimplestTargetOther.
  
  Definition map: list string := nil.
  Definition args := 0.

  Lemma fenv_well_formed_proof :
    fenv_well_formed' SOURCE.funcs SOURCE.fenv.
  Proof.
    unfold fenv_well_formed'.
    split; intros.
    - unfold SOURCE.funcs. constructor. unfold not; intros. invs H. constructor.
    - split; [ | split ].
      + unfold SOURCE.fenv in H. unfold init_fenv in H. rewrite H. unfold SOURCE.funcs. unfold init_fenv. right. reflexivity.
      + unfold SOURCE.fenv, SOURCE.funcs. unfold init_fenv.
        unfold SOURCE.fenv in H. unfold init_fenv in H. rewrite H. simpl.
        constructor. constructor.
      + unfold SOURCE.fenv in H. unfold init_fenv in H.
        rewrite H. simpl. constructor. eapply String.eqb_eq. reflexivity.
  Qed.

  Lemma funcs_okay_too_proof :
    funcs_okay_too SOURCE.funcs TARGET.fenv.
  Proof.
    unfold funcs_okay_too, SOURCE.funcs, TARGET.fenv.
    constructor.
    - constructor.
      + simpl. econstructor.
        * econstructor.
        * econstructor.
          all: unfold stack_mapping; simpl.
          reflexivity. econstructor. constructor. econstructor. econstructor. reflexivity. reflexivity.
      + simpl. econstructor; unfold stack_mapping; simpl.
        reflexivity. econstructor. reflexivity.
    - constructor.
  Qed.

  Lemma all_params_ok_for_funcs_proof :
    Forall (fun func => all_params_ok (DanTrickLanguage.Args func)
                                   (DanTrickLanguage.Body func)) SOURCE.funcs.
  Proof.
    unfold SOURCE.funcs. econstructor.
    - simpl. econstructor. constructor. econstructor.
    - constructor.
  Qed.

  Lemma fun_app_well_formed_proof :
    fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
  Proof.
    unfold SOURCE.program.
    constructor.
  Qed.
  
  Lemma aimp_always_wf_proof :
    aimp_always_wf SOURCE.funcs map SOURCE.num_args Simplest.cond Simplest.program Simplest.cond Simplest.fenv Simplest.hoare_triple.
  Proof.
    unfold aimp_always_wf, map, Simplest.hoare_triple, Simplest.cond, Simplest.program, Simplest.cond, Simplest.fenv, Simplest.hoare_triple, SOURCE.funcs.
    assert (Simplest.cond = Simplest.cond).
    reflexivity.
    specialize (DanLogPropDec.UIP_AbsEnv_refl _ H).
    intros.
    assert (SKIP_Dan = SKIP_Dan) by reflexivity.
    specialize (UIP_imp_refl _ H1). intros.
    apply HLDanWFSkip with (Heq := H) (HSkip := H1).
    - subst. simpl. reflexivity.
    - constructor. constructor. constructor.
    - constructor. constructor. constructor.
    - constructor. constructor. constructor.
    - constructor. constructor. constructor.
  Defined.

  Lemma translate_precond_proof :
    logic_transrelation args map Simplest.cond SimplestTarget.cond.
  Proof.
    unfold Simplest.cond, SimplestTarget.cond.
    apply log_comp_adequacy. simpl. reflexivity.
  Defined.

  Definition translate_postcond_proof := translate_precond_proof.

  Lemma terminator_proof :
    terminator SOURCE.fenv SOURCE.num_args Simplest.cond Simplest.cond Simplest.program SOURCE.hoare_triple.
  Proof.
    unfold_everything_once.
    unfold SOURCE.fenv. unfold SOURCE.num_args. unfold Simplest.cond. unfold SOURCE.precond.
    simpl.
    constructor. repeat constructor.
  Defined.
 
  Lemma program_compiled_proof :
    SimplestTarget.program = comp_code Simplest.program map args.
  Proof.
    reflexivity.
  Defined.

  Lemma fun_env_compiled_proof :
    SimplestTarget.fenv = compile_fenv Simplest.fenv.
  Proof.
    reflexivity.
  Defined.

  Lemma precond_wf_proof :
    AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Simplest.cond.
  Proof.
    unfold Simplest.cond. constructor. constructor. constructor.
  Defined.

  Definition postcond_wf_proof := precond_wf_proof.

  Lemma imp_code_wf_proof :
    imp_rec_rel (var_map_wf_wrt_imp map) Simplest.program.
  Proof.
    unfold Simplest.program, map.
    constructor.
    unfold_wf_imp.
    - split; [ | split; [ | split ] ]; intros.
      + constructor.
      + split; intros.
        invs H0.
        invs H. simpl in H2. invs H2.
      + invs H.
      + invs H.
    - constructor.
    - intros. invs H.
  Defined.
  
End SimplestCompile.

Module SmallerCompiler <: CompilerType.
  Definition proof_compiler := Tests.hl_compile_smaller.
End SmallerCompiler.

Module SCCompiled := CompileProof SimplestCompile SmallerCompiler.

Eval compute in "The tiniest possible proof...".
Time Eval compute in (SCCompiled.compiled).

Module LessSimpleExample.
  (** Transparently give the module AssignDan the SourceProgramType
    * module type *)
  Module AssignDan <: SourceProgramType.
    Definition program := ASSIGN_Dan "z" (CONST_Dan 0).
    Definition postcond := AbsEnvLP (Dan_lp_arith (UnaryProp _ _ (fun x => x = 0) (VAR_Dan "z"))).
    Definition precond := DanLogSubst.subst_AbsEnv "z" (CONST_Dan 0) postcond.
    Definition fenv := init_fenv.
    Definition hoare_triple :=
      hl_Dan_assign postcond fenv "z" (CONST_Dan 0).
    Definition idents := "z" :: nil.
    Definition num_args := 0.
    Definition funcs := ((init_fenv "id") :: nil).
  End AssignDan.

  Module AssignStk := TargetProgram AssignDan.

  Module CompileAssign <: CompileType.
    Module SOURCE := AssignDan.
    Module TARGET := AssignStk.

    Lemma var_in_idents_implies_wf :
      forall (idents: list ident) (x: ident),
        In x idents ->
        NoDup idents ->
        var_map_wf_wrt_aexp idents (VAR_Dan x).
    Proof.
      induction idents; intros.
      - invs H.
      - invs H.
        + unfold_wf_aexp; [ | intros .. ].
          * split; [ | split; [ | split ] ]; intros.
            -- assumption.
            -- apply second_wf_proof. assumption.
            -- apply in_list_means_exists_index. assumption.
            -- eapply free_vars_in_imp_has_variable. ereflexivity. unfold construct_trans in H2. rewrite H2 in H1. rewrite fold_left_is_reverse in H1. apply in_preserved_by_reverse in H1.
               assumption.
          * simpl in H1. rewrite H1 in H2. invs H2; [ | invs H3].
            assumption.
          * eapply free_vars_in_aexp_has_variable. ereflexivity. rewrite H1 in H2. assumption.
          * simpl in H1.  rewrite H1 in H2. invs H2; [ | invs H3].
            exists 0. econstructor. reflexivity.
          * invs H1.
        + invs H0. eapply var_map_wf_var_dan; eassumption.
    Defined.

    Ltac unfold_src_tar :=
      unfold SOURCE.idents, SOURCE.precond, SOURCE.program, SOURCE.postcond, SOURCE.fenv, SOURCE.hoare_triple, SOURCE.num_args, SOURCE.funcs, TARGET.precond, TARGET.postcond, TARGET.program, TARGET.compile_dan_log in *.

    Lemma fenv_well_formed_proof :
      fenv_well_formed' SOURCE.funcs SOURCE.fenv.
    Proof.
      unfold_src_tar.
      unfold fenv_well_formed'.
      split; intros.
      - constructor. unfold not. intros. invs H. constructor.
      - split; [ | split ].
        + unfold init_fenv in *. right. assumption.
        + unfold init_fenv in *. rewrite H. simpl. constructor. constructor.
        + unfold init_fenv in H. rewrite H. simpl. constructor. apply String.eqb_eq. reflexivity.
    Defined.

    Lemma funcs_okay_too_proof :
      funcs_okay_too SOURCE.funcs TARGET.fenv.
    Proof.
      unfold funcs_okay_too, SOURCE.funcs, TARGET.fenv.
      constructor.
      - constructor.
        + simpl. econstructor.
          * econstructor.
          * econstructor.
            all: unfold stack_mapping; simpl.
            reflexivity. econstructor. constructor. econstructor. econstructor. reflexivity. reflexivity.
        + simpl. econstructor; unfold stack_mapping; simpl.
          reflexivity. econstructor. reflexivity.
      - constructor.
    Defined.

    Lemma all_params_ok_for_funcs_proof :
      Forall (fun func => all_params_ok (DanTrickLanguage.Args func)
                                     (DanTrickLanguage.Body func)) SOURCE.funcs.
    Proof.
      unfold SOURCE.funcs. econstructor.
      - simpl. econstructor. constructor. econstructor.
      - constructor.
    Defined.

    Lemma fun_app_well_formed_proof :
      fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
    Proof.
      unfold_src_tar.
      constructor. constructor.
    Defined.

    Lemma aimp_always_wf_proof :
      aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.hoare_triple.
    Proof.
      unfold_src_tar.
      unfold_src_tar.
      unfold aimp_always_wf.
      assert (("z" <- CONST_Dan 0) = ("z" <- CONST_Dan 0)) by reflexivity.
      specialize (UIP_imp_refl _ H); intros.
      assert ((DanLogSubst.subst_AbsEnv "z" (CONST_Dan 0) SOURCE.postcond) = SOURCE.precond) by reflexivity.
      unfold_src_tar.
      specialize (DanLogPropDec.UIP_AbsEnv_refl _ H1); intros.
      eapply HLDanWFAssign with (Heq := H) (Hsubst := H1).
      - subst.
        simpl.
        econstructor.
      - constructor. constructor. constructor.
        eapply var_in_idents_implies_wf.
        econstructor. reflexivity. econstructor. unfold not. intros. invs H3.
        econstructor.
      - econstructor. unfold_wf_imp.
        + split; [ | split; [ | split ]]; intros.
          econstructor. unfold not; intros. invs H3. econstructor.
          eapply second_wf_proof. eassumption.
          apply in_list_means_exists_index. assumption.
          eapply free_vars_in_imp_has_variable.
          reflexivity.
          unfold construct_trans in H4. rewrite H4 in H3.
          rewrite fold_left_is_reverse in H3. apply in_preserved_by_reverse in H3. assumption.
        + econstructor. prove_var_map_wf_wrt_aexp_no_vars_in_aexp.
        + intros.
          invs H3.
          * eapply String.eqb_eq in H6.
            subst. econstructor. reflexivity.
          * invs H6.
      - constructor. constructor. constructor. constructor.
      - constructor. constructor. constructor. eapply var_in_idents_implies_wf.
        econstructor. reflexivity. econstructor. unfold not. intros. invs H3.
        econstructor.
      - constructor. constructor. constructor. constructor.
      - constructor.
      - constructor.
    Defined.
    
    Lemma translate_precond_proof :
      logic_transrelation SOURCE.num_args SOURCE.idents SOURCE.precond TARGET.precond.
    Proof.
      unfold_src_tar.
      simpl.
      constructor. constructor. constructor. constructor.
    Defined.
    Lemma translate_postcond_proof : logic_transrelation SOURCE.num_args SOURCE.idents SOURCE.postcond TARGET.postcond.
    Proof.
      unfold_src_tar.
      simpl.
      constructor. constructor. constructor. constructor.
    Defined.

    Lemma terminator_proof :
      terminator SOURCE.fenv SOURCE.num_args SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.hoare_triple.
    Proof.
      unfold_src_tar.
      unfold_src_tar.
      simpl. repeat constructor.
      all: unfold aexp_terminates_always; intros.
      - exists 0. constructor.
      - exists (nenv "z"). constructor. reflexivity.
    Defined.
    
    Lemma program_compiled_proof : TARGET.program = comp_code SOURCE.program SOURCE.idents SOURCE.num_args.
    Proof.
      unfold_src_tar.
      reflexivity.
    Defined.
    Lemma fun_env_compiled_proof : TARGET.fenv = compile_fenv SOURCE.fenv.
    Proof.
      reflexivity.
    Defined.
    Lemma precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
    Proof.
      unfold_src_tar.
      constructor. constructor. constructor.
      simpl. prove_var_map_wf_wrt_aexp_no_vars_in_aexp.
    Defined.
    Lemma postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
    Proof.
      unfold_src_tar.
      constructor. constructor. constructor.
      apply var_map_wf_var_dan.
      constructor. reflexivity. constructor. unfold not; intros. invs H.
      constructor.
    Defined.

    Ltac splits :=
      match goal with
      | [ |- _ /\ _ ] =>
          split; splits
      | _ =>
          intros
      end.
    Lemma imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
    Proof.
      unfold_src_tar.
      constructor.
      unfold_wf_imp.
      - splits.
        + constructor. unfold not; intros. invs H.
          constructor.
        + apply second_wf_proof. assumption.
        + apply in_list_means_exists_index. assumption.
        + apply free_vars_in_imp_has_variable with (idents := ("z" :: nil)).
          unfold construct_trans in H0.
          rewrite fold_left_is_reverse in H0.
          assert (rev ("z" :: nil) = rev (rev (free_vars_imp_src imp))) by (f_equal; assumption).
          rewrite rev_involutive in H1. rewrite <- H1. reflexivity.
          assumption.
      - econstructor. prove_var_map_wf_wrt_aexp_no_vars_in_aexp.
      - intros. invs H. apply String.eqb_eq in H2. subst.
        econstructor. reflexivity.
        invs H2.
    Defined.
  End CompileAssign.

  Module AssignCompiled := CompileProof CompileAssign DefaultCompiler.

  Module AssignSmallCompiled := CompileProof CompileAssign SmallerCompiler.



  Eval compute in "The second smallest tiny proof.".
  Time Eval compute in AssignSmallCompiled.compiled.
  Eval compute in "Eval4".


        
  
End LessSimpleExample.
