From Coq Require Import Psatz Arith List Program.Equality String.
From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick Require Import TranslationPure Imp_LangTrickLanguage.
From Imp_LangTrick Require Import ProofCompiler FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy.
From Imp_LangTrick Require Import TerminatesForSure CompilerCorrectHelpers UnprovenCorrectProofCompiler BuggyProofCompiler ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
Import Tests.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope imp_langtrick_scope.

Section input_program.
  Let p0 := PARAM_Imp_Lang 0.
  Let p1 := PARAM_Imp_Lang 1.
  Let y := VAR_Imp_Lang "y".

  Eval compute in (lt_Imp_Lang p0 p1).
  
  Definition min_program : imp_Imp_Lang :=
    SEQ_Imp_Lang (ASSIGN_Imp_Lang "y" p0)
            (IF_Imp_Lang ((p0 <=d p1) &d (!d (y <=d p1) &d (p1 <=d p0)))
                    (ASSIGN_Imp_Lang "z" p0)
                    (ASSIGN_Imp_Lang "z" p1)).
  
  Definition min_function : fun_Imp_Lang :=
    {| Name := "min"
    ; Args := 2
    ; Ret := "z"
    ; Body := min_program |}.

  Definition min_fenv :=
    update "min" min_function init_fenv.

  Definition min_pre :=
    AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)).

  Definition min_post :=
    Source.true_bool (((VAR_Imp_Lang "z") <=d p0) &d ((VAR_Imp_Lang "z") <=d p1)).

  Definition min_program_stk : imp_stack :=
    UnprovenCorrectCodeCompiler.compile_imp min_program ("z" :: nil) 2.

  Definition min_fun_idents := "z" :: nil.

  Definition min_fun_args := 2.

  

  Eval compute in min_program_stk.

  Let n2 := (Var_Stk 2).
  Let n3 := (Var_Stk 3).
  Let n1 := (Var_Stk 1).
  Let c1 := (Const_Stk 1).

  Eval compute in (compile_function min_function).

  Definition min_program_stk_incorrect : imp_stack :=
    StackLanguage.Body (compile_function min_function).

  Eval compute in min_program_stk_incorrect.
    (* If_Stk ((n2 <=s n3) &s (!s (n2 <=s n3) &s (n3 <=s n2))) *)
           (* (Assign_Stk 1 (Plus_Stk n2 c1)) (Assign_Stk 1 (Plus_Stk n3 c1)). *)

  Definition create_stk_min_function (ibody: imp_stack) :=
    {| StackLanguage.Name := "min"
    ; StackLanguage.Args := 2
    ; StackLanguage.Body := ibody
    ; Return_expr := n1
    ; Return_pop := 1 |}.
  Definition stk_min_function_incorrect :=
    create_stk_min_function min_program_stk_incorrect.

  Definition min_program_stk_incorrect_optimized : imp_stack :=
    BuggyProofCompilable.CC.compile_imp min_program min_fun_idents min_fun_args.
    (* If_Stk (!s (n3 <=s n2)) *)
           (* (Assign_Stk 1 (Plus_Stk n2 c1)) (Assign_Stk 1 (Plus_Stk n3 c1)). *)

  (* Eval compute in min_program_stk_incorrect_optimized. *)
  
  Definition stk_min_function_incorrect_optimized :=
    create_stk_min_function (prepend_push min_program_stk_incorrect_optimized 2).

  (* Eval compute in stk_min_function_incorrect_optimized. *)

  Let min_app :=
    (APP_Imp_Lang "min" ((VAR_Imp_Lang "y") :: (VAR_Imp_Lang "z") :: nil)).

  Let get_min : imp_Imp_Lang :=
    ASSIGN_Imp_Lang "x" min_app.

  Let x := (VAR_Imp_Lang "x").
  (* Let y := (VAR_Imp_Lang "y"). *)
  Let z := (VAR_Imp_Lang "z").

  (* Definition imp_fact_env := (min_pre, min_post) :: nil. *)
  
  Definition get_min_post :=
    (AbsEnvAnd (Source.true_bool (LEQ_Imp_Lang x y))
               (Source.true_bool (LEQ_Imp_Lang x z))).

  Definition min_fact_env :=
    ((Source.imp_lang_log_true), Imp_LangLogSubst.subst_AbsEnv "x" min_app get_min_post) :: nil. 


  Lemma zeroth_implication_index :  
    nth_error min_fact_env 0 =
      Some (Source.imp_lang_log_true,
             Imp_LangLogSubst.subst_AbsEnv "x"
                                      min_app get_min_post).
  Proof using min_app.
    unfold min_fact_env. simpl. unfold min_post. unfold Source.true_bool. unfold p0. reflexivity.
  Qed.     

  (* Definition get_min_post : AbsEnv := *)
  (*     AbsEnvLP (Imp_Lang_lp_bool ( *)

  Lemma min_terminates' :
    forall (dbenv: list nat) (nenv: store nat),
      all_params_ok (Datatypes.length dbenv) min_program ->
      exists nenv',
        i_Imp_Lang min_program dbenv min_fenv nenv nenv'.
  Proof.
    intros.
    (* unfold min_program. unfold min_fenv. unfold p0. unfold p1. unfold y. *)
    eapply imp_has_no_functions_always_terminates.
    - repeat econstructor.
    - assumption.
  Defined.

  Lemma min_terminates :
    forall (dbenv: list nat) (nenv: store nat),
      all_params_ok (Datatypes.length dbenv) min_program ->
      exists nenv',
        i_Imp_Lang min_program dbenv min_fenv nenv nenv'.
  Proof.
    intros.
    (* unfold min_program. unfold min_fenv. unfold p0. unfold p1. unfold y. *)
    prove_imp_terminates.
  Defined.

  (* Print min_terminates'. *)

  (* Print min_terminates. *)


  

  Lemma min_leq_first_arg_always_terminates :
    forall (dbenv: list nat) (nenv: store nat),
    exists v,
      b_Imp_Lang (min_app <=d y) dbenv min_fenv nenv v.
  Proof using min_app y.
    intros.
    eapply bexp_has_no_functions_always_terminates.
    - econstructor.
      + unfold min_app. prove_aexp_terminates.
        intros.
        pose proof (min_terminates (nenv0 "y" :: nenv0 "z" :: nil) init_nenv).
        assert (all_params_ok (Datatypes.length (nenv0 "y" :: nenv0 "z" :: nil)) min_program).
        repeat econstructor. specialize (H H0).
        destruct H.
        exists (x0 "z"). econstructor.
        reflexivity.
        reflexivity.
        econstructor. econstructor. reflexivity. econstructor. econstructor. reflexivity. econstructor.
        eassumption. simpl. reflexivity.
      + prove_aexp_terminates.
    - repeat econstructor.
  Qed.

  
      
    
  Ltac invsas H :=
    inversion H as [];
    subst.
  Ltac invcas H :=
    inversion_clear H as [];
    subst.

  Ltac imp_lang_semantics_inversion Himp_lang :=
    idtac Himp_lang;
    let Himp_lang_type := type of Himp_lang in
    match Himp_lang_type with
    | i_Imp_Lang (ASSIGN_Imp_Lang _ ?a) ?dbenv ?fenv ?nenv _ =>
        invc Himp_lang;
        match goal with
        | [ H': a_Imp_Lang a dbenv fenv nenv _ |- _ ] =>
            try imp_lang_semantics_inversion H'
        end
    | b_Imp_Lang (?b1 &d ?b2) ?dbenv ?fenv ?nenv ?val =>
        (* idtac "and1"; *)
        invs Himp_lang;
        (* idtac "and2"; *)
        try match goal with
        | [ H': andb ?b1' ?b2' = val |- _ ] =>
            rewrite H' in *
        end;
        match goal with
        | [ H': b_Imp_Lang b1 dbenv fenv nenv _, H'': b_Imp_Lang b2 dbenv fenv nenv _ |- _ ] =>
            try imp_lang_semantics_inversion H';
            try imp_lang_semantics_inversion H''
        end
    | b_Imp_Lang (!d ?b) ?dbenv ?fenv ?nenv _ =>
        invs Himp_lang;
        match goal with
        | [ H': b_Imp_Lang b dbenv fenv nenv _ |- _ ] =>
            try imp_lang_semantics_inversion H'
        end
    | b_Imp_Lang (?a1 <=d ?a2) ?dbenv ?fenv ?nenv _ =>
        invs Himp_lang;
        match goal with
        | [ H' : a_Imp_Lang a1 dbenv fenv nenv _ , H'': a_Imp_Lang a2 dbenv fenv nenv _ |- _ ] =>
            try imp_lang_semantics_inversion H';
            try imp_lang_semantics_inversion H''
        end
    | a_Imp_Lang (PARAM_Imp_Lang ?n) ?dbenv _ _ ?res =>
        invc Himp_lang;
        match goal with
        | [ H': nth_error dbenv n = Some res |- _ ] =>
            symmetry in H'; invc H'
        end
    | a_Imp_Lang (VAR_Imp_Lang ?x) ?dbenv ?fenv ?nenv _ =>
        invc Himp_lang
    | args_Imp_Lang (?arg :: ?args) ?dbenv ?fenv ?nenv _ =>
        invc Himp_lang;
        match goal with
        | [ H': a_Imp_Lang arg dbenv fenv nenv _, H'': args_Imp_Lang args dbenv fenv nenv _ |- _ ] =>
            try imp_lang_semantics_inversion H';
            try imp_lang_semantics_inversion H''
        end
    | a_Imp_Lang ?x ?dbenv _ _ ?res =>
        invc Himp_lang;
        match goal with
        | [ H': nth_error dbenv ?n = Some ?res |- _ ] =>
            symmetry in H'; invc H'
        end
    end.

  Lemma min_always_less_than1 :
    forall dbenv nenv,
      b_Imp_Lang ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil <=d VAR_Imp_Lang "y") dbenv
            min_fenv nenv true.
  Proof using min_app.
    intros.
    pose proof (MIN := min_leq_first_arg_always_terminates).
    specialize (MIN dbenv nenv). destruct MIN as (v & BIMP_LANG).
    destruct v.
    - eassumption.
    - invc BIMP_LANG. rewrite H1.
      invc H6. invc H5.
      imp_lang_semantics_inversion H4.
      invc H9.
      simpl in H6. invc H6.
      imp_lang_semantics_inversion H2.
      invc H9.
      + imp_lang_semantics_inversion H10.
        invc H13.
        remember ((update "y" (nenv "y") init_nenv "y")) as updatey.
        unfold update in Hequpdatey. simpl in Hequpdatey. subst updatey. simpl in H1.
        imp_lang_semantics_inversion H11.
        unfold update in H1. simpl in H1. rewrite Nat.leb_refl in H1. invc H1.
      + imp_lang_semantics_inversion H10.
        invc H13.
        imp_lang_semantics_inversion H11.
        unfold update in H1. simpl in H1.
        rewrite H1 in H4.
        eapply Nat.leb_gt in H1. assert (nenv "y" <= nenv "z") by lia.
        eapply Nat.leb_le in H. rewrite H in H4. simpl in H4. unfold update in H4. simpl in H4. rewrite H in H4. simpl in H4. discriminate.
  Qed.

  Lemma min_leq_second_arg_always_terminates :
    forall (dbenv: list nat) (nenv: store nat),
    exists v,
      b_Imp_Lang (min_app <=d z) dbenv min_fenv nenv v.
  Proof using min_app z.
    intros. eapply bexp_has_no_functions_always_terminates.
    - econstructor. econstructor.
      + unfold min_fenv. econstructor. prove_aexp_terminates. econstructor. prove_aexp_terminates. econstructor.
      + intros.
        pose proof (min_terminates (nenv0 "y" :: nenv0 "z" :: nil) init_nenv).
        assert (all_params_ok (Datatypes.length (nenv0 "y" :: nenv0 "z" :: nil)) min_program).
        repeat econstructor. specialize (H H0).
        destruct H.
        exists (x0 "z"). econstructor.
        reflexivity.
        reflexivity.
        econstructor. econstructor. reflexivity. econstructor. econstructor. reflexivity. econstructor.
        eassumption. simpl. reflexivity.
      + econstructor.
    - repeat econstructor.
  Qed.

 
  
  Lemma min_always_less_than2 :
    forall dbenv nenv,
      b_Imp_Lang (min_app <=d VAR_Imp_Lang "z") dbenv min_fenv nenv true.
  Proof using min_app.
    intros.
    pose proof (MIN := min_leq_second_arg_always_terminates).
    specialize (MIN dbenv nenv). destruct MIN as (v & BIMP_LANG).
    destruct v; [ eassumption | .. ].
    invs BIMP_LANG. invs H5.  invs H6. invs H4. invs H2. invs H12. invs H14. invs H8. invs H7. invs H16.
    - rewrite H1. invs H16.
      + imp_lang_semantics_inversion H18.
        imp_lang_semantics_inversion H19.
        invc H24.
        repeat Imp_LangLogicHelpers.a_Imp_Lang_same. simpl in H1.
        unfold update in H1. simpl in H1.
        rewrite H1 in H10.
        imp_lang_semantics_inversion H9.
        simpl in H10. invc H10.
      + pose proof (DET := b_Imp_Lang_deterministic).
        specialize (DET _ _ _ _ _ _ H18 H20). invs DET.
    - invc H19. invc H17. simpl in H10. symmetry in H10. invc H10. unfold update in H1. simpl in H1. rewrite Nat.leb_refl in H1. invs H1.
  Qed.

      

  Lemma implication : 
    aimpImp_Lang Source.imp_lang_log_true
            (Imp_LangLogSubst.subst_AbsEnv
               "x"
               min_app get_min_post) min_fenv.
  Proof using min_app.
    unfold aimpImp_Lang. intros.
    simpl. econstructor; econstructor; econstructor; econstructor.
    - eapply min_always_less_than1.
    - reflexivity.
    - eapply min_always_less_than2.
    - reflexivity.
  Qed.

  Definition min_assign_triple :=
    hl_Imp_Lang_consequence_pre (Imp_LangLogSubst.subst_AbsEnv "x" min_app get_min_post)
                           get_min_post
                           min_pre
                           get_min
                           0
                           min_fact_env
                           min_fenv
                           (hl_Imp_Lang_assign 
                              get_min_post min_fact_env min_fenv "x" min_app)
                           zeroth_implication_index
                           implication.
  Definition min_funcs := min_function :: (init_fenv "id") :: nil.
  Definition min_assign := get_min.
  
End input_program.


Module SourceAssignMin <: SourceProgramType.
  Definition program := min_assign.
  Definition precond := min_pre.
  Definition postcond := get_min_post.
  Definition fenv := min_fenv.
  Definition facts := min_fact_env.
  Definition hoare_triple := min_assign_triple.
  Definition idents := construct_trans min_assign.
  Definition num_args := 0.
  Definition funcs := min_funcs.
End SourceAssignMin.

(* TODO: Move to ProofCompCodeCompAgnosticMod *)
Module Type HasCompileFenv.
  Parameter compile_fenv: fun_env -> fun_env_stk.
End HasCompileFenv.

Print ProofCompilableCodeCompiler.CheckableSpecificationCompilerType.

Module CAPCTargetProgram (SP: SourceProgramType) (PC: ProofCompilableCodeCompiler.ProofCompilableType) (CCF: HasCompileFenv).
  Module TPI <: TargetProgramInputs.
    Definition target_fenv := CCF.compile_fenv SP.fenv.
    Definition target_facts (idents: list Base.ident) (num_args: nat): StackLogic.implication_env_stk :=
      map (fun (pr: AbsEnv * AbsEnv) =>
             let (P, P') := pr in
             (PC.SC.comp_logic num_args idents P,
               PC.SC.comp_logic num_args idents P')) SP.facts.
  End TPI.
  Module TP := CompilerAgnosticProofCompilableTargetProgram (SP) (PC.CC) (PC.SC) (TPI).
  Include TP.
End CAPCTargetProgram.
(* END TODO move *)


Module TargetAssignMinCorrect := CAPCTargetProgram(SourceAssignMin) (UnprovenCorrectProofCompilable) (EnvToStack).

Module TargetAsssignMinIncorrectOptimized <: TargetProgramType.
  Module SP := SourceAssignMin.
  Definition program := TargetAssignMinCorrect.program.
  Definition precond := TargetAssignMinCorrect.precond.
  Definition postcond := TargetAssignMinCorrect.postcond.
  Definition compile_imp_lang_log := TargetAssignMinCorrect.compile_imp_lang_log.
  Definition fenv := update "min" stk_min_function_incorrect_optimized init_fenv_stk.
  Definition facts := TargetAssignMinCorrect.facts.
End TargetAsssignMinIncorrectOptimized.

Module TargetAssignMinIncorrect <: TargetProgramType.
  Module SP := SourceAssignMin.
  Definition program := TargetAssignMinCorrect.program.
  Definition precond := TargetAssignMinCorrect.precond.
  Definition postcond := TargetAssignMinCorrect.postcond.
  Definition compile_imp_lang_log := TargetAssignMinCorrect.compile_imp_lang_log.
  Definition fenv := update "min" stk_min_function_incorrect init_fenv_stk.
  Definition facts := TargetAssignMinCorrect.facts.
End TargetAssignMinIncorrect.



Module CompileMinCorrect <: ProgramProofCompilationType.
  Module CAPC := UnprovenCorrectProofCompiler.
  Module SOURCE := SourceAssignMin.
  Module TARGET := TargetAssignMinCorrect.

  Ltac unfold_src_tar :=
      unfold SOURCE.idents, SOURCE.precond, SOURCE.program, SOURCE.postcond, SOURCE.fenv, SOURCE.hoare_triple, SOURCE.num_args, SOURCE.funcs, TARGET.precond, TARGET.postcond, TARGET.program, TARGET.compile_imp_lang_log, TARGET.fenv, SOURCE.facts, TARGET.facts in *.

  Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. repeat econstructor.
    simpl.
    destruct_stks stk. simpl. lia.
  Defined.
    
  Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar.
    cbv delta [get_min_post min_fenv EnvToStack.compile_fenv min_assign construct_trans]. simpl. cbv delta [Source.true_bool]. simpl.
    repeat econstructor; try solve [destruct_stks stk; simpl; lia | destruct_stks stk; simpl; reflexivity].
    - AbsEnv_rel_inversion.
      repeat Imp_LangLogicHelpers.a_Imp_Lang_same.
      rewrite H3 in *. rewrite H4 in *.
      repeat Imp_LangLogicHelpers.a_Imp_Lang_same.
      invs H11. invs H10. eassumption.
    - AbsEnv_rel_inversion. rewrite H4 in *. rewrite H3 in *. repeat Imp_LangLogicHelpers.a_Imp_Lang_same. invs H11. invs H12. eassumption.
    - invs H0. simpl in *. absstate_match_inversion. simpl in *. invc H19. invc H23. invc H22. rewrite <- H15. reflexivity.
    - invs H0. simpl in *. absstate_match_inversion. simpl in *. invc H19. invc H18. rewrite <- H17. reflexivity.
  Defined.
  
  Lemma fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
  Proof.
    unfold fact_env_valid. unfold_src_tar.
    unfold SOURCE.facts. unfold min_fact_env. simpl. intros.
    destruct H as [H | H]; [ | invs H].
    invc H. unfold Source.imp_lang_log_true.
    eapply implication.
  Defined.
  
  Lemma fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
  Proof.
    unfold fenv_well_formed'. unfold_src_tar. unfold min_funcs, min_fenv.
    repeat split.
    - finite_nodup.
    - unfold update in H. destruct (string_dec "min" f).
      + subst. left. finite_in.
      + subst. right. unfold init_fenv. reflexivity.
    - unfold update. subst. unfold update. destruct (string_dec "min" f);
      FunctionWellFormedReflection.prove_fun_app_wf.
    - unfold update in H. destruct (string_dec "min" f); simpl; subst; ImpHasVariableReflection.prove_imp_has_variable.
    - simpl. finite_nodup.
    - intros. simpl in H. destruct H as [H | H].
      + rewrite <- H in *.
        unfold update in H0. destruct (string_dec "min" f).
        * rewrite <- e. simpl. reflexivity.
        * unfold init_fenv in H0. invs H0.
      + destruct H as [H | H]; [ | invs H].
        simpl in IN_FUNC_NAMES. destruct IN_FUNC_NAMES as [A | [B | C ]]; [ | | invs C ].
        * rewrite <- A in *. unfold update in H0. simpl in H0. rewrite <- H in H0. invs H0.
        * rewrite <- B in *. rewrite <- H in H0. rewrite <- H. simpl. reflexivity.
    - finite_in.
    - intros. unfold not in H.
      pose proof (IN_DEC := in_dec).
      specialize (IN_DEC _ string_dec f (map Name (min_function :: init_fenv "id" :: nil))). destruct IN_DEC. eapply H in i. invs i.
      simpl in n.
      pose proof (string_dec "min" f).
      pose proof (string_dec "id" f).
      destruct H0 as [A1 | A2]; destruct H1 as [B1 | B2].
      + rewrite <- B1 in A1. invs A1.
      + assert ("min" = f \/ "id" = f \/ False).
        left. assumption. eapply n in H0. invs H0.
      + assert ("min" = f \/ "id" = f \/ False).
        right. left. assumption.
        eapply n in H0. invs H0.
      + unfold update. destruct (string_dec "min" f).
        * eapply A2 in e. invs e.
        * unfold init_fenv. reflexivity.
    - intros. invs H0.
      + exists "min". repeat split.
        * finite_in.
        * rewrite <- H1. unfold update. reflexivity.
        * rewrite <- H1. reflexivity.
      + invs H1.
        * rewrite <- H. exists "id". repeat split.
          finite_in.
        * invs H.
  Defined.
  Lemma funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
  Proof.
    unfold funcs_okay_too; repeat split; unfold_src_tar; unfold SourceAssignMin.facts; unfold SourceAssignMin.fenv.
    - econstructor.
      + repeat constructor.
        unfold min_fenv. unfold EnvToStack.compile_fenv. unfold EnvToStack.compile_function. simpl. unfold stack_mapping. unfold construct_trans. unfold min_program. simpl. econstructor. econstructor. simpl. econstructor. repeat econstructor.
        repeat econstructor.
      + simpl. repeat econstructor.
    - unfold min_funcs, min_fenv, EnvToStack.compile_fenv. unfold EnvToStack.compile_function. intros. simpl.
      invs H.
      + reflexivity.
      + invs H0.
        * reflexivity.
        * invs H1.
    - intros. unfold min_funcs. unfold EnvToStack.compile_fenv, min_fenv. simpl. unfold init_fenv_stk.
      pose proof (A := string_dec names "min").
      pose proof (B := string_dec names "id").
      destruct A as [A1 | A2]; destruct B as [B1 | B2].
      + rewrite A1 in B1. invs B1.
      + left. left. symmetry in A1. assumption.
      + left. right. left. symmetry. assumption.
      + right. unfold TARGET.TPI.target_fenv. unfold EnvToStack.compile_fenv. unfold EnvToStack.compile_function. simpl. unfold SourceAssignMin.fenv. unfold min_fenv. unfold update. destruct (string_dec "min" names); try congruence.
        reflexivity.
  Defined.
  Lemma all_params_ok_for_funcs_proof : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func)
                                                                                                                                                  (Imp_LangTrickLanguage.Body func))
                                               SOURCE.funcs.
  Proof.
    unfold SOURCE.funcs. unfold min_funcs. econstructor.
    - simpl. repeat econstructor.
    - econstructor.
      + simpl. repeat econstructor.
      + econstructor.
  Defined.
  
  Lemma fun_app_well_formed_proof : fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
  Proof.
    unfold_src_tar. econstructor. econstructor.
    - econstructor. econstructor. econstructor. econstructor. econstructor.
    - reflexivity.
    - unfold min_funcs. remember (min_fenv "min") as min. unfold min_fenv in Heqmin. unfold update in Heqmin. simpl in Heqmin. rewrite Heqmin. finite_in.
    - reflexivity.
    - simpl. eapply ImpHasVarSeq__right. eapply ImpHasVarIf__else. econstructor.
      reflexivity.
    - simpl. left. reflexivity.
  Defined.

  Lemma min_var_map_wf: var_map_wf ("x" :: "z" :: "y" :: nil).
  Proof.
    unfold var_map_wf; intuition; try (apply find_index_rel_and_one_index_opt; auto); try (clear; finite_nodup); 
    try (apply in_list_means_exists_index; auto);
    eapply free_vars_in_imp_has_variable; eauto;
    apply in_construct_trans_implies_in_free_vars.
    rewrite <- H0; auto.
  Qed. 

  Lemma min_no_dup: NoDup ("x" :: "z" :: "y" :: nil).
  Proof.
    finite_nodup.
  Qed.
  
  Lemma min_find_index_one_opt: forall x index,
    0 <= index < 3 ->
    find_index_rel ("x" :: "z" :: "y" :: nil) x (Some index) ->
    one_index_opt x ("x" :: "z" :: "y" :: nil) = S index.
  Proof.
    intros. apply find_index_rel_and_one_index_opt; auto.
    apply min_no_dup.
  Qed.

  Lemma min_one_opt_find_index: forall x index,
    0 <= index < 3 ->
    one_index_opt x ("x" :: "z" :: "y" :: nil) = S index ->
    find_index_rel ("x" :: "z" :: "y" :: nil) x (Some index).
  Proof.
    intros. apply find_index_rel_and_one_index_opt; auto.
    apply min_no_dup.
  Qed.

  Lemma min_in_exists_index: forall x,
    In x ("x" :: "z" :: "y" :: nil) ->
    exists index : nat,
      one_index_opt x ("x" :: "z" :: "y" :: nil) =
      S index.
  Proof.
    intros. apply in_list_means_exists_index; auto.
  Qed.

  Lemma min_construct_trans_has_var : forall x imp, 
    In x ("x" :: "z" :: "y" :: nil) ->
    "x" :: "z" :: "y" :: nil = construct_trans imp ->
    imp_has_variable x imp.
  Proof.
    intros. eapply free_vars_in_imp_has_variable; eauto.
    apply in_construct_trans_implies_in_free_vars.
    rewrite <- H0. auto.
  Qed.
  
  Lemma min_in_rev_cons:
    forall y,
      In y ("y" :: "z" :: nil) ->
      In y ("x" :: "z" :: "y" :: nil).
  Proof.
   intros. apply in_cons. apply in_rev. auto.
  Qed.

  Local Hint Resolve min_var_map_wf min_no_dup min_find_index_one_opt 
    min_one_opt_find_index min_in_exists_index min_construct_trans_has_var
    min_in_rev_cons.

  Lemma min_var_wf_bexp: forall id,
    (id = "y" \/ id = "z") ->
    var_map_wf_wrt_bexp
      ("x" :: "z" :: "y" :: nil)
      ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil <=d VAR_Imp_Lang id) /\
    var_map_wf_wrt_bexp
      ("x" :: "z" :: "y" :: nil)
      (VAR_Imp_Lang "x" <=d VAR_Imp_Lang id).
  Proof.
   intros.
   pose proof (var_map_wf_wrt_bexp_self ("y" :: "z" :: nil) ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil <=d VAR_Imp_Lang id)).
   pose proof (var_map_wf_wrt_bexp_self ("x" :: "y" :: nil) (VAR_Imp_Lang "x" <=d VAR_Imp_Lang id)).
   unfold var_map_wf_wrt_bexp in *. repeat split; intros; auto.
   - apply min_in_rev_cons. rewrite H2 in H3. subst. destruct H; subst; assumption.
   - eapply free_vars_in_bexp_has_variable; eauto.
   - eapply find_index_rel_in_stronger; eauto. destruct H; subst; auto.
   - destruct H; subst; destruct H3; subst; intuition.
   - eapply free_vars_in_bexp_has_variable; eauto.
   - eapply find_index_rel_in_stronger; eauto. destruct H; subst; destruct H3; subst; intuition.
  Qed.

  Lemma min_var_forall:
    imp_forall_relation_on_aexps_bexps
      (var_map_wf_wrt_aexp ("x" :: "z" :: "y" :: nil))
      (var_map_wf_wrt_bexp ("x" :: "z" :: "y" :: nil))
      ("x" <- ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil)).
  Proof.
    constructor. unfold var_map_wf_wrt_aexp. repeat split; intros; auto.
    - simpl in H. subst. auto.
    - eapply free_vars_in_aexp_has_variable; eauto.
    - eapply find_index_rel_in; eauto; intros. subst. auto.
    - rewrite H in H0. eapply free_vars_in_args_has_variable; eauto.
  Qed.

  Lemma min_var_map_wf_wrt_imp:
    var_map_wf_wrt_imp
      ("x" :: "z" :: "y" :: nil)
      ("x" <- ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil)).
  Proof.
    econstructor; unfold var_map_wf_wrt_imp; repeat split; intros; auto.
    - apply min_var_forall.
    - apply in_rev. unfold rev. unfold app. eapply free_vars_in_imp_has_variable; eauto. simpl. auto.
  Qed.

  Lemma min_fun_app_wf:
   fun_app_well_formed
     (update "min" min_function init_fenv)
     (min_function :: init_fenv "id" :: nil)
     ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil).
  Proof.
    econstructor; eauto.
    - repeat constructor.
    - constructor. reflexivity.
    - unfold update. simpl. unfold min_program. eapply free_vars_in_imp_has_variable; eauto.
      simpl. right. left. auto.
  Qed.

  (* These proofs are easy but repetitive; reflective tactics will go very far in reducing user proof burden post-deadline! *)
  Lemma aimp_always_wf_proof : aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
  Proof.
    unfold_src_tar. unfold SOURCE.facts. unfold min_funcs. unfold min_pre. unfold get_min_post, min_assign, min_fenv, min_fact_env, min_assign_triple, construct_trans. simpl. unfold aimp_always_wf.
    eapply HLImp_LangWFConsequencePre.
    - shelve.
    - reflexivity.
    - prove_imp_rec_rel min_var_map_wf_wrt_imp.
    - simpl. 
      constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
    - prove_AbsEnv_prop_wf. 
    - constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
    - eapply HLImp_LangWFAssign with (Heq := eq_refl) (Hsubst := eq_refl); eauto.
      + constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
      + prove_imp_rec_rel min_var_map_wf_wrt_imp.
      + repeat constructor.
      + constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
      + repeat constructor.
      + repeat constructor.
      + apply min_fun_app_wf.
    - constructor; constructor; constructor; constructor; simpl; constructor; 
      try constructor; apply min_fun_app_wf.
    - repeat constructor.
    - repeat constructor.
    -  constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
    - repeat constructor.
    - constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
  Unshelve. constructor; constructor.
      + destruct (andb (Nat.leb (nenv "y")  (nenv "z"))
        ((negb (andb (Nat.leb (nenv "y") (nenv "z")) 
            (Nat.leb (nenv "z") (nenv "y")))))) eqn:?.
        * repeat econstructor. rewrite <- Heqb; econstructor; rewrite Heqb; repeat econstructor. simpl.
          unfold update. simpl. eapply Nat.leb_refl.
        * econstructor. simpl. econstructor. eapply min_always_less_than1. reflexivity.
      + destruct (andb (Nat.leb (nenv "y")  (nenv "z"))
      ((negb (andb (Nat.leb (nenv "y") (nenv "z")) 
          (Nat.leb (nenv "z") (nenv "y")))))) eqn:?.
        * repeat econstructor. rewrite <- Heqb; econstructor; rewrite Heqb; repeat econstructor. simpl. unfold update. simpl. eapply Bool.andb_true_iff in Heqb. destruct Heqb. assumption. 
        * econstructor. econstructor. simpl. eapply min_always_less_than2. reflexivity.
  Qed. 

  Lemma translate_precond_proof : UnprovenCorrectProofCompiler.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.precond = TARGET.precond.
  Proof.
    reflexivity.
  Qed.

  Lemma translate_postcond_proof : UnprovenCorrectProofCompiler.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.postcond = TARGET.postcond.
  Proof.
    reflexivity.
  Qed.

  Lemma check_proof_proof :
    UnprovenCorrectProofCompiler.PC.check_proof SOURCE.fenv SOURCE.funcs SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.facts SOURCE.idents SOURCE.num_args SOURCE.hoare_triple.
  Proof.
    unfold_src_tar. unfold min_assign_triple.
    eapply UnprovenCorrectProofCompilable.CheckHLPre.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - assert (Heq : (Imp_LangLogSubst.subst_AbsEnv "x"
          ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil)
          get_min_post) = (Imp_LangLogSubst.subst_AbsEnv "x"
          ("min" @d VAR_Imp_Lang "y" :: VAR_Imp_Lang "z" :: nil)
          get_min_post)) by reflexivity.
      assert (Hi : min_assign = min_assign) by reflexivity.
      eapply UnprovenCorrectProofCompilable.CheckHLAssign with (Heq := Heq) (Hi := Hi).
      + rewrite (UIP_imp_refl _ Hi). rewrite (Imp_LangLogPropDec.UIP_AbsEnv_refl _ Heq). simpl. reflexivity.
      + reflexivity.
      + unfold UnprovenCorrectProofCompilable.CC.compile_aexp. simpl.
        StackExprWellFormed.prove_absstate_well_formed.
      + simpl. unfold construct_trans. simpl. unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp.  simpl.
        StackExprWellFormed.prove_absstate_well_formed.
      + simpl. unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp. simpl. prove_stack_large_enough_for_state.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + intros. unfold UnprovenCorrectProofCompilable.CC.compile_aexp.
        simpl.
        unfold funcs_okay_too in H3. destruct H3 as (FORALL & ?).
        simpl in FORALL. invs FORALL. destruct H6.
        prove_expr_stack_pure; try eassumption.
        
        eapply StackPurestBase.aexp_frame_implies_aexp_pure. eassumption.

      + intros. unfold UnprovenCorrectProofCompilable.SC.comp_logic. simpl. unfold UnprovenCorrectProofCompilable.CC.compile_bexp. simpl. unfold UnprovenCorrectProofCompilable.CC.compile_aexp. simpl.
        simpl in H2. rewrite H2. rewrite <- H. simpl. reflexivity.
  Qed.

  Lemma check_logic_precond_proof :
    UnprovenCorrectProofCompiler.SC.check_logic SOURCE.precond = true.
  Proof.
    reflexivity.
  Qed.

  Lemma check_logic_postcond_proof :
    UnprovenCorrectProofCompiler.SC.check_logic SOURCE.postcond = true.
  Proof.
    reflexivity.
  Qed.

  Lemma program_compiled_proof : TARGET.program = comp_code SOURCE.program SOURCE.idents SOURCE.num_args.
  Proof.
    reflexivity.
  Qed.

  Lemma check_imp_proof :
    UnprovenCorrectProofCompiler.CC.check_imp SOURCE.program = true.
  Proof.
    reflexivity.
  Qed.

  (* Lemma fun_env_compiled_proof : TARGET.fenv = compile_fenv SOURCE.fenv. *)
  Lemma precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
  Proof.
    repeat econstructor.
  Qed.   

  Lemma postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
  Proof.
    constructor; constructor; constructor; constructor; eapply min_var_wf_bexp; eauto.
  Qed.
  Lemma imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
  Proof.
    constructor. unfold var_map_wf_wrt_imp; repeat split; intros; auto.
    - apply min_var_forall.
    - apply in_rev. unfold rev. unfold app. eapply free_vars_in_imp_has_variable; eauto. simpl. auto.
  Qed.

  Lemma bexp_replace_result_value :
    forall b dbenv fenv nenv bval boolexpr,
    forall (EQ : boolexpr = bval),
      b_Imp_Lang b dbenv fenv nenv bval <-> b_Imp_Lang b dbenv fenv nenv boolexpr.
  Proof.
    intros. split; intros.
    - rewrite EQ. assumption.
    - rewrite <- EQ. assumption.
  Qed.
      
  
  Lemma implication_transformer :
    UnprovenCorrectProofCompiler.PC.valid_imp_trans_def SOURCE.facts TARGET.facts SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold UnprovenCorrectProofCompiler.PC.valid_imp_trans_def; repeat split; intros; unfold_src_tar.
    - simpl. lia.
    - destruct n.
      + simpl in *. invs H3. simpl.  reflexivity.
      + unfold_src_tar.
        simpl. simpl in H3. rewrite nth_error_nil_none in H3. invs H3.
    - unfold StackLogic.fact_env_valid. cbv delta [TARGET.TPI.target_fenv TARGET.TPI.target_facts]. unfold UnprovenCorrectProofCompilable.SC.comp_logic.
      simpl.
      intros. destruct H; try contradiction.
      invc H.
      unfold EnvToStack.compile_fenv. unfold SourceAssignMin.fenv. unfold min_fenv. unfold EnvToStack.compile_function. unfold EnvToStack.pre_compile_function. simpl. unfold SourceAssignMin.num_args, SourceAssignMin.idents.
      unfold construct_trans, min_assign. simpl.
      unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp.
      unfold EnvToStack.compile_bexp. simpl.
      unfold StackLogic.aimpstk. intros.
      invc H. invc H5. invc H0. invc H1. invc H2.
      do 3 match goal with
             | [ H: context G [Datatypes.length ?stk] |- _ ] =>
                 destruct stk; simpl in H; try lia
           end.
      clear H0.
      pose proof (Hn1n0 := le_gt_dec n1 n0).
      pose proof (Hn0n1 := le_gt_dec n0 n1).
      destruct Hn1n0, Hn0n1; meta_smash; try lia; try smash_stack_mutated_at_index;
        try match goal with
            | [ |- prop_rel _ _ ] =>
                repeat econstructor
            end.

      all: try match goal with
               | [ H: ?n1 <= ?n0, H': ?n0 <= ?n1 |- imp_stack_sem _ _ (_ :: ?n1 :: _ :: ?n0 :: _ ) _ ] =>
                   eapply Stack_if_false; meta_smash; smash_stack_mutated_at_index; eapply Nat.leb_le in H, H'; rewrite H, H'; reflexivity
               | [ H: ?n1 <= ?n0, H': ?n0 > ?n1 |- imp_stack_sem _ _ (_ :: ?n1 :: _ :: ?n0 :: _ ) _ ] =>
                   eapply Stack_if_true; meta_smash; smash_stack_mutated_at_index; eapply Nat.leb_le in H; eapply Nat.leb_gt in H'; rewrite H, H'; reflexivity
               | [ H: ?n1 > ?n0, H': ?n0 <= ?n1 |- imp_stack_sem _ _ (_ :: ?n1 :: _ :: ?n0 :: _ ) _ ] =>
                   eapply Stack_if_false; meta_smash; smash_stack_mutated_at_index; eapply Nat.leb_le in H'; eapply Nat.leb_gt in H; rewrite H, H'; reflexivity
               end.
      all: simpl; try lia; try reflexivity; try eapply Nat.leb_refl; try eapply Nat.leb_le; eauto.
      all: repeat econstructor.
      Unshelve.
      all: eauto; try eapply stk_min_function_incorrect; try eapply (Var_Stk 1).
   Qed. 
End CompileMinCorrect.
