From Coq Require Import Psatz Arith List Program.Equality String.
From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick Require Import TranslationPure Imp_LangTrickLanguage.
From Imp_LangTrick Require Import ProofCompiler FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompMod ProofCompAuto ProofCompilableCodeCompiler.
From Imp_LangTrick Require Import TerminatesForSure Imp_LangDec.
From Imp_LangTrick Require Import EnvToStackIncomplete.
Import Tests.
From Imp_LangTrick Require Import StackLogic IncompleteProofCompiler.


Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope imp_langtrick_scope.


Section input_program.
  Let p0 := PARAM_Imp_Lang 0.
  Let r := VAR_Imp_Lang "r".
  Definition left_shift_program : imp_Imp_Lang :=
    (ASSIGN_Imp_Lang "r" (PLUS_Imp_Lang p0 p0)).

  Definition left_shift_function : fun_Imp_Lang :=
    {| Name := "left_shift"
    ; Args := 1
    ; Ret := "r"
    ; Body := left_shift_program |}.

  Definition left_shift_fenv :=
    update (Name left_shift_function) left_shift_function init_fenv.

  Definition left_shift_pre :=
    AbsEnvLP(Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)).

  Definition left_shift_post :=
    AbsEnvLP (Imp_Lang_lp_arith (BinaryProp nat aexp_Imp_Lang (fun ret n => ret = 2 * n) r p0)).

  Definition left_shift_function_idents :=
    construct_trans left_shift_program.

  Definition left_shift_program_stk : imp_stack :=
    Seq_Stk Push_Stk (comp_code left_shift_program left_shift_function_idents (Args left_shift_function)).

  Eval compute in left_shift_program_stk.

  

  Definition stk_min_function :=
    compile_function_incomplete left_shift_function.

  Print comp_code.
  
  (* Lemma incomplete_correct_on_shift : *)
  (*   comp_code left_shift_program left_shift_function_idents (Args left_shift_function) = compile_imp_incomplete left_shift_program (ident_list_to_map left_shift_function_idents) (Datatypes.length left_shift_function_idents). *)
  (* Proof. *)
  (*   simpl. unfold comp_code. simpl. reflexivity. *)
  (* Qed. *)
                                   

  Let x := VAR_Imp_Lang "x".
  Let y := VAR_Imp_Lang "y".
                   

  Let left_shift_app :=
        (APP_Imp_Lang (Name left_shift_function) (y :: nil)).

  Let assign_left_shift :=
        ASSIGN_Imp_Lang "x" left_shift_app.

  Let assign_left_shift_idents :=
        construct_trans assign_left_shift.
  
  Definition assign_left_shift_post :=
    AbsEnvLP (Imp_Lang_lp_arith (BinaryProp nat aexp_Imp_Lang (fun ret n => ret = 2 * n) x y)). 

  Definition left_shift_fact_env :=
    ((Source.imp_lang_log_true), Imp_LangLogSubst.subst_AbsEnv "x" left_shift_app assign_left_shift_post) :: nil.

  Lemma first_implication_exists :
    nth_error left_shift_fact_env 0 =
      Some ((Source.imp_lang_log_true), Imp_LangLogSubst.subst_AbsEnv "x" left_shift_app assign_left_shift_post).
  Proof using left_shift_app.
    unfold left_shift_fact_env. simpl. unfold assign_left_shift_post. reflexivity.
  Qed.

  Lemma left_shift_is_always_n_plus_n :
    forall dbenv nenv n,
      n = nenv "y" ->
      a_Imp_Lang ("left_shift" @d y :: nil) dbenv left_shift_fenv nenv (n + n).
  Proof.
    intros. econstructor.
    - reflexivity.
    - reflexivity.
    - econstructor. econstructor. reflexivity. econstructor.
    - econstructor. econstructor.
      + econstructor. simpl. lia. simpl. reflexivity.
      + econstructor; simpl. lia. reflexivity.
    - simpl. unfold update. simpl. rewrite H. reflexivity.
  Qed.

  Lemma implication :
    aimpImp_Lang Source.imp_lang_log_true
            (Imp_LangLogSubst.subst_AbsEnv "x" left_shift_app assign_left_shift_post)
            left_shift_fenv.
  Proof using left_shift_app.
    unfold aimpImp_Lang. unfold left_shift_app. intros.
    simpl. econstructor; econstructor; econstructor.
    - 
      eapply left_shift_is_always_n_plus_n. reflexivity.
    - econstructor. reflexivity.
    - rewrite Nat.add_0_r. reflexivity.
  Qed.

  Definition assign_left_shift_triple :=
    hl_Imp_Lang_consequence_pre (Imp_LangLogSubst.subst_AbsEnv "x" left_shift_app assign_left_shift_post)
                           assign_left_shift_post
                           left_shift_pre
                           assign_left_shift
                           0
                           left_shift_fact_env
                           left_shift_fenv
                           (hl_Imp_Lang_assign
                              assign_left_shift_post
                              left_shift_fact_env
                              left_shift_fenv
                              "x"
                              left_shift_app)
                           first_implication_exists
                           implication.
  Definition left_shift_funcs := left_shift_function :: (init_fenv "id") :: nil.

  Definition left_shift_assign := assign_left_shift.

End input_program.
  
    
Module SourceAssignLeftShift <: SourceProgramType.
  Definition program := left_shift_assign.
  Definition precond := left_shift_pre.
  Definition postcond := assign_left_shift_post.
  Definition fenv := left_shift_fenv.
  Definition facts := left_shift_fact_env.
  Definition hoare_triple := assign_left_shift_triple.
  Definition idents := construct_trans program.
  Definition num_args := 0.
  Definition funcs := left_shift_funcs.
End SourceAssignLeftShift.


Print IncompleteProofCompiler.SC.comp_logic.  


(* Module TargetAssignLeftShift := TargetProgram(SourceAssignLeftShift). *)

Definition translate_AbsEnv_pair_incomplete lst args p :=
  match p with
  |(P, Q) => ((IncompleteProofCompiler.SC.comp_logic args lst P)
  , (IncompleteProofCompiler.SC.comp_logic args lst Q))
  end. 

Module TargetAssignLeftShift <: TargetProgramType.
  Module SP := SourceAssignLeftShift.

  Definition compile_imp_lang_log (d: AbsEnv): AbsState :=
    IncompleteProofCompiler.SC.comp_logic SP.num_args SP.idents d.
  
  Definition program: imp_stack := IncompleteCodeCompiler.compile_imp SP.program SP.idents SP.num_args.
  Definition precond: AbsState := IncompleteSpecCompiler.comp_logic SP.num_args SP.idents SP.precond.
  Definition postcond: AbsState := IncompleteSpecCompiler.comp_logic SP.num_args SP.idents SP.postcond.
  Definition fenv: fun_env_stk := compile_fenv_incomplete SP.fenv.
  Definition facts: implication_env_stk := map (translate_AbsEnv_pair_incomplete SP.idents SP.num_args) SP.facts.
End TargetAssignLeftShift.

(* Definition left_shift_function_facts := *)
(*   (left_shift_pre, Imp_LangLogSubst.subst_AbsEnv "r" (PLUS_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 0)) left_shift_post) :: nil. *)


(* Lemma left_shift_function_triple : *)
(*   forall fenv, *)
(*     hl_Imp_Lang left_shift_pre left_shift_program left_shift_post left_shift_function_facts fenv. *)
(* Proof. *)
(*   intros. *)
(*   unfold left_shift_pre, left_shift_program, left_shift_post. *)
(*   econstructor. *)

(*   Print left_shift_program. *)
(*   - econstructor. *)
(*   - simpl. unfold left_shift_function_facts. unfold Source.imp_lang_log_true. *)
(*     assert (nth_error left_shift_function_facts 0 = Some *)
(*     (AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)), *)
(*      AbsEnvLP *)
(*        (Imp_Lang_lp_arith *)
(*           (BinaryProp nat aexp_Imp_Lang (fun ret n : nat => ret = n + (n + 0)) *)
(*                       (PARAM_Imp_Lang 0 +d PARAM_Imp_Lang 0) (PARAM_Imp_Lang 0))))). *)
(*     unfold left_shift_pre. unfold left_shift_post. simpl. reflexivity. *)
(*     eapply H. *)
(*   - unfold aimpImp_Lang. intros. simpl. econstructor. econstructor.  *)

Require Import ProofCompCodeCompAgnosticMod.

Module CompileLeftShiftIncomplete <: ProgramProofCompilationType.
  Module CAPC := IncompleteProofCompiler.
  Module SOURCE := SourceAssignLeftShift.
  Module TARGET := TargetAssignLeftShift.

  Ltac unfold_src_tar := unfold SOURCE.idents, SOURCE.precond, SOURCE.program, SOURCE.postcond, SOURCE.fenv, SOURCE.hoare_triple, SOURCE.num_args, SOURCE.funcs, TARGET.precond, TARGET.postcond, TARGET.program, TARGET.compile_imp_lang_log, TARGET.fenv in *.

 

  Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. repeat econstructor. simpl. invs H0. simpl. lia.
  Defined.

  Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. unfold EnvToStack.compile_fenv. unfold left_shift_fenv. unfold assign_left_shift_post.
    unfold SourceAssignLeftShift.fenv. unfold construct_trans. unfold left_shift_assign. simpl. unfold EnvToStack.compile_function. simpl.
    repeat econstructor; simpl; invs H0; simpl.
    - lia.
    - lia.
    - AbsEnv_rel_inversion. invs H7. invs H6. f_equal. eassumption.
    - lia.
    - reflexivity.
    - absstate_match_inversion. simpl in H13. invs H13. simpl in H11. invs H11. eassumption.
  Defined.


  Lemma fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
  Proof.
    unfold Imp_LangLogHoare.fact_env_valid. unfold SOURCE.facts. unfold SOURCE.fenv.
    unfold left_shift_fact_env. intros. invs H.
    - invc H0.
      clear H. unfold aimpImp_Lang. intros. repeat econstructor.
      simpl. unfold update. rewrite Nat.add_0_r. reflexivity.
    - invs H0.
  Defined.
  
  Lemma fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
  Proof.
    unfold fenv_well_formed'. unfold_src_tar. unfold left_shift_funcs. repeat split.
    - finite_nodup.
    - unfold left_shift_fenv in *. simpl in H. unfold update in H.
      destruct (string_dec "left_shift" f).
      + subst func. left. finite_in.
      + unfold init_fenv in H. subst. left.  unfold init_fenv. finite_in.
    - unfold left_shift_fenv in H. unfold update in H.
      destruct (string_dec (Name left_shift_function) f).
      + subst func. repeat econstructor.
      + subst func. simpl. repeat econstructor.
    - unfold left_shift_fenv in H. unfold update in H. destruct (string_dec (Name left_shift_function) f); subst func; simpl; econstructor; eapply String.eqb_refl.
    - simpl. finite_nodup.
    - intros. simpl in H. simpl in IN_FUNC_NAMES. destruct H as [A | [B | C]]; [ | | invs C ].
      + unfold left_shift_fenv in H0. simpl in H0. unfold update in H0. destruct (string_dec "left_shift" f).
        * subst func. rewrite <- e. reflexivity.
        * subst func. simpl. destruct IN_FUNC_NAMES as [A | [B | C]]; [ eapply n in A; invs A | | invs C].
          invs H0.
      + unfold left_shift_fenv in H0. simpl in H0. unfold update in H0. destruct (string_dec "left_shift" f); subst func.
        * simpl. invs H0.
        * simpl. destruct IN_FUNC_NAMES as [A | [B | C]]; [eapply n in A; invs A | invs H0 | invs C ]. reflexivity.
    - finite_in.
    - intros. simpl in H.
      pose proof (LS := string_dec "left_shift" f).
      pose proof (ID := string_dec "id" f).
      destruct LS as [LS | LS]; destruct ID as [ID | ID].
      + rewrite <- ID in LS. invs LS.
      + assert ("left_shift" = f \/ "id" = f \/ False).
        {
          left. assumption.
        }
        eapply H in H0. invs H0.
      + assert ("left_shift" = f \/ "id" = f \/ False).
        {
          right. left. assumption.
        }
        eapply H in H0. invs H0.
      + unfold left_shift_fenv. simpl. unfold update. destruct (string_dec "left_shift" f).
        * eapply LS in e. invs e.
        * reflexivity.
    - intros. unfold left_shift_fenv in H. simpl in H. unfold update in H. destruct (string_dec "left_shift" f).
      + exists f. repeat split.
        * replace f with (Name left_shift_function). eapply in_map. rewrite H in H0. assumption.
        * subst. reflexivity.
      + exists "id". replace "id" with (Name (init_fenv "id")).
        * repeat split.
          -- eapply in_map. rewrite H in H0. simpl. simpl in H0. eassumption.
          -- simpl. unfold left_shift_fenv. simpl. unfold update. destruct (string_dec "left_shift" f); [ eapply n in e; invs e | ].
             simpl. reflexivity.
          -- simpl. rewrite H. reflexivity.
        * reflexivity.
  Defined.
      
  Lemma funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
  Proof.
    unfold SOURCE.funcs. unfold TARGET.fenv. unfold left_shift_funcs. unfold SourceAssignLeftShift.fenv.
    unfold funcs_okay_too. repeat split.
    - econstructor.
      + simpl. econstructor. econstructor. econstructor. econstructor.
        unfold stack_mapping. simpl. reflexivity.
        unfold stack_mapping. simpl. lia.
        econstructor. econstructor. lia. reflexivity. econstructor; lia.
        unfold stack_mapping. econstructor; simpl; lia.
      + econstructor; [ | econstructor ].
        econstructor; econstructor; econstructor; unfold stack_mapping; simpl; try lia. econstructor; lia.
    - intros.
      simpl in H. destruct H as [A | [B | C]]; [ | | invs C].
      + rewrite <- A. simpl. reflexivity.
      + rewrite <- B. simpl. reflexivity.
    - intros. remember ((map Name (left_shift_function :: init_fenv "id" :: nil))) as MAP. simpl in HeqMAP. subst MAP.
      pose proof (IN_DEC := in_dec string_dec names ("left_shift" :: "id" :: nil)).
      destruct IN_DEC as [IN | NOTIN].
      + left. assumption.
      + simpl in NOTIN.
        pose proof (LS := string_dec "left_shift" names).
        pose proof (ID := string_dec "id" names).
        destruct LS as [LS | LS]; destruct ID as [ID | ID].
        * rewrite <- ID in LS. invs LS.
        * assert ("left_shift" = names \/ "id" = names \/ False).
          {
            left. assumption.
          }
          eapply NOTIN in H. invs H.
        * assert ("left_shift" = names \/ "id" = names \/ False).
          {
            right. left. assumption.
          }
          eapply NOTIN in H. invs H.
        * unfold left_shift_fenv. simpl. unfold update. destruct (string_dec "left_shift" names).
          -- eapply LS in e. invs e.
          -- right. unfold compile_fenv_incomplete. destruct (string_dec "left_shift" names).
             ++ eapply n in e. invs e.
             ++ unfold init_fenv.   reflexivity.
  Defined.


  Lemma all_params_ok_for_funcs_proof : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func)
                                                                                                                                                  (Imp_LangTrickLanguage.Body func))
                                               SOURCE.funcs.
  Proof.
    unfold SOURCE.funcs.
    unfold left_shift_funcs. repeat econstructor.
  Defined.

   Lemma imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
  Proof.
    unfold_src_tar. unfold left_shift_assign. unfold construct_trans. simpl.
    econstructor. econstructor.
    - var_map_wf_finite.
    - split.
      + econstructor. econstructor; [ var_map_wf_finite | ].
        repeat split; intros.
        * simpl in H. subst. finite_in_implication.
        * simpl in H. rewrite H in H0. eapply free_vars_in_aexp_has_variable_forwards. reflexivity. eassumption.
        * simpl in H. subst. eapply in_implies_find_index_rel.
          finite_in_implication. finite_nodup.
        * inversion H.
          eapply free_vars_in_args_has_variable.
          eassumption. eassumption.
      + intros.
        invs H;
          try match goal with
          | [ H: (String.eqb _ _) = true |- _ ] =>
               eapply String.eqb_eq in H
              end.
        subst. finite_in.
        invs H2. invs H3. invs H4.
        eapply String.eqb_eq in H5. subst. finite_in.
        invs H4.
  Defined.

  Lemma precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
  Proof.
    repeat econstructor.
  Qed.   

  Lemma postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
  Proof.
    econstructor; econstructor; econstructor; unfold SOURCE.idents; unfold construct_trans; unfold SOURCE.program; simpl; eapply var_map_wf_var_imp_lang; try finite_in; try finite_nodup.
  Defined.

  Lemma prop_wf_assign_left_shift_post :
    AbsEnv_prop_wf
      (construct_trans (ASSIGN_Imp_Lang "x" ("left_shift" @d VAR_Imp_Lang "y" :: nil)))
      assign_left_shift_post.
  Proof.
    unfold assign_left_shift_post. unfold construct_trans. simpl. do 3 econstructor; (split; [ var_map_wf_finite | ]).
    all: repeat split; intros.
    + simpl in H. subst. finite_in_implication.
    + eapply free_vars_in_aexp_has_variable; eassumption.
    + eapply find_index_rel_in; try eassumption; intros.
      * simpl in H. subst. finite_in_implication.
      * finite_nodup.
    + invs H.
    + simpl in H. subst. finite_in_implication.
    + eapply free_vars_in_aexp_has_variable; eassumption.
    + eapply find_index_rel_in; try eassumption; intros.
      * simpl in H. subst. finite_in_implication.
      * finite_nodup.
    + invs H.
  Defined.

  Lemma var_map_wf_left_shift_app :
    var_map_wf_wrt_aexp ("x" :: "y" :: nil)
                        ("left_shift" @d VAR_Imp_Lang "y" :: nil).
  Proof.
    (econstructor; [ var_map_wf_finite | ]); repeat split; simpl; intros.
    + subst. invs H0. right. left. reflexivity. invs H.
    + subst. invs H0. econstructor. econstructor. econstructor. eapply String.eqb_refl. invs H.
    + subst. invs H0.
      * exists 1. econstructor. unfold not. intros.  invs H. econstructor. reflexivity.
      * invs H.
    +  subst. invs H1. invs H. invs H1. econstructor. econstructor. reflexivity. econstructor. econstructor. reflexivity. invs H0.
  Defined.

  Lemma fun_app_well_formed_proof :
    fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
  Proof.
    unfold_src_tar. unfold left_shift_assign. econstructor.
    econstructor.
    - econstructor. econstructor. econstructor.
    - reflexivity.
    - unfold left_shift_funcs. simpl. left. reflexivity.
    - simpl. reflexivity.
    - simpl. unfold left_shift_program. econstructor. simpl. reflexivity.
    - left. simpl. reflexivity.
  Defined.
  

  Lemma aimp_always_wf_proof : aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
  Proof.
    unfold_src_tar. unfold left_shift_assign. simpl. unfold SOURCE.facts. unfold assign_left_shift_triple.
    eapply HLImp_LangWFConsequencePre.
    - unfold aimpImp_Lang. intros.
      assert (AbsEnv_rel (Imp_LangLogSubst.subst_AbsEnv "x"
      (Name left_shift_function @d VAR_Imp_Lang "y" :: nil)
      assign_left_shift_post) left_shift_fenv dbenv nenv). unfold left_shift_pre in H. simpl. repeat econstructor. simpl. unfold update. rewrite Nat.add_0_r. reflexivity. eassumption.
    - reflexivity.
    - eapply imp_code_wf_proof.
    - unfold AbsEnv_prop_wf. econstructor. simpl. econstructor. unfold construct_trans. simpl. econstructor.
      eapply var_map_wf_left_shift_app.
      eapply var_map_wf_var_imp_lang. finite_in. finite_nodup.
    - unfold construct_trans. simpl. repeat econstructor.
    - eapply prop_wf_assign_left_shift_post.
    - assert ((ASSIGN_Imp_Lang "x" ("left_shift" @d VAR_Imp_Lang "y" :: nil) = ASSIGN_Imp_Lang "x" ("left_shift" @d VAR_Imp_Lang "y" :: nil))) by reflexivity.
      pose proof (UIP_imp_refl _ H).
      assert ((Imp_LangLogSubst.subst_AbsEnv "x"
       (Name left_shift_function @d VAR_Imp_Lang "y" :: nil)
       assign_left_shift_post) = (Imp_LangLogSubst.subst_AbsEnv "x"
       (Name left_shift_function @d VAR_Imp_Lang "y" :: nil)
       assign_left_shift_post)) by reflexivity.
      pose proof (Imp_LangLogPropDec.UIP_AbsEnv_refl _ H1).
      eapply HLImp_LangWFAssign with (Heq := H) (Hsubst := H1).
      + subst. reflexivity.
      + eapply prop_wf_assign_left_shift_post.
      + eapply imp_code_wf_proof.
      + unfold CompilerAssumptionLogicTrans.log_Imp_Lang_wf.
        repeat econstructor.
      + unfold construct_trans. simpl. econstructor. econstructor. econstructor. eapply var_map_wf_var_imp_lang. finite_in. finite_nodup. eapply var_map_wf_var_imp_lang. finite_in. finite_nodup.
      + repeat econstructor.
      + repeat econstructor.
      + repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
    - econstructor. econstructor. econstructor. simpl.
      unfold construct_trans. simpl. eapply var_map_wf_left_shift_app.
      simpl. unfold construct_trans. simpl. eapply var_map_wf_var_imp_lang. finite_in. finite_nodup.
    - repeat econstructor.
    - econstructor. unfold construct_trans. simpl. econstructor. econstructor; (eapply var_map_wf_var_imp_lang; [ finite_in | finite_nodup ]).
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
  Defined.

  Lemma check_proof_proof:
    IncompleteProofCompiler.PC.check_proof SOURCE.fenv SOURCE.funcs SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.facts SOURCE.idents SOURCE.num_args SOURCE.hoare_triple.
  Proof.
    unfold_src_tar. unfold SOURCE.facts.
    unfold assign_left_shift_triple. unfold left_shift_assign.
    eapply CAPC.PC.CheckHLPre.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - pose proof (Hi := eq_refl  (("x" <- (Name left_shift_function @d VAR_Imp_Lang "y" :: nil)))).
      simpl.
      pose proof (Heq := eq_refl ((AbsEnvLP
       (Imp_Lang_lp_arith
          (BinaryProp nat aexp_Imp_Lang
             (fun ret n : nat => ret = n + (n + 0))
             ("left_shift" @d VAR_Imp_Lang "y" :: nil) 
             (VAR_Imp_Lang "y")))))).
      eapply CAPC.PC.CheckHLAssign with (Hi := Hi) (Heq := Heq).
      + rewrite (UIP_imp_refl _ Hi). rewrite (Imp_LangLogPropDec.UIP_AbsEnv_refl _ Heq). simpl. reflexivity.
      + reflexivity.
      + simpl. unfold CAPC.PC.CC.compile_aexp. simpl. econstructor.
        econstructor. econstructor. lia. econstructor.
      + simpl. econstructor. econstructor. econstructor. econstructor. simpl. lia. econstructor. simpl. lia.
      + simpl. econstructor. econstructor. lia.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + unfold CAPC.PC.CC.compile_aexp. unfold left_shift_funcs. simpl. intros. econstructor.
        * reflexivity.
        * econstructor. econstructor. lia.
          econstructor.
        * unfold funcs_okay_too in H3. simpl in H3. destruct H3. invs H3. destruct H7. assumption.
        * unfold funcs_okay_too in H3. simpl in H3. destruct H3. invs H3. destruct H7. assumption.
        * unfold funcs_okay_too in H3. simpl in H3. destruct H3. invs H3. destruct H7. eapply StackPurestBase.aexp_frame_implies_aexp_pure. eassumption.
      + simpl. unfold IncompleteProofCompilable.SC.comp_arith. unfold IncompleteProofCompilable.SC.CC.compile_aexp. simpl. intros.
        rewrite H2. rewrite <- H. simpl. reflexivity.
  Defined.
  

  Lemma translate_precond_proof :
    CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.precond = TARGET.precond.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma translate_postcond_proof :
    CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.postcond = TARGET.postcond.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma check_logic_precond_proof :
    CAPC.SC.check_logic SOURCE.precond = true.
  Proof.
    reflexivity.
  Defined.

  Lemma check_logic_postcond_proof :
    CAPC.SC.check_logic SOURCE.postcond = true.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma program_compiled_proof : TARGET.program = CAPC.CC.compile_imp SOURCE.program SOURCE.idents SOURCE.num_args.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma check_imp_proof :
    CAPC.CC.check_imp SOURCE.program = true.
  Proof.
    reflexivity.
  Qed.
  
 

  
    
          
                                    
  Lemma implication_transformer :
    CAPC.PC.valid_imp_trans_def SOURCE.facts TARGET.facts SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. unfold SOURCE.facts. unfold TARGET.facts. simpl.
    unfold CAPC.PC.valid_imp_trans_def.
    repeat split; simpl.
    - reflexivity.
    - intros. destruct_nth_error left_shift_fact_env. simpl. reflexivity.
    - unfold StackLogic.fact_env_valid. intros. invs H; [ | invs H0].
      invc H0. clear H. unfold StackLogic.aimpstk. intros.
      unfold IncompleteProofCompilable.SC.CC.compile_aexp. simpl.
      absstate_match_inversion.
      destruct stk. invs H0. destruct stk. invs H0. invs H1.
      econstructor. econstructor. eassumption.
      econstructor; econstructor; try reflexivity; econstructor.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + econstructor. econstructor; try lia. simpl. reflexivity.
        econstructor.
      + econstructor. econstructor. reflexivity.
        econstructor; unfold stack_mapping; simpl.
        lia. lia. econstructor. econstructor. lia. simpl. lia. simpl. reflexivity. econstructor. lia. simpl. lia. simpl. reflexivity.
        econstructor. reflexivity.
      + simpl. unfold stack_mapping. simpl. econstructor. lia. simpl. lia. simpl. rewrite Nat.add_0_r. reflexivity.
      + simpl. econstructor. econstructor. econstructor. reflexivity.
      + lia.
      + simpl. lia.
      + simpl. reflexivity.
      + reflexivity.
      + repeat econstructor.
      + simpl. unfold stack_mapping. simpl. repeat econstructor.
      + simpl. unfold stack_mapping. simpl. repeat econstructor.
      + simpl. unfold stack_mapping. repeat econstructor.
      + lia.
  Defined.  
End CompileLeftShiftIncomplete.

