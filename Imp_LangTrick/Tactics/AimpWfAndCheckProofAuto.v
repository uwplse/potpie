(** Automation for aimp_wf proofs *)

From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList CompilerAssumptionLogicTrans.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod Imp_LangHoareWF ProofCompilerBase ImpHasVariableReflection FunctionWellFormedReflection.
Local Open Scope imp_langtrick_scope.

Ltac hl_Imp_Lang_wf_seq_helper :=
    match goal with
    | [ |- Imp_LangHoareWF.hl_Imp_Lang_wf ?fenv ?funcs ?idents ?num_args ?P ?Q (SEQ_Imp_Lang ?c1 ?c2) ?facts (hl_Imp_Lang_seq ?P' ?Q' ?R ?facts' ?fenv' ?c1' ?c2' ?hl1' ?hl2') ] =>
        let Heq := fresh "Heq" in
        assert (Heq : SEQ_Imp_Lang c1 c2 = SEQ_Imp_Lang c1' c2') by reflexivity || enough (Heq : SEQ_Imp_Lang c1 c2 = SEQ_Imp_Lang c1' c2');
        let Heq_refl := fresh "Heq_refl" in
        (* let HL1 := fresh "HL1" in *)
        (* let HL2 := fresh "HL2" in *)
        (* pose proof (HL1 := hl1'); *)
        (* pose proof (HL2 := hl2'); *)
        pose proof (Heq_refl := UIP_imp_refl _ Heq);
        eapply Imp_LangHoareWF.HLImp_LangWFSeq with (*hl1 := HL1) (hl2 := HL2*) (Heq := Heq); [ rewrite Heq_refl; simpl; try reflexivity | clear Heq Heq_refl .. ]
    end.

Ltac econstructor_prop_args_rel :=
  repeat match goal with
         | [ |- prop_args_rel  _ _ ] =>
             econstructor
         end.

Ltac hl_Imp_Lang_wf_roc_pre_helper :=
        match goal with
        | [ |- Imp_LangHoareWF.hl_Imp_Lang_wf ?fenv ?funcs ?idents ?num_args ?precond ?postcond ?i ?facts (hl_Imp_Lang_consequence_pre ?P ?d ?d' ?i' ?n ?facts' ?fenv' ?hlP ?Hnth' ?aimp) ] =>
            let Hnth := fresh "Hnth" in
            assert (Hnth : let ele := nth n facts (true_precondition, true_precondition) in
                           nth_error facts n = Some (fst ele, snd ele)) by reflexivity;
            pose proof (UIP_option_refl := UIP_option_pair_refl);
            specialize (UIP_option_refl _ Imp_LangLogPropDec.UIP_AbsEnv);
            specialize (UIP_option_refl _ Hnth);
            eapply Imp_LangHoareWF.HLImp_LangWFConsequencePre with (nth := Hnth); [ | | try clear UIP_option_refl; try clear Hnth .. ]
        end.

Ltac hl_imp_lang_wf_assign_helper :=
          match goal with
          | [ |- Imp_LangHoareWF.hl_Imp_Lang_wf ?fenv ?func_list ?idents ?num_args ?d ?d' (ASSIGN_Imp_Lang ?x ?a) ?facts (hl_Imp_Lang_assign ?d'' ?facts' ?fenv' ?x' ?a') ] =>
              let Hsubst := fresh "Hsubst" in
              let Heq := fresh "Heq" in
              assert (Hsubst : Imp_LangLogSubst.subst_AbsEnv x a d' = d) by reflexivity || enough (Hsubst : Imp_LangLogSubst.subst_AbsEnv x a d' = d);
              assert (Heq : ASSIGN_Imp_Lang x a = ASSIGN_Imp_Lang x' a') by reflexivity || enough (Heq: ASSIGN_Imp_Lang x a = ASSIGN_Imp_Lang x' a');
              pose proof (Hsubstrefl := Imp_LangLogPropDec.UIP_AbsEnv_refl _ Hsubst);
              pose proof (Heqrefl := UIP_imp_refl _ Heq);
              eapply Imp_LangHoareWF.HLImp_LangWFAssign with (Heq := Heq) (Hsubst := Hsubst); [try rewrite Hsubstrefl; try rewrite Heqrefl; simpl; try reflexivity | clear Hsubstrefl Heqrefl; clear Heq Hsubst .. ]
          end.



Ltac AbsEnv_prop_wf_nary_prop :=
          match goal with
          | [ |- ProofCompilerBase.AbsEnv_prop_wf ?idents ?P ] =>
              match P with
              | context P' [(NaryProp _ _ ?Q ?args)] =>
                  do 3 econstructor;
                  econstructor_prop_args_rel;
                  first [eapply CompilerCorrectHelpers.param_imp_lang_always_well_formed | eapply CompilerCorrectHelpers.const_imp_lang_always_well_formed | eapply ImpVarMapTheorems.var_map_wf_var_imp_lang | eapply CompilerCorrectHelpers.var_map_wf_wrt_aexp_subset ];
                  try first [finite_nodup | finite_in]
              end
          end.

Ltac deal_with_var_map_wf :=
          match goal with
          | [ |- var_map_wf_wrt_aexp ?idents ?a ] =>
              first [eapply CompilerCorrectHelpers.param_imp_lang_always_well_formed | eapply CompilerCorrectHelpers.const_imp_lang_always_well_formed | eapply ImpVarMapTheorems.var_map_wf_var_imp_lang | eapply CompilerCorrectHelpers.var_map_wf_wrt_aexp_subset ];
              (* simpl -[In]; *)
              cbn -[In];
              try finite_nodup; try finite_in
          | [ |- var_map_wf_wrt_bexp ?idents ?b ] =>
              first [eapply CompilerCorrectHelpers.true_imp_lang_always_well_formed | eapply CompilerCorrectHelpers.false_imp_lang_always_well_formed | eapply CompilerCorrectMoreHelpers.var_map_wf_wrt_bexp_subset; [ unfold construct_trans; cbn -[In]; intros; finite_in_implication | .. ] ];
              (* simpl -[In]; *)
              cbn -[In];
              try finite_nodup; try finite_in
          | [ |- imp_rec_rel (var_map_wf_wrt_imp ?idents) ?i ] =>
              
              first [assert (idents = construct_trans i) by reflexivity;
                     eapply CompilerCorrectMoreHelpers.var_map_wf_imp_self_imp_rec_rel
                    | eapply CompilerCorrectMoreHelpers.var_map_wf_wrt_imp_subset_imp_rec_rel; [ try eapply CompilerCorrectMoreHelpers.var_map_wf_imp_self_imp_rec_rel; unfold construct_trans; cbn -[In]; reflexivity | intros; finite_in_implication | finite_nodup .. ] ]
          end.

Ltac hl_Imp_Lang_wf_roc_post_helper :=
      match goal with
      | [ |- Imp_LangHoareWF.hl_Imp_Lang_wf ?fenv ?funcs ?idents ?num_args ?precond ?postcond ?i ?facts (hl_Imp_Lang_consequence_post ?d ?P ?d' ?i' ?n ?facts' ?fenv' ?hlP ?Hnth' ?aimp) ] =>
          let Hnth := fresh "Hnth" in
          assert (Hnth : let ele := nth n facts (true_precondition, true_precondition) in
                         nth_error facts n = Some (fst ele, snd ele)) by reflexivity;
          pose proof (UIP_option_refl := UIP_option_pair_refl);
          specialize (UIP_option_refl _ Imp_LangLogPropDec.UIP_AbsEnv);
          specialize (UIP_option_refl _ Hnth);
          (* idtac *)
          eapply Imp_LangHoareWF.HLImp_LangWFConsequencePost with (nth := Hnth); [ rewrite UIP_option_refl; try reflexivity | | try clear UIP_option_refl; try clear Hnth .. ]
      end.

(** Runs econstructor until you get to either 
 * prop_rel or prop_args_rel. 
 * Typically, you want to stop there, because it might start going into bad
 * cases from there on.
 *)
Ltac AbsEnv_prop_wf_helper :=
        repeat match goal with
               | [ |- prop_args_rel _ _ ] =>
                   fail 1
               | [ |- prop_rel _ _ ] =>
                   fail 1
               | [ |- ?sth _ ] =>
                   match sth with
                   | prop_args_rel =>
                       fail 2
                   | prop_rel =>
                       fail 2
                   | _ =>
                       econstructor
                   end
               end;
        repeat match goal with
               | [ |- prop_args_rel _ _ ] =>
                   econstructor_prop_args_rel
               | [ |- prop_rel _ _ ] =>
                   econstructor
               end.

Ltac simplify_in := cbn -[In].

Ltac simplify_var_map_wf_cases :=
  try ((AbsEnv_prop_wf_helper; deal_with_var_map_wf; cbn -[In]; intros) || deal_with_var_map_wf).

Ltac hl_wf_assign :=
  hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.

Ltac repeat_econstructor_on :=
  repeat match goal with
         | [ |- hl_Imp_Lang_wf _ _ _ _ _ _ _ _ _ ] =>
             idtac
         | [ |- AbsEnv_prop_wf _ _ ] =>
             AbsEnv_prop_wf_helper; deal_with_var_map_wf
         | [ |- imp_has_variable _ _ ] =>
             prove_imp_has_variable
         | [ |- fun_app_well_formed _ _ (APP_Imp_Lang _ _) ] =>
             prove_fun_app_wf
         | [ |- _ ] =>
             econstructor
         end.

Ltac hl_wf_seq_assign :=
  hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; [ hl_imp_lang_wf_assign_helper | ..]; simplify_var_map_wf_cases; repeat_econstructor_on.

Ltac handle_fun_app_well_formed_app :=
  prove_fun_app_wf.
  (* match goal with *)
  (* | [ |- fun_app_well_formed _ _ (APP_Imp_Lang _ _) ] => *)
  (*     econstructor; *)
  (*     [ do 4 first *)
  (*          [ handle_fun_app_well_formed_app | econstructor ] *)
  (*     | reflexivity *)
  (*     | cbn -[In]; *)
  (*       repeat *)
  (*         match goal with *)
  (*         | [ |- In _ ?b ] => unfold b *)
  (*         end; finite_in *)
  (*     | reflexivity *)
  (*     | prove_imp_has_variable *)
  (*     | solve [left; reflexivity | right; reflexivity] ] *)
  (* end. *)


Ltac log_Imp_Lang_wf_helper_no_app := repeat_econstructor_on; handle_fun_app_well_formed_app.

Ltac hl_imp_lang_wf_while_helper  :=
      match goal with
      | [ |- Imp_LangHoareWF.hl_Imp_Lang_wf ?fenv ?funcs ?idents ?args ?d ?d' (WHILE_Imp_Lang ?b ?while_body) ?facts (hl_Imp_Lang_while ?I ?b' ?while_body' ?facts' ?fenv' ?hl) ] =>
          let HeqP := fresh "HeqP" in
          let Heq := fresh "Heq" in
          assert (HeqP : afalseImp_Lang b d = d') by reflexivity || enough (HeqP : afalseImp_Lang b d = d');
          assert (Heq : WHILE_Imp_Lang b while_body = WHILE_Imp_Lang b' while_body') by reflexivity || enough (Heq: WHILE_Imp_Lang b while_body = WHILE_Imp_Lang b' while_body');
          pose proof (HeqPrefl := Imp_LangLogPropDec.UIP_AbsEnv_refl _ HeqP);
          pose proof (Heqrefl := UIP_imp_refl _ Heq);
          eapply Imp_LangHoareWF.HLImp_LangWFWhile with (Heq := Heq) (HeqP := HeqP); [try rewrite HeqPrefl; try rewrite Heqrefl; simpl; try reflexivity | clear HeqPrefl Heqrefl; clear Heq HeqP .. ]
      end.


Ltac program_subset_imp_rec_rel_var_map_wf :=
            match goal with
            | [ |- imp_rec_rel (var_map_wf_wrt_imp _) _ ] =>
                eapply CompilerCorrectMoreHelpers.var_map_wf_wrt_imp_subset_imp_rec_rel; cbn -[In];
                [ eapply CompilerCorrectMoreHelpers.var_map_wf_imp_self_imp_rec_rel; reflexivity
                | cbn -[In]; intros; finite_in_implication
                | cbn; finite_nodup_reflective .. ]
            end.


Ltac smash_other_cases :=
          repeat match goal with
                 | [ |- log_Imp_Lang_wf _ _ _ ] =>
                     try log_Imp_Lang_wf_helper_no_app
                 | [ |- log_Imp_Lang_wf_map _ _ ] =>
                     simplify_var_map_wf_cases
                 | [ |- AbsEnv_prop_rel (all_params_ok_aexp _)
                                       (all_params_ok_bexp _) _ ] =>
                     repeat_econstructor_on
                 | [ |- ProofCompilerBase.AbsEnv_prop_wf _ _ ] =>
                     simplify_var_map_wf_cases
                 | [ |- imp_rec_rel (var_map_wf_wrt_imp _) _ ] =>
                     try (solve [deal_with_var_map_wf | program_subset_imp_rec_rel_var_map_wf ])
                 | [ |- fun_app_well_formed _ _ _ ] =>
                     try FunctionWellFormedReflection.prove_fun_app_wf
                 | [ |- _ ] => idtac
                 end.

Ltac hl_Imp_Lang_wf_if_helper :=
              match goal with
              | [ |- hl_Imp_Lang_wf ?fenv ?funcs ?idents ?args ?d ?d' (IF_Imp_Lang ?b ?i1 ?i2) _ (hl_Imp_Lang_if ?P ?Q ?b' ?i1' ?i2' ?fact_env ?fenv' ?HLtrue ?HLfalse) ] =>
                  (* idtac "hi" *)
                  (* ; *)
                  let heq := fresh "heq" in
                  
                  assert (heq : IF_Imp_Lang b i1 i2 = IF_Imp_Lang b' i1' i2') by reflexivity;
                  let Himp_uip := fresh "Himp_uip" in
                  pose proof (Himp_uip := UIP_imp_refl _ heq);
                  eapply HLImp_LangWFIf with (heq := heq); try rewrite Himp_uip; try simpl; try reflexivity; try (clear Himp_uip; clear heq)
              end.
