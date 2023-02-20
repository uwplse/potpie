From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From DanTrick Require Import DanTrickLanguage DanLogProp DanLogicHelpers StackLanguage StackLangEval EnvToStack StackLogicGrammar LogicProp LogicTranslationBase StackPurest StackLangTheorems.
From DanTrick Require Import DanLogicHelpers DanTrickSemanticsMutInd StackFrame ImpVarMapTheorems RCompileMutInd.
From DanTrick Require Import FunctionWellFormed ParamsWellFormed.
Require Import CompilerCorrectMoreHelpers.

                      
Local Open Scope string_scope.


Definition comp_aexp (a: aexp_Dan) (idents: list ident) :=
  compile_aexp a (fun x => one_index_opt x idents) (List.length idents).

Definition comp_bexp (b: bexp_Dan) (idents: list ident) :=
  compile_bexp b (fun x => one_index_opt x idents) (List.length idents).

Definition comp_args (args: list aexp_Dan) (idents: list ident) :=
  List.map (fun a =>
              comp_aexp a idents) args.

Inductive no_pushes_or_pops_and_fxn_calls_fine : fun_env_stk -> imp_stack -> Prop :=
| NoPushPopSkip :
  forall fenv,
    no_pushes_or_pops_and_fxn_calls_fine fenv Skip_Stk
| NoPushPopAssign :
  forall fenv x a,
    (exists k,
        aexp_frame_rule a fenv k) ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (Assign_Stk x a)
| NoPushPopSeq :
  forall fenv i1 i2,
    no_pushes_or_pops_and_fxn_calls_fine fenv i1 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i2 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (Seq_Stk i1 i2)
| NoPushPopIf :
  forall fenv b i1 i2,
    (exists k,
        bexp_frame_rule b fenv k) ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i1 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i2 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (If_Stk b i1 i2)
| NoPushPopWhile :
  forall fenv b i,
    (exists k,
        bexp_frame_rule b fenv k) ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (While_Stk b i).


Section compile_imp_section.
  Let P1 := fun (i: imp_Dan) =>
          forall (idents: list ident) (i': imp_stack),
            i' = compile_imp i
                             (fun x : StackLanguage.ident => one_index_opt x idents)
                             (Datatypes.length idents) ->
            rcompile_imp idents i i'.

  Lemma compile_imp_adequate_backwards :
    forall (i: imp_Dan),
      P1 i.
  Proof using P1.
    pose (fun (a: aexp_Dan) =>
            forall (idents: list ident) (a': aexp_stack),
              a' = compile_aexp a
                                (fun x : StackLanguage.ident => one_index_opt x idents)
                                (Datatypes.length idents) ->
              rcompile_aexp idents a a') as P.
    pose (fun (b: bexp_Dan) =>
            forall (idents: list ident) (b': bexp_stack),
              b' = compile_bexp b
                                (fun x : StackLanguage.ident => one_index_opt x idents)
                                (Datatypes.length idents) ->
              rcompile_bexp idents b b').
    induction i using imp_Dan_ind2 with (P := P) (P0 := P0) (P1 := P1); unfold P, P0, P1; intros; subst; simpl; econstructor; eauto.
    - revert idents.
      induction H; intros.
      + constructor.
      + constructor.
        * eapply H. reflexivity.
        * eapply IHForall.
  Qed.
End compile_imp_section.


Section in_construct_trans_vs_in_free_vars_proof.
  Lemma in_construct_trans_implies_in_free_vars :
    forall (i: imp_Dan) (x: ident),
      In x (construct_trans i) ->
      In x (free_vars_imp_src i).
  Proof.
    unfold construct_trans.
    destruct i; intros; simpl in H; simpl.
    - eapply ListSet.set_union_iff.
      eapply fold_left_containment_helper_forward in H.
      eapply ListSet.set_union_iff in H.
      destruct H.
      + left. assumption.
      + right. eapply ListSet.set_union_iff in H.
        eapply ListSet.set_union_iff.
        destruct H; auto.
    - assumption.
    - eapply fold_left_containment_helper_forward in H.
      eapply ListSet.set_union_iff. eapply ListSet.set_union_iff in H.
      destruct H; auto.
    - eapply fold_left_containment_helper_forward in H.
      assumption.
    - eapply fold_left_containment_helper_forward in H.
      assumption.
  Qed.
End in_construct_trans_vs_in_free_vars_proof.

Lemma in_free_vars_implies_in_construct_trans :
  forall (i: imp_Dan) (x: ident),
    In x (free_vars_imp_src i) ->
    In x (construct_trans i).
Proof.
  intros. unfold construct_trans.
  eapply fold_left_containment_helper. assumption.
Qed.

Lemma in_construct_trans_vs_in_free_vars :
  forall (i: imp_Dan) (x: ident),
    In x (construct_trans i) <->
      In x (free_vars_imp_src i).
Proof.
  split; intros.
  - eapply in_construct_trans_implies_in_free_vars. assumption.
  - eapply in_free_vars_implies_in_construct_trans. assumption.
Qed.



Require Import Coq.Program.Equality.
Require Import DanImpHigherOrderRel DanImpHigherOrderRelTheorems.
Require Import ZArith.
Print rcomp_imp_mut_ind.

Lemma in_forall :
  forall (A: Type) (P: A -> Prop) (l: list A) (a: A),
    In a l ->
    Forall P l ->
    P a.
Proof.
  clear.
  induction l; intros.
  - invs H.
  - invs H.
    + invs H0. assumption.
    + invs H0. eapply IHl. assumption. assumption.
Qed.

Section CompiledDanFrame.
  Print stack_frame_rule_mut_ind.

  Inductive no_pushes_pops : fun_env_stk -> imp_stack -> Prop :=
  | no_pushes_pops_skip :
    forall fenv,
      no_pushes_pops fenv Skip_Stk
  | no_pushes_pops_assign :
    forall (fenv: fun_env_stk) (k: nat) (a: aexp_stack),
      1 <= k ->
      (exists f,
         aexp_frame_rule a fenv f) ->
      no_pushes_pops fenv (Assign_Stk k a)
  | no_pushes_pops_seq :
    forall (fenv: fun_env_stk) (i1 i2: imp_stack),
      no_pushes_pops fenv i1 ->
      no_pushes_pops fenv i2 ->
      no_pushes_pops fenv (Seq_Stk i1 i2)
  | no_pushes_pops_if :
    forall (fenv: fun_env_stk) (b: bexp_stack) (i1 i2: imp_stack),
      (exists f,
          bexp_frame_rule b fenv f) ->
      no_pushes_pops fenv i1 ->
      no_pushes_pops fenv i2 ->
      no_pushes_pops fenv (If_Stk b i1 i2)
  | no_pushes_pops_while :
    forall (fenv: fun_env_stk) (b: bexp_stack) (i: imp_stack),
      (exists f,
          bexp_frame_rule b fenv f) ->
      no_pushes_pops fenv i ->
      no_pushes_pops fenv (While_Stk b i).

  Lemma no_pushes_pops_means_constant_frame :
    forall (i: imp_stack) (fenv: fun_env_stk),
      no_pushes_pops fenv i ->
      exists k,
        imp_frame_rule i fenv k k.
  Proof.
    induction 1; intros.
    - exists 0. constructor.
    - destruct H0 as (aframe & FRAME).
      exists (max k aframe).
      constructor.
      + assumption.
      + lia.
      + eapply aexp_frame_expansion. eassumption. lia.
    - destruct IHno_pushes_pops1 as (frame1 & FRAME1).
      destruct IHno_pushes_pops2 as (frame2 & FRAME2).
      exists (max frame1 frame2).
      econstructor.
      + eapply imp_frame_expansion. eassumption.
        lia.
      + rewrite Nat.add_sub. rewrite <- (Nat.add_sub _ frame2) at 2.
        eapply imp_frame_expansion. assumption. lia.
    - destruct H as (frameb & Fb).
      destruct IHno_pushes_pops1 as (frame1 & F1).
      destruct IHno_pushes_pops2 as (frame2 & F2).
      exists (max frameb (max frame1 frame2)).
      econstructor; [ | rewrite <- (Nat.add_sub _ frame1) at 2 | rewrite <- (Nat.add_sub _ frame2) at 2].
      + eapply bexp_frame_expansion. eassumption. lia.
      + eapply imp_frame_expansion. assumption. lia.
      + eapply imp_frame_expansion. assumption. lia.
    - destruct H as (frameb & FRAMEb).
      destruct IHno_pushes_pops as (framebody & FRAMEbody).
      exists (max frameb framebody).
      econstructor.
      + eapply bexp_frame_expansion. eassumption. lia.
      + rewrite <- (Nat.add_sub _ framebody) at 2. eapply imp_frame_expansion.
        assumption. lia.
  Qed.

  Let P_compiled_no_pushes_pops
      (num_locals num_args: nat)
      (fenv: fun_env) (fenv': fun_env_stk) (funcs: list fun_Dan) (idents: list ident) (a: aexp_Dan) (a': aexp_stack) :=
        forall (PARAMS: all_params_ok_aexp num_args a),
        forall (FUN_APP: fun_app_well_formed fenv funcs a),
        forall (LOCALS: Datatypes.length idents = num_locals),
        forall (WF: var_map_wf_wrt_aexp idents a),
        exists frame,
          aexp_frame_rule a' fenv' frame.
  Let P0_compiled_no_pushes_pops
      (num_locals num_args: nat)
      (fenv: fun_env) (fenv': fun_env_stk) (funcs: list fun_Dan) (idents: list ident) (args: list aexp_Dan) (args': list aexp_stack) :=
        forall (PARAMS: all_params_ok_args num_args args),
        forall (FUN_APP: fun_app_args_well_formed fenv funcs args),
        forall (LOCALS: Datatypes.length idents = num_locals),
        forall (WF: Forall (var_map_wf_wrt_aexp idents) args),
        exists frame,
          args_frame_rule args' fenv' frame.

  Let P1_compiled_no_pushes_pops
      (num_locals num_args: nat)
      (fenv: fun_env) (fenv': fun_env_stk) (funcs: list fun_Dan) (idents: list ident) (b: bexp_Dan) (b': bexp_stack) :=
        forall (PARAMS: all_params_ok_bexp num_args b),
        forall (FUN_APP: fun_app_bexp_well_formed fenv funcs b),
        forall (LOCALS: Datatypes.length idents = num_locals),
        forall (WF: var_map_wf_wrt_bexp idents b),
          exists frame,
            bexp_frame_rule b' fenv' frame.
  
  Let P2_compiled_no_pushes_pops
      (num_locals num_args: nat)
      (fenv: fun_env) (fenv': fun_env_stk) (funcs: list fun_Dan) (idents: list ident) (i: imp_Dan) (i': imp_stack) :=
        forall (PARAMS: all_params_ok num_args i),
        forall (FUN_APP: fun_app_imp_well_formed fenv funcs i),
        forall (LOCALS: Datatypes.length idents = num_locals),
        forall (WF: imp_rec_rel (var_map_wf_wrt_imp idents) i),
          no_pushes_pops fenv' i'.

  Collection no_pushes_pops_props := P_compiled_no_pushes_pops P0_compiled_no_pushes_pops P1_compiled_no_pushes_pops P2_compiled_no_pushes_pops. 

  Require Import DanTrick.CompilerCorrectHelpers.
  Lemma prepend_push_frame :
    forall (n: nat) (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
      imp_frame_rule i fenv (frame + n) frame' ->
      imp_frame_rule (prepend_push i n) fenv frame frame'.
  Proof using - no_pushes_pops_props.
    clear. induction n; intros.
    - unfold prepend_push. rewrite Nat.add_0_r in H. assumption.
    - simpl. rewrite prepend_push_commutes.
      econstructor.
      + econstructor.
      + eapply IHn.
        rewrite <- Nat.add_assoc. replace (1 + n) with (S n) by lia. assumption.
  Qed.

  Definition funcs_okay_too (funcs: list fun_Dan) (fenv: fun_env_stk) :=
    Forall (fun func =>
              imp_frame_rule (StackLanguage.Body func)
                             fenv
                             (StackLanguage.Args func)
                             (StackLanguage.Return_pop func + StackLanguage.Args func) /\
                aexp_frame_rule (StackLanguage.Return_expr func)
                                fenv
                                (StackLanguage.Return_pop func + StackLanguage.Args func))
           (map compile_function funcs).

  

  Lemma compiled_means_no_pushes_pops :
    forall (num_locals num_args: nat) (fenv: fun_env) (fenv': fun_env_stk) (funcs: list fun_Dan),
    forall (FUNCS: funcs_okay_too funcs fenv'),
    forall (FENV: fenv' = compile_fenv fenv),
    forall (FENV_WF: fenv_well_formed' funcs fenv),
      rcomp_imp_mut_ind_theorem
        (P_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs)
        (P0_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs)
        (P1_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs)
        (P2_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs).
  Proof using (no_pushes_pops_props).
    intros num_locals num_args fenv fenv' funcs FUNCS_OK FENV FENV_WF.
    pose (P := RCompileMutInd.rcomp_imp_mut_ind_P (P_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs)
        );
      pose (P0 := RCompileMutInd.rcomp_imp_mut_ind_P0 (P0_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs)
        );
      pose (P1 := RCompileMutInd.rcomp_imp_mut_ind_P1 (P1_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs)
        );
      pose (P2 := RCompileMutInd.rcomp_imp_mut_ind_P2 (P2_compiled_no_pushes_pops num_locals num_args fenv fenv' funcs));
      apply (rcomp_imp_mut_ind P P0 P1 P2); unfold P, P0, P1, P2;
      clear P P0 P1 P2;
      unfold rcomp_imp_mut_ind_theorem;
      unfold RCompileMutInd.rcomp_imp_mut_ind_P,
      RCompileMutInd.rcomp_imp_mut_ind_P0,
      RCompileMutInd.rcomp_imp_mut_ind_P1,
      RCompileMutInd.rcomp_imp_mut_ind_P2;
      unfold P_compiled_no_pushes_pops, P0_compiled_no_pushes_pops, P1_compiled_no_pushes_pops, P2_compiled_no_pushes_pops;
      Tactics.revert_until P2_compiled_no_pushes_pops; clear; intros.
    - exists 0. constructor.
    - pose proof (one_index_opt_always_geq_1). specialize (H x map).  exists k. constructor; lia. 
    - exists k. constructor; lia.
    - invs PARAMS. invs FUN_APP. apply var_map_wf_plus_dan_forwards in WF. destruct WF.
      specialize (H H4 H7 eq_refl H1).
      specialize (H0 H5 H8 eq_refl H2). destruct H as (frame1 & F1).
      destruct H0 as (frame2 & F2). exists (max frame1 frame2).
      + constructor; eapply aexp_frame_expansion.
        * eapply F1.
        * lia.
        * eapply F2.
        * lia.
    - invs PARAMS. invs FUN_APP. apply var_map_wf_minus_dan_forwards in WF. destruct WF.
      specialize (H H4 H7 eq_refl H1).
      specialize (H0 H5 H8 eq_refl H2). destruct H as (frame1 & F1).
      destruct H0 as (frame2 & F2). exists (max frame1 frame2).
      + constructor; eapply aexp_frame_expansion.
        * eapply F1.
        * lia.
        * eapply F2.
        * lia.
    - invs PARAMS. invs FUN_APP.
      pose proof (var_map_wf_app_dan_args_all _ _ _ WF).
      specialize (H H2 H3 eq_refl H0).
      destruct H as (frame & F).
      exists frame.
      econstructor.
      + assumption.
      + reflexivity.
      + remember (compile_fenv fenv) as fenv'.
        remember (fenv' f) as func'.
        pose proof (Hfunc' := Heqfunc').
        rewrite Heqfenv' in Hfunc'.
        unfold compile_fenv in Hfunc'.
        unfold compile_function in Hfunc'.
        remember (pre_compile_function (fenv f)) as comp.
        unfold pre_compile_function in Heqcomp. unfold compile_code in Heqcomp. unfold stack_mapping in Heqcomp. rewrite Heqcomp in Hfunc'. simpl in Hfunc'. clear Heqcomp. clear comp. rewrite Hfunc'. simpl.
        unfold funcs_okay_too in FUNCS_OK.
        eapply Forall_map in FUNCS_OK.
        pose proof (in_forall).
        specialize (H _ _ funcs (fenv f) H5 FUNCS_OK).
        simpl in H. destruct H. rewrite Nat.add_comm. assumption.
      + remember (compile_fenv fenv) as fenv'.
        remember (fenv' f) as func'.
        pose proof (Hfunc' := Heqfunc').
        rewrite Heqfenv' in Hfunc'.
        unfold compile_fenv in Hfunc'.
        unfold compile_function in Hfunc'.
        remember (pre_compile_function (fenv f)) as comp.
        unfold pre_compile_function in Heqcomp. unfold compile_code in Heqcomp. unfold stack_mapping in Heqcomp. rewrite Heqcomp in Hfunc'. simpl in Hfunc'. clear Heqcomp. clear comp. rewrite Hfunc'. simpl.
        unfold funcs_okay_too in FUNCS_OK.
        eapply Forall_map in FUNCS_OK.
        pose proof (in_forall).
        specialize (H _ _ funcs (fenv f) H5 FUNCS_OK).
        simpl in H. destruct H. rewrite Nat.add_comm. assumption.
    - exists 0. constructor.
    - invs PARAMS. rename H4 into P1. rename H5 into P2. invs FUN_APP. rename H5 into F1. rename H6 into F2. invs WF. rename H3 into WF1. rename H4 into WF2.
      specialize (H P1 F1 eq_refl WF1).
      specialize (H0 P2 F2 eq_refl WF2).
      destruct H as (frame1 & FRAME1).
      destruct H0 as (frame2 & FRAME2).
      exists (max frame1 frame2).
      econstructor.
      + eapply aexp_frame_expansion. eapply FRAME1. lia.
      + eapply args_frame_expansion. eapply FRAME2. lia.
    - exists 0. constructor.
    - exists 0. constructor.
    - invs PARAMS. invs FUN_APP. eapply var_map_wf_neg_dan in WF; [ | eauto ].
      specialize (H H2 H4 eq_refl WF).
      invs H. exists x. constructor. assumption.
    - invs PARAMS. rename H4 into P1. rename H5 into P2.
      invs FUN_APP. rename H5 into F1. rename H6 into F2.
      eapply var_map_wf_and_or_dan_forwards in WF; [ | eauto ].
      destruct WF as (WF1 & WF2).
      specialize (H P1 F1 eq_refl WF1).
      specialize (H0 P2 F2 eq_refl WF2).
      destruct H. destruct H0. exists (max x x0).
      constructor.
      + eapply bexp_frame_expansion.
        eassumption. lia.
      + eapply bexp_frame_expansion. eassumption. lia.
    - invs PARAMS. rename H4 into P1. rename H5 into P2.
      invs FUN_APP. rename H5 into F1. rename H6 into F2.
      eapply var_map_wf_and_or_dan_forwards in WF; [ | eauto ].
      destruct WF as (WF1 & WF2).
      specialize (H P1 F1 eq_refl WF1).
      specialize (H0 P2 F2 eq_refl WF2).
      destruct H. destruct H0. exists (max x x0).
      constructor.
      + eapply bexp_frame_expansion.
        eassumption. lia.
      + eapply bexp_frame_expansion. eassumption. lia.
    - invs PARAMS. rename H4 into P1. rename H5 into P2.
      invs FUN_APP. rename H5 into F1. rename H6 into F2.
      eapply var_map_wf_leq_dan_forwards in WF; [ | eauto ].
      destruct WF as (WF1 & WF2).
      specialize (H P1 F1 eq_refl WF1).
      specialize (H0 P2 F2 eq_refl WF2).
      destruct H. destruct H0. exists (max x x0).
      constructor.
      + eapply aexp_frame_expansion.
        eassumption. lia.
      + eapply aexp_frame_expansion. eassumption. lia.
    - constructor.
    - constructor.
      + rewrite e. eapply one_index_opt_always_geq_1.
      + invs PARAMS. invs FUN_APP. invs WF. unfold_wf_imp_in H3.
        invs WF'. eapply H. eassumption. assumption. reflexivity. assumption.
    - invs PARAMS. invs FUN_APP. invs WF.
      econstructor; eauto.
    - invs PARAMS. invs FUN_APP. invs WF. unfold_wf_imp_in H14. clear WF0. clear WF''. invc WF'.
      econstructor; eauto.
    - invs PARAMS. invs FUN_APP. invs WF. unfold_wf_imp_in H9. clear WF0. clear WF''.
      invc WF'. econstructor; eauto.
  Qed.

  Lemma aexp_compiled_no_pushes_pops :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (fenv' : fun_env_stk) (funcs : list fun_Dan)
      (idents : list StackLanguage.ident) (a : aexp_Dan)
      (a' : aexp_stack),
      funcs_okay_too funcs fenv' ->
      fenv' = compile_fenv fenv ->
      fenv_well_formed' funcs fenv ->
      rcompile_aexp idents a a' ->
      all_params_ok_aexp num_args a ->
      fun_app_well_formed fenv funcs a ->
      Datatypes.length idents = num_locals ->
      var_map_wf_wrt_aexp idents a ->
      exists frame : nat, aexp_frame_rule a' fenv' frame.
  Proof.
    intros.
    eapply compiled_means_no_pushes_pops; eassumption.
  Qed.
  Lemma args_compiled_no_pushes_pops :
      forall (num_locals num_args : nat) (fenv : fun_env)
        (fenv' : fun_env_stk) (funcs : list fun_Dan)
        (idents : list StackLanguage.ident) (args : list aexp_Dan)
        (args' : list aexp_stack),
        funcs_okay_too funcs fenv' ->
        fenv' = compile_fenv fenv ->
        fenv_well_formed' funcs fenv ->
        rcompile_args idents args args' ->
        all_params_ok_args num_args args ->
        fun_app_args_well_formed fenv funcs args ->
        Datatypes.length idents = num_locals ->
        Forall (var_map_wf_wrt_aexp idents) args ->
        exists frame : nat, args_frame_rule args' fenv' frame.
  Proof.
    intros.
    eapply compiled_means_no_pushes_pops; eassumption.
  Qed.
  Lemma bexp_compiled_no_pushes_pops :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (fenv' : fun_env_stk) (funcs : list fun_Dan)
      (idents : list StackLanguage.ident) (b : bexp_Dan)
         (b' : bexp_stack),
      funcs_okay_too funcs fenv' ->
      fenv' = compile_fenv fenv ->
      fenv_well_formed' funcs fenv ->
      rcompile_bexp idents b b' ->
      all_params_ok_bexp num_args b ->
      fun_app_bexp_well_formed fenv funcs b ->
      Datatypes.length idents = num_locals ->
      var_map_wf_wrt_bexp idents b ->
      exists frame : nat, bexp_frame_rule b' fenv' frame.
  Proof.
    intros.
    eapply compiled_means_no_pushes_pops; eassumption.
  Qed.

  Lemma imp_compiled_no_pushes_pops :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (fenv' : fun_env_stk) (funcs : list fun_Dan)
      (idents: list StackLanguage.ident) (i: imp_Dan) (i': imp_stack),
      funcs_okay_too funcs fenv' ->
      fenv' = compile_fenv fenv ->
      fenv_well_formed' funcs fenv ->
      rcompile_imp idents i i' ->
      all_params_ok num_args i ->
      fun_app_imp_well_formed fenv funcs i ->
      Datatypes.length idents = num_locals ->
      imp_rec_rel (var_map_wf_wrt_imp idents) i -> no_pushes_pops fenv' i'.
  Proof.
    intros.
    eapply compiled_means_no_pushes_pops; eassumption.
  Qed.
                                                                            
  
  
  Let P_compiled_dan_min_frame (num_locals num_args: nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list ident)
      (a': aexp_stack) (fenv': fun_env_stk) (frame: nat) :=
        forall (a: aexp_Dan),
        forall (PARAMS: all_params_ok_aexp num_args a),
        forall (FUN_APP: fun_app_well_formed fenv funcs a),
        forall (WF: var_map_wf_wrt_aexp idents a),
        forall (FENV_COMP: fenv' = compile_fenv fenv),
          rcompile_aexp idents a a' ->
          exists (min: nat),
            aexp_frame_rule a' fenv' min /\
              (forall f,
                  aexp_frame_rule a' fenv' f -> min <= f) /\
              min <= num_locals + num_args.

  Let P0_compiled_dan_min_frame (num_locals num_args: nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list ident)
      (args': list aexp_stack) (fenv': fun_env_stk) (frame: nat) :=
        forall (args: list aexp_Dan),
        forall (PARAMS: all_params_ok_args num_args args),
        forall (FUN_APP: fun_app_args_well_formed fenv funcs args),
        forall (WF: Forall (var_map_wf_wrt_aexp idents) args),
        forall (FENV_COMP: fenv' = compile_fenv fenv),
          rcompile_args idents args args' ->
          exists (min: nat),
            args_frame_rule args' fenv' min /\
              (forall f,
                  args_frame_rule args' fenv' f -> min <= f) /\
              min <= num_locals + num_args.
                
  Let P1_compiled_dan_min_frame (num_locals num_args: nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list ident)
      (b': bexp_stack) (fenv': fun_env_stk) (frame: nat) :=
        forall (b: bexp_Dan),
        forall (PARAMS: all_params_ok_bexp num_args b),
        forall (FUN_APP: fun_app_bexp_well_formed fenv funcs b),
        forall (WF: var_map_wf_wrt_bexp idents b),
        forall (FENV_COMP: fenv' = compile_fenv fenv),
          rcompile_bexp idents b b' ->
          exists (min: nat),
            bexp_frame_rule b' fenv' min /\
              (forall f,
                  bexp_frame_rule b' fenv' f -> min <= f) /\
              min <= num_locals + num_args.
  Let P2_compiled_dan_min_frame (num_locals num_args: nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list ident)
      (i': imp_stack) (fenv': fun_env_stk) (frame frame': nat) :=
        forall (i: imp_Dan),
        forall (PARAMS: all_params_ok num_args i),
        forall (FUN_APP: fun_app_imp_well_formed fenv funcs i),
        forall (WF: imp_rec_rel (var_map_wf_wrt_imp idents) i),
          forall (FENV_COMP: fenv' = compile_fenv fenv),
          rcompile_imp idents i i' ->
          exists (min: nat),
            imp_frame_rule i' fenv' min (min + frame' - frame) /\
              (forall f f',
                  imp_frame_rule i' fenv' f f' -> min <= f) /\
              min <= num_locals + num_args.

  Let P2_compiled_dan_frame (num_locals num_args: nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list ident)
      (i': imp_stack) (fenv': fun_env_stk) (frame frame': nat) :=
        forall (i: imp_Dan),
        forall (PARAMS: all_params_ok num_args i),
        forall (FUN_APP: fun_app_imp_well_formed fenv funcs i),
        forall (WF: imp_rec_rel (var_map_wf_wrt_imp idents) i),
        forall (FENV_COMP: fenv' = compile_fenv fenv),
          rcompile_imp idents i i' ->
          frame = frame' /\ (frame = frame' -> exists (min: nat),
            imp_frame_rule i' fenv' min (min + frame' - frame) /\
              (forall f f',
                  imp_frame_rule i' fenv' f f' -> min <= f) /\
              min <= num_locals + num_args).

   Lemma compiled_dan_frame :
    forall (num_locals num_args: nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list ident),
    forall (FENV_WF: fenv_well_formed' funcs fenv),
      num_locals = Datatypes.length idents ->
      frame_rule_mut_ind_theorem
        (P_compiled_dan_min_frame num_locals num_args fenv funcs idents)
        (P0_compiled_dan_min_frame num_locals num_args fenv funcs idents)
        (P1_compiled_dan_min_frame num_locals num_args fenv funcs idents)
        (P2_compiled_dan_frame num_locals num_args fenv funcs idents).
  Proof.
    intros ? ? ? ? ? ? LEN.
    pose (P := frame_rule_mut_ind_theorem_P (P_compiled_dan_min_frame num_locals num_args fenv funcs idents)
        );
      pose (P0 := frame_rule_mut_ind_theorem_P0 (P0_compiled_dan_min_frame num_locals num_args fenv funcs idents)
        );
      pose (P1 := frame_rule_mut_ind_theorem_P1 (P1_compiled_dan_min_frame num_locals num_args fenv funcs idents)
        );
      pose (P2 := frame_rule_mut_ind_theorem_P2 (P2_compiled_dan_frame num_locals num_args fenv funcs idents));
      apply (stack_frame_rule_mut_ind P P0 P1 P2); unfold P, P0, P1, P2;
      clear P P0 P1 P2;
      unfold frame_rule_mut_ind_theorem_P, frame_rule_mut_ind_theorem_P0,
      frame_rule_mut_ind_theorem_P1, frame_rule_mut_ind_theorem_P2;
      unfold P_compiled_dan_min_frame, P0_compiled_dan_min_frame, P1_compiled_dan_min_frame, P2_compiled_dan_frame; Tactics.revert_until P2_compiled_dan_min_frame; clear; intros.
        - invs H. exists 0.
      split; [ | split ]; intros.
      + econstructor.
      + lia.
      + lia.
    - invs H.
      + remember (one_index_opt x idents) as k.
        unfold_wf_aexp_in WF.
        pose proof (A x _ eq_refl). simpl in H0.
        specialize (H0 (or_introl eq_refl)).
        symmetry in Heqk.
        eapply inside_implies_within_range' with (index := k) in H0.
        exists k.
        split; [ | split ]; intros.
        * econstructor. assumption. reflexivity.
        * invs H1. assumption.
        * eapply le_plus_trans. assumption.
        * assumption.
      + exists (Datatypes.length idents + n + 1).
        split; [ | split ]; intros.
        * econstructor. assumption.  reflexivity.
        * invs H0. assumption.
        * invs PARAMS. rewrite <- Nat.add_assoc. eapply plus_le_compat_l. lia.
    - invs H1.
      eapply var_map_wf_plus_dan_forwards in WF.
      rename a4 into a1'. rename a5 into a2'.
      destruct WF as (WF1 & WF2).
      invs FUN_APP. rename H8 into FWF1. rename H9 into FWF2.
      invs PARAMS. rename H5 into PARAMS1. rename H8 into PARAMS2.
      rename H6 into COMP1.
      rename H7 into COMP2.
      specialize (H a1' PARAMS1 FWF1 WF1 eq_refl COMP1).
      specialize (H0 a2' PARAMS2 FWF2 WF2 eq_refl COMP2).
      destruct H, H0. destruct H, H0. destruct H2, H3.
      exists (max x x0).
      split; [ | split ]; intros.
      + econstructor. eapply aexp_frame_expansion. eapply H. lia.
        eapply aexp_frame_expansion. eapply H0. lia.
      + pose proof (MAX := Nat.max_spec).
        specialize (MAX x x0).
        invs H6.
        destruct MAX as [MAX | MAX]; destruct MAX as [INEQ MAXeq].
        * rewrite MAXeq. eapply H3. eassumption.
        * rewrite MAXeq. eapply H2. eassumption.
      + lia.
    - invs H1.
      eapply var_map_wf_minus_dan_forwards in WF.
      rename a4 into a1'. rename a5 into a2'.
      destruct WF as (WF1 & WF2).
      invs FUN_APP. rename H8 into FWF1. rename H9 into FWF2.
      invs PARAMS. rename H5 into PARAMS1. rename H8 into PARAMS2.
      rename H6 into COMP1.
      rename H7 into COMP2.
      specialize (H a1' PARAMS1 FWF1 WF1 eq_refl COMP1).
      specialize (H0 a2' PARAMS2 FWF2 WF2 eq_refl COMP2).
      destruct H, H0. destruct H, H0. destruct H2, H3.
      exists (max x x0).
      split; [ | split ]; intros.
      + econstructor. eapply aexp_frame_expansion. eapply H. lia.
        eapply aexp_frame_expansion. eapply H0. lia.
      + pose proof (MAX := Nat.max_spec).
        specialize (MAX x x0).
        invs H6.
        destruct MAX as [MAX | MAX]; destruct MAX as [INEQ MAXeq].
        * rewrite MAXeq. eapply H3. eassumption.
        * rewrite MAXeq. eapply H2. eassumption.
      + lia.
    - invs H2. pose proof (var_map_wf_app_dan_args_all _ _ _ WF).
      invs PARAMS.
      rename H7 into PARAMSargs.
      rename H3 into WFargs.
      rename H6 into COMPargs.
      rename H2 into COMPapp.
      invs FUN_APP. rename H4 into FUN_APPexprs.
      rename H11 into Fwf. rename H10 into HasRet. rename H7 into ARGS.
      rename H6 into ContainsFunc.
      specialize (H _ PARAMSargs FUN_APPexprs WFargs eq_refl COMPargs).
      destruct H as [min [FRAMEargs [MINargs LEQ]]].
      exists min.
      split; [ | split ]; intros.
      + econstructor. eassumption. reflexivity. assumption.
        assumption.
      + eapply MINargs. invs H. assumption.
      + eassumption.
    - invs H. exists 0. split; [ | split ]; intros.
      + constructor.
      + lia.
      + lia.
    - invs H1.
      rename H6 into COMParg. rename H7 into COMPargs. invs FUN_APP.
      rename H6 into FUNarg. rename H7 into FUNargs. invs WF.
      rename H4 into WFarg. rename H5 into WFargs.
      invs PARAMS. rename H5 into PARAMSarg. rename H6 into PARAMSargs.
      specialize (H _ PARAMSarg FUNarg WFarg eq_refl COMParg).
      specialize (H0 _ PARAMSargs FUNargs WFargs eq_refl COMPargs).
      destruct H as [min_arg [FrameArg [MinArg LeqArg]]].
      destruct H0 as [min_args [FrameArgs [MinArgs LeqArgs]]].
      exists (Nat.max min_arg min_args).
      split; [ | split]; intros.
      + econstructor.
        * eapply aexp_frame_expansion. eapply FrameArg. lia.
        * eapply args_frame_expansion. eapply FrameArgs. lia.
      + pose proof (MAX := Nat.max_spec).
        specialize (MAX min_arg min_args).
        invs H.
        destruct MAX as [MAX | MAX]; destruct MAX as [INEQ MAXeq].
        * rewrite MAXeq. eapply MinArgs. eassumption.
        * rewrite MAXeq. eapply MinArg. eassumption.
      + lia.
    - exists 0. split; [ | split ]; intros.
      + constructor.
      + lia.
      + lia.
    - exists 0. split; [ | split ]; intros; [ constructor | lia .. ].
    - invs H0. rename H4 into COMP. invs FUN_APP. rename H4 into FUNb.
      eapply var_map_wf_neg_dan in WF; [ | reflexivity ].
      invs PARAMS. rename H3 into PARAMSb.
      specialize (H _ PARAMSb FUNb WF eq_refl COMP).
      destruct H as [min [FrameB [Min Leq]]].
      exists min. split; [ | split ]; intros.
      + econstructor. assumption.
      + eapply Min. invs H. eassumption.
      + assumption.
    - invs H1. rename H6 into COMP1. rename H7 into COMP2.
      rename b4 into b1'. rename b5 into b2'.
      eapply var_map_wf_and_or_dan_forwards in WF; eauto.
      destruct WF as (WF1 & WF2).
      invc FUN_APP. rename H6 into FUN1. rename H7 into FUN2.
      invc PARAMS. rename H5 into P1. rename H6 into P2.
      specialize (H _ P1 FUN1 WF1 eq_refl COMP1).
      specialize (H0 _ P2 FUN2 WF2 eq_refl COMP2).
      destruct H as (min1 & Frame1 & Min1 & Leq1).
      destruct H0 as (min2 & Frame2 & Min2 & Leq2).
      exists (max min1 min2).
      split; [ | split ]; intros.
      + econstructor; eapply bexp_frame_expansion.
        * eapply Frame1.
        * lia.
        * eapply Frame2.
        * lia.
      + invs H. eapply Min1 in H3. eapply Min2 in H6. lia.
      + lia.
    - invs H1. rename H6 into COMP1. rename H7 into COMP2.
      rename b4 into b1'. rename b5 into b2'.
      eapply var_map_wf_and_or_dan_forwards in WF; eauto.
      destruct WF as (WF1 & WF2).
      invc FUN_APP. rename H6 into FUN1. rename H7 into FUN2.
      invc PARAMS. rename H5 into P1. rename H6 into P2.
      specialize (H _ P1 FUN1 WF1 eq_refl COMP1).
      specialize (H0 _ P2 FUN2 WF2 eq_refl COMP2).
      destruct H as (min1 & Frame1 & Min1 & Leq1).
      destruct H0 as (min2 & Frame2 & Min2 & Leq2).
      exists (max min1 min2).
      split; [ | split ]; intros.
      + econstructor; eapply bexp_frame_expansion.
        * eapply Frame1.
        * lia.
        * eapply Frame2.
        * lia.
      + invs H. eapply Min1 in H3. eapply Min2 in H6. lia.
      + lia.
    - invs H1.
      eapply var_map_wf_leq_dan_forwards in WF; [ | reflexivity ].
      rename a3 into a1'. rename a4 into a2'.
      destruct WF as (WF1 & WF2).
      invs FUN_APP. rename H8 into FWF1. rename H9 into FWF2.
      invs PARAMS. rename H5 into PARAMS1. rename H8 into PARAMS2.
      rename H6 into COMP1.
      rename H7 into COMP2.
      specialize (H a1' PARAMS1 FWF1 WF1 eq_refl COMP1).
      specialize (H0 a2' PARAMS2 FWF2 WF2 eq_refl COMP2).
      destruct H, H0. destruct H, H0. destruct H2, H3.
      exists (max x x0).
      split; [ | split ]; intros.
      + econstructor. eapply aexp_frame_expansion. eapply H. lia.
        eapply aexp_frame_expansion. eapply H0. lia.
      + pose proof (MAX := Nat.max_spec).
        specialize (MAX x x0).
        invs H6.
        destruct MAX as [MAX | MAX]; destruct MAX as [INEQ MAXeq].
        * rewrite MAXeq. eapply H3. eassumption.
        * rewrite MAXeq. eapply H2. eassumption.
      + lia.
    - invs H1.
    - split; intros; try (split; [ | split ]); intros.
      reflexivity.
      + exists 0.
        split; [ | split].
        * rewrite Nat.add_sub. constructor.
        * intros. lia.
        * lia.
    - invs H0. invs FUN_APP. invs PARAMS.
      invs WF. unfold_wf_imp_in H5. invs WF'.
      specialize (H _ H3 H4 H7 eq_refl H6).
      destruct H as [min [FRAMEmin [Min Leq]]].
      
      split; [ reflexivity | exists (max (one_index_opt x idents) min) ].
      split; [ | split ]; intros.
      + rewrite Nat.add_sub. econstructor.
        assumption. lia.
        eapply aexp_frame_expansion.
        eapply FRAMEmin.
        lia.
      + invs H1.
        eapply Min in H13. lia.
      +
        Print imp_has_variable.
        assert ((x =? x) = true).
        eapply String.eqb_eq. reflexivity.
        pose proof (InIdents := WF'' x (ImpHasVarAssignee _ x a1 H1)).
        pose proof (inside_implies_within_range').
        specialize (H2 _ _ _ InIdents eq_refl).
        pose proof (Nat.max_spec (one_index_opt x idents) min).
        destruct H5 as [MAX | MAX]; destruct MAX as [MAXineq MAXeq]; rewrite MAXeq.
        * lia.
        * eapply le_plus_trans. assumption.
    - invs H.
    - invs H.
    - invs H1. rename i4 into i1'.
      rename i5 into i2'. rename H6 into COMP1. rename H7 into COMP2.
      invs WF. rename H4 into REC1. rename H6 into REC2. rename H7 into WFseq.
      invs FUN_APP. rename H6 into FUN1. rename H7 into FUN2.
      invs PARAMS. rename H5 into OK1. rename H6 into OK2.
      specialize (H _ OK1 FUN1 REC1 eq_refl COMP1).
      specialize (H0 _ OK2 FUN2 REC2 eq_refl COMP2).
      destruct H as [FramesEq1 H].
      destruct H0 as [FramesEq2 H0].
      subst frame'. subst frame. rename frame'' into frame.
      specialize (H eq_refl). specialize (H0 eq_refl).
      destruct H as [min1 [Frame1 [Min1 Leq1]]].
      destruct H0 as [min2 [Frame2 [Min2 Leq2]]].
      split. reflexivity.
      intros.
      rewrite Nat.add_sub in *.
      exists (max min1 min2).
      split; [ | split ]; intros.
      + rewrite Nat.add_sub. econstructor.
        * eapply frame_expansion. eapply Frame1. lia.
        * rewrite Nat.add_sub.
          rewrite <- (Nat.add_sub (max min1 min2) min2) at 2.
          eapply imp_frame_expansion. assumption. lia.
      + invs H0.
        assert (f = frame').
        eapply frames_equal.
        eapply i. assumption. reflexivity. subst f.
        eapply Min1 in H4. eapply Min2 in H8. lia.
      + lia.
    - invs H2. rename H8 into COMPb. rename H9 into COMP1. rename H10 into COMP2.
      rename i4 into i1'. rename i5 into i2'. rename b1 into b'.
      invs WF. rename H7 into REC1. rename H8 into REC2. rename H9 into WFif.
      invs FUN_APP. rename H8 into FUNb. rename H9 into FUN1. rename H10 into FUN2.
      invs PARAMS. rename H7 into PARAMb. rename H8 into PARAM1. rename H9 into PARAM2.
      pose proof (WF' := WFif).
      unfold_wf_imp_in WF'. clear WF0. clear WF''. invc WF'0. clear H9 H10. rename H8 into WFb.
      specialize (H _ PARAMb FUNb WFb eq_refl COMPb).
      specialize (H0 _ PARAM1 FUN1 REC1 eq_refl COMP1).
      specialize (H1 _ PARAM2 FUN2 REC2 eq_refl COMP2).
      destruct H1, H0. clear H1. split. assumption.
      intros. clear H1. specialize (H3 H0). specialize (H4 H0).
      symmetry in H0. subst frame'.
      destruct H3 as [min2 [Frame2 [Min2 Leq2]]].
      destruct H4 as [min1 [Frame1 [Min1 Leq1]]].
      destruct H as [minb [Frameb [Minb Leqb]]].
      exists (max minb (max min1 min2)).
      split.
      + rewrite Nat.add_sub. econstructor.
        * eapply bexp_frame_expansion. eapply Frameb. lia.
        * rewrite <- (Nat.add_sub _ min1) at 2.
          eapply imp_frame_expansion. rewrite Nat.add_sub in Frame1. assumption.
          lia.
        * rewrite <- (Nat.add_sub _ min2) at 2.
          eapply imp_frame_expansion. rewrite Nat.add_sub in Frame2. assumption.
          lia.
      + split; intros.
        * invs H.
          assert (f = f').
          eapply frames_equal. eapply i0. assumption. reflexivity.
          symmetry in H0. subst f'.
          eapply Minb in H4. eapply Min1 in H8. eapply Min2 in H9. lia.
        * lia.
    - split; [ reflexivity | ].
      intros. clear H2.
      invs H1. rename H6 into COMPb. rename H7 into COMPbody.
      rename b into b'. rename b1 into b. rename loop_body into body'. rename i1 into body.
      invs WF.
      pose proof (H7 := H6).
      unfold_wf_imp_in H7. clear WF0. clear WF''. invc WF'. clear H9.
      rename H5 into REC. rename H8 into WFb.
      invs FUN_APP. rename H7 into FUNb. rename H8 into FUNbody.
      invs PARAMS. rename H5 into Pb. rename H7 into Pbody.
      specialize (H0 _ Pbody FUNbody REC eq_refl COMPbody).
      specialize (H _ Pb FUNb WFb eq_refl COMPb).
      destruct H as (minb & FRAMEb & Minb & Leqb).
      destruct H0. apply H0 in H. clear H0.
      destruct H as (minbody & FRAMEbody & Minbody & Leqbody).
      exists (max minb minbody).
      split; [ | split ].
      + rewrite Nat.add_sub in *. econstructor.
        * eapply bexp_frame_expansion. eapply FRAMEb.
          lia.
        * rewrite <- (Nat.add_sub _ minbody) at 2.
          eapply imp_frame_expansion. eapply FRAMEbody. lia.
      + intros.
        invs H.
        eapply Minbody in H8. eapply Minb in H3. lia.
      + lia.
  Qed.

  Lemma compiled_aexp_dan_frame :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (funcs : list fun_Dan) (idents : list ident),
      fenv_well_formed' funcs fenv ->
      num_locals = Datatypes.length idents ->
      (forall (a : aexp_stack) (fenv0 : fun_env_stk) (frame : nat),
          aexp_frame_rule a fenv0 frame ->
          forall a0 : aexp_Dan,
            all_params_ok_aexp num_args a0 ->
            fun_app_well_formed fenv funcs a0 ->
            var_map_wf_wrt_aexp idents a0 ->
            fenv0 = compile_fenv fenv ->
            rcompile_aexp idents a0 a ->
            exists min : nat,
              aexp_frame_rule a fenv0 min /\
                (forall f : nat, aexp_frame_rule a fenv0 f -> min <= f) /\
                min <= num_locals + num_args).
  Proof.
    intros. eapply compiled_dan_frame; eassumption.
  Qed.

  Lemma compiled_args_dan_frame :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (funcs : list fun_Dan) (idents : list ident),
      fenv_well_formed' funcs fenv ->
      num_locals = Datatypes.length idents ->
    (forall (args : list aexp_stack) (fenv0 : fun_env_stk) (frame : nat),
        args_frame_rule args fenv0 frame ->
        forall args0 : list aexp_Dan,
          all_params_ok_args num_args args0 ->
          fun_app_args_well_formed fenv funcs args0 ->
          Forall (var_map_wf_wrt_aexp idents) args0 ->
          fenv0 = compile_fenv fenv ->
          rcompile_args idents args0 args ->
          exists min : nat,
            args_frame_rule args fenv0 min /\
              (forall f : nat, args_frame_rule args fenv0 f -> min <= f) /\
              min <= num_locals + num_args).
  Proof.
    intros. eapply compiled_dan_frame; eassumption.
  Qed.

  Lemma compiled_bexp_dan_frame :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (funcs : list fun_Dan) (idents : list ident),
      fenv_well_formed' funcs fenv ->
      num_locals = Datatypes.length idents ->
      (forall (b : bexp_stack) (fenv0 : fun_env_stk) (frame : nat),
          bexp_frame_rule b fenv0 frame ->
          forall b0 : bexp_Dan,
            all_params_ok_bexp num_args b0 ->
            fun_app_bexp_well_formed fenv funcs b0 ->
            var_map_wf_wrt_bexp idents b0 ->
            fenv0 = compile_fenv fenv ->
            rcompile_bexp idents b0 b ->
            exists min : nat,
              bexp_frame_rule b fenv0 min /\
                (forall f : nat, bexp_frame_rule b fenv0 f -> min <= f) /\
                min <= num_locals + num_args).
  Proof.
    intros. eapply compiled_dan_frame; eassumption.
  Qed.

  Lemma compiled_imp_dan_frame :
    forall (num_locals num_args : nat) (fenv : fun_env)
      (funcs : list fun_Dan) (idents : list ident),
      fenv_well_formed' funcs fenv ->
      num_locals = Datatypes.length idents ->
    (forall (i : imp_stack) (fenv0 : fun_env_stk) (frame frame' : nat),
        imp_frame_rule i fenv0 frame frame' ->
        forall i0 : imp_Dan,
          all_params_ok num_args i0 ->
          fun_app_imp_well_formed fenv funcs i0 ->
          imp_rec_rel (var_map_wf_wrt_imp idents) i0 ->
          fenv0 = compile_fenv fenv ->
          rcompile_imp idents i0 i ->
          frame = frame' /\
            (frame = frame' ->
             exists min : nat,
               imp_frame_rule i fenv0 min (min + frame' - frame) /\
                 (forall f f' : nat, imp_frame_rule i fenv0 f f' -> min <= f) /\
                 min <= num_locals + num_args)).
  Proof.
    intros. eapply compiled_dan_frame; eassumption.
  Qed.

  Lemma compiled_imp_has_constant_frame :
    forall (num_locals num_args: nat) (fenv: fun_env)
      (funcs: list fun_Dan) (idents: list ident)
      (i: imp_Dan)
      (i' : imp_stack) (fenv' : fun_env_stk),
      rcompile_imp idents i i' ->
      fenv' = compile_fenv fenv ->
      funcs_okay_too funcs fenv' ->
      fenv_well_formed' funcs fenv ->
      all_params_ok num_args i ->
      fun_app_imp_well_formed fenv funcs i ->
      imp_rec_rel (var_map_wf_wrt_imp idents) i ->
      num_locals = Datatypes.length idents ->
      exists frame,
        imp_frame_rule i' fenv' frame frame.
  Proof.
    intros.
    pose proof (imp_compiled_no_pushes_pops).
    symmetry in H6.
    specialize (H7 num_locals num_args fenv fenv' funcs idents i i' H1 H0 H2 H H3 H4 H6 H5).
    eapply no_pushes_pops_means_constant_frame in H7. destruct H7. exists x. assumption.
  Qed.

  Lemma compiled_imp_function_has_typical_frame :
    forall (num_locals num_args: nat) (fenv: fun_env)
      (funcs: list fun_Dan) (idents: list ident)
      (i: imp_Dan)
      (i' : imp_stack) (fenv' : fun_env_stk)
      (frame frame': nat) (func: fun_Dan),
      i = DanTrickLanguage.Body func ->
      idents = construct_trans i ->
      rcompile_imp idents i i' ->
      fenv' = compile_fenv fenv ->
      fenv_well_formed' funcs fenv ->
      num_args = DanTrickLanguage.Args func ->
      all_params_ok num_args i ->
      fun_app_imp_well_formed fenv funcs i ->
      imp_rec_rel (var_map_wf_wrt_imp idents) i ->
      num_locals = Datatypes.length idents ->
      frame = num_locals + num_args ->
      frame' = num_locals + num_args ->
      funcs_okay_too funcs fenv' ->
      imp_frame_rule i' fenv' frame frame'.
  Proof.
    intros.
    pose proof (compiled_imp_dan_frame).
    pose proof (compiled_imp_has_constant_frame).
    specialize (H13 num_locals num_args fenv funcs idents i i' fenv' H1 H2 H11 H3 H5 H6 H7 H8).
    destruct H13 as (frame'' & IMP_FRAME).
    specialize (H12 num_locals num_args fenv funcs idents H3 H8 i' fenv' frame'' frame'' IMP_FRAME i H5 H6 H7 H2 H1).
    destruct H12. apply H13 in H12. clear H13. destruct H12 as (min & FRAMEmin & FORALL & Leq). rewrite Nat.add_sub in FRAMEmin. rewrite <- (Nat.add_sub frame' min).
    replace (frame') with frame.
    eapply imp_frame_expansion.
    assumption.
    lia. subst. reflexivity.
  Qed.
    
           
  
  Lemma funcs_okay_too_proof :
    forall (funcs: list fun_Dan) (fenv: fun_env)
      (fenv': fun_env_stk) (func: fun_Dan) func' (num_args: nat) (body: imp_Dan),
      funcs_okay_too funcs fenv' ->
      func' = compile_function func ->
      fenv' = compile_fenv fenv ->
      fenv_well_formed' funcs fenv ->
      body = DanTrickLanguage.Body func ->
      num_args = DanTrickLanguage.Args func ->
      all_params_ok num_args body ->
      fun_app_imp_well_formed fenv funcs body ->
      imp_frame_rule (StackLanguage.Body func') fenv'
                     (StackLanguage.Args func')
                     (StackLanguage.Return_pop func' + StackLanguage.Args func').
  Proof.
    intros ? ? ? ? ? ? ? OK. unfold funcs_okay_too in OK. intros.
    unfold compile_function in H. unfold pre_compile_function in H. simpl in H.
    remember ((compile_imp (DanTrickLanguage.Body func)
                           (stack_mapping (DanTrickLanguage.Body func))
                           (Datatypes.length
                              (construct_trans (DanTrickLanguage.Body func))))) as C.
    unfold stack_mapping in HeqC. remember (construct_trans (DanTrickLanguage.Body func)) as idents.
    rewrite <- H2 in *.
    pose proof (VAR_WF := var_map_wf_imp_self_imp_rec_rel).
    specialize (VAR_WF body idents).
    symmetry in Heqidents.
    specialize (VAR_WF Heqidents).
    rewrite H. simpl. eapply prepend_push_frame.
    rewrite Nat.add_comm.
    eapply compiled_imp_function_has_typical_frame.
    + eassumption.
    + symmetry in Heqidents. eassumption.
    + eapply compile_imp_adequate_backwards.
      eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + assumption.
    + reflexivity.
    + rewrite <- H3. reflexivity.
    + rewrite <- H3. reflexivity.
    + unfold funcs_okay_too. assumption.
  Qed.

  Lemma funcs_okay_too_proof_second_try :
    forall (funcs: list fun_Dan) (fenv: fun_env)
      (fenv': fun_env_stk) (func: fun_Dan) func' (num_args num_locals: nat) (body: imp_Dan) (idents: list StackLanguage.ident),
    forall (IDENT: idents = construct_trans body),
    forall (OK: funcs_okay_too funcs fenv'),
    forall (COMP_FENV: fenv' = compile_fenv fenv),
    forall (COMP_FUNC: func' = compile_function func),
    forall (FENV_WF: fenv_well_formed' funcs fenv),
    forall (BODY: body = DanTrickLanguage.Body func),
    forall (NUM_ARGS: num_args = DanTrickLanguage.Args func)
      (NUM_LOCALS: num_locals = Datatypes.length idents)
      (PARAMS: all_params_ok num_args body)
      (IMP_HAS_VAR: imp_has_variable (Ret func) body)
      (FUN: fun_app_imp_well_formed fenv funcs body),
      aexp_frame_rule (StackLanguage.Return_expr func') fenv'
                      (StackLanguage.Return_pop func' + StackLanguage.Args func').
  Proof.
    intros.
    unfold compile_function in COMP_FUNC. unfold pre_compile_function in COMP_FUNC. simpl in COMP_FUNC.
    rewrite <- BODY in COMP_FUNC. rewrite <- IDENT in COMP_FUNC. rewrite <- NUM_LOCALS in COMP_FUNC. unfold stack_mapping in COMP_FUNC. rewrite <- IDENT in COMP_FUNC.
    pose proof (AEXP := compiled_aexp_dan_frame).
    pose proof (AEXP' := aexp_compiled_no_pushes_pops).
    assert (COMP_AEXP : rcompile_aexp idents (VAR_Dan (Ret func)) (Return_expr func')).
    rewrite COMP_FUNC. simpl. econstructor. reflexivity.
    assert (PARAMS_OK_RET : all_params_ok_aexp num_args (VAR_Dan (Ret func))) by constructor.
    assert (FUN_RET : fun_app_well_formed fenv funcs (VAR_Dan (Ret func))) by constructor.
    assert (VAR_WF : var_map_wf_wrt_aexp idents (VAR_Dan (Ret func))).
    {
      eapply var_map_wf_var_dan.
      - rewrite IDENT. eapply in_free_vars_implies_in_construct_trans. eapply free_vars_in_imp_has_variable. reflexivity. eassumption.
      - pose proof (VAR_WF := var_map_wf_imp_self_imp_rec_rel).
        specialize (VAR_WF body idents).
        symmetry in IDENT. specialize (VAR_WF IDENT).
        eapply imp_rec_rel_self in VAR_WF. unfold_wf_imp_in VAR_WF. destruct WF. assumption.
    }
    Print fenv_well_formed'.
    symmetry in NUM_LOCALS.
    specialize (AEXP' num_locals num_args fenv fenv' funcs idents (VAR_Dan (Ret func)) (Return_expr func') OK COMP_FENV FENV_WF COMP_AEXP PARAMS_OK_RET FUN_RET NUM_LOCALS VAR_WF).
    destruct AEXP' as (frame__aexp & RET_FRAME).
    symmetry in NUM_LOCALS.
    specialize (AEXP num_locals num_args fenv funcs idents FENV_WF NUM_LOCALS _ _ _ RET_FRAME _ PARAMS_OK_RET FUN_RET VAR_WF COMP_FENV COMP_AEXP).
    destruct AEXP as (min & FRAMEmin & FORALL & Leq).
    eapply aexp_frame_expansion.
    eapply FRAMEmin. rewrite COMP_FUNC. simpl. rewrite <- NUM_ARGS. assumption.
  Qed.

  Lemma triangle_something_something_from_real_analysis :
    forall (n1 n2 n3: nat),
      n1 <= n2 <= n3 \/ n2 <= n1 <= n3 \/
        n2 <= n3 <= n1 \/ n3 <= n2 <= n1 \/
        n3 <= n1 <= n2 \/ n1 <= n3 <= n2.
  Proof.
    clear. intros.
    pose proof (H13 := le_gt_dec n1 n3).
    destruct H13 as [H13 | H31 ].
    - pose proof (H23 := le_gt_dec n2 n3).
      destruct H23 as [H23 | H32].
      + pose proof (H12 := le_gt_dec n1 n2).
        destruct H12 as [H12 | H21].
        * left. lia.
        * right. left. lia.
      + right. right. right. right. right. lia.
    - pose proof (H23 := le_gt_dec n2 n3).
      destruct H23 as [H23 | H32].
      + right. right. left. lia.
      + pose proof (H12 := le_gt_dec n1 n2).
        destruct H12 as [H12 | H21 ].
        * right. right. right. right. left. lia.
        * right. right. right. left. lia.
  Qed.

End CompiledDanFrame.

Lemma imp_frame_of_compiled_imp_dan :
  forall (i: imp_Dan) (idents: list ident) (num_locals num_args frame: nat) (fenv: fun_env_stk) (fenv': fun_env),
  forall (funcs: list fun_Dan),
    fenv = compile_fenv fenv' ->
    funcs_okay_too funcs fenv ->
    all_params_ok num_args i ->
    fun_app_imp_well_formed fenv' funcs i ->
    fenv_well_formed' funcs fenv' ->
    idents = construct_trans i ->
    num_locals = Datatypes.length idents ->
    imp_rec_rel (var_map_wf_wrt_imp idents) i ->
    frame = num_locals + num_args ->
    imp_frame_rule (compile_imp i (stack_mapping i) num_locals)
                   fenv
                   frame
                   frame.
Proof.
  pose proof (compiled_imp_dan_frame).
  pose proof compiled_imp_has_constant_frame.
  intros.
  remember (compile_imp i (stack_mapping i) num_locals) as i'.
  unfold stack_mapping in Heqi'.
  rewrite <- H6 in Heqi'.
  rewrite H7 in Heqi'.
  eapply compile_imp_adequate_backwards in Heqi'.
  specialize (H0 num_locals num_args _ _ _ _ _ _ Heqi' H1 H2 H5 H3 H4 H8 H7).
  destruct H0.
  specialize (H num_locals num_args fenv' funcs idents H5 H7 i' fenv x x H0 i H3 H4 H8 H1 Heqi').
  destruct H. apply H10 in H. clear H10. destruct H. destruct H. rewrite Nat.add_sub in H. destruct H10.
  repeat rewrite H9.
  rewrite <- (Nat.add_sub (num_locals + num_args) x0) at 2.
  eapply imp_frame_expansion.
  assumption. assumption.
Qed.






Lemma frame_pure_of_compiled_fenv_helper :
  forall (num_locals: nat) (i_body: imp_Dan) (s_body: imp_stack) (frame_beginning frame_end num_args : nat) (fenv: fun_env) (funcs: list fun_Dan) (idents: list StackLanguage.ident) (fenv_s: fun_env_stk),
  forall (FENV: fenv_s = compile_fenv fenv),
  forall (FUNC_OK: funcs_okay_too funcs fenv_s),
  forall (REC: imp_rec_rel (var_map_wf_wrt_imp idents) i_body),
  forall (FUN_APP:  fun_app_imp_well_formed fenv funcs i_body),
    idents = construct_trans i_body ->
    num_locals = Datatypes.length idents ->
    frame_beginning = num_args ->
    frame_end = num_locals + num_args ->
    fenv_well_formed' funcs fenv ->
    all_params_ok num_args i_body ->
    s_body = fst (compile_code i_body) ->
    imp_frame_rule (s_body) (compile_fenv fenv) (frame_beginning) (frame_end).
Proof.
  intros.
  unfold compile_code in H5.
  rewrite H5.
  unfold fst.
  eapply prepend_push_frame.
  subst frame_beginning. rewrite <- H. rewrite <- H0.
  rewrite H2. rewrite Nat.add_comm.
  eapply imp_frame_of_compiled_imp_dan.
  reflexivity. rewrite <- FENV. eassumption. eassumption. eassumption. eassumption.
  eassumption. eassumption. assumption. reflexivity.
Qed.

Lemma frame_pure_of_compiled_fenv' :
  forall (idents: list StackLanguage.ident) i_body fenv_i fenv_s f func_i func_s body i_args i_ret f_name funcs,
  forall (IDENT : idents = construct_trans i_body),
  forall (OKAY: funcs_okay_too funcs fenv_s),
    fenv_s = compile_fenv fenv_i ->
    func_s = fenv_s f ->
    all_params_ok i_args i_body ->
  forall (RET_POP : Return_pop (func_s) = Datatypes.length idents),
  forall (FUNC: func_i = {| DanTrickLanguage.Name := f_name
                    ; DanTrickLanguage.Args := i_args
                    ; DanTrickLanguage.Ret := i_ret
                    ; DanTrickLanguage.Body := i_body |}),
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUNC': func_i = fenv_i f),
      body = (Body func_s) ->
      StackFrameBase.imp_frame_rule
        body
        fenv_s (Args (func_s))
        (Return_pop (func_s) + Args (func_s)).
Proof.
  intros.
  pose proof (WF := var_map_wf_imp_self_imp_rec_rel).
  specialize (WF i_body (construct_trans i_body) eq_refl).
  rewrite <- IDENT in WF.
  subst.
  
  unfold compile_fenv. 
  remember (pre_compile_function (fenv_i f)) as PRE.
  pose proof (PRE_COMP := HeqPRE).
  unfold pre_compile_function in HeqPRE. rewrite <- FUNC' in HeqPRE. simpl in HeqPRE.
  rewrite PRE_COMP in HeqPRE.
  clear PRE_COMP.

  unfold fenv_well_formed' in FENV_WF.
  eapply frame_pure_of_compiled_fenv_helper; try reflexivity; try eassumption.
  + rewrite <- FUNC'. simpl. assumption.
  + destruct FENV_WF as (_ & FENV_WF').
    specialize (FENV_WF' f (fenv_i f) eq_refl).
    destruct FENV_WF' as (_ & FUN & _).
    assumption.
  + unfold compile_function. repeat rewrite HeqPRE.
    simpl. rewrite <- FUNC'. simpl. assumption.
Qed.

Lemma frame_pure_of_return_expr :
  forall fenv_i f funcs,
    fenv_well_formed' funcs fenv_i ->
    StackFrameBase.aexp_frame_rule
      (Return_expr (compile_fenv fenv_i f))
      (compile_fenv fenv_i)
      (Return_pop (compile_fenv fenv_i f) + Args (compile_fenv fenv_i f)).
Proof.
  intros. unfold fenv_well_formed' in H. destruct H as (NODUP & H).
  unfold compile_fenv. fold (compile_fenv fenv_i). remember (compile_function (fenv_i f)) as func'.
  remember (fenv_i f) as func.
  specialize (H f func Heqfunc). destruct H. unfold compile_function in Heqfunc'. remember (pre_compile_function func) as pre_func.
  unfold pre_compile_function in Heqpre_func. rewrite Heqpre_func in Heqfunc'. simpl in Heqfunc'. rewrite Heqfunc'. simpl. constructor.
  unfold stack_mapping.
  apply one_index_opt_always_geq_1.
  unfold stack_mapping.
  destruct H0 as (WF & HASVAR).
  eapply free_vars_in_imp_has_variable in HASVAR; [ | eauto ].
  eapply in_free_vars_implies_in_construct_trans in HASVAR.
  pose proof (inside_implies_within_range' (construct_trans (DanTrickLanguage.Body func)) (Ret func) (one_index_opt (Ret func) (construct_trans (DanTrickLanguage.Body func))) HASVAR eq_refl). eapply le_plus_trans. assumption.
Qed.

Local Definition rcomp_pure_P (funcs: list fun_Dan) (idents: list ident) (adan: aexp_Dan) (astk: aexp_stack): Prop :=
  forall fenv_i fenv_s dbenv nenv val,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    fenv_well_formed' funcs fenv_i ->
    fun_app_well_formed fenv_i funcs adan ->
    var_map_wf_wrt_aexp idents adan ->
    fenv_s = compile_fenv fenv_i ->
    a_Dan adan dbenv fenv_i nenv val ->
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    aexp_frame_rule astk fenv_s (Datatypes.length idents + Datatypes.length dbenv).

Local Definition rcomp_pure_P0 (funcs: list fun_Dan) (idents: list ident) (adans: list aexp_Dan) (astks: list aexp_stack): Prop :=
  forall fenv_i fenv_s dbenv nenv vals,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    fenv_well_formed' funcs fenv_i ->
    fun_app_args_well_formed fenv_i funcs adans ->
    Forall (var_map_wf_wrt_aexp idents) adans ->
    fenv_s = compile_fenv fenv_i ->
    args_Dan adans dbenv fenv_i nenv vals ->
    forall (OKparams: Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    args_frame_rule astks fenv_s (Datatypes.length idents + Datatypes.length dbenv).

Lemma rcomp_aexp_args_implies_frame :
  forall (funcs: list fun_Dan),
    rcompile_aexp_args_mut_ind_theorem (rcomp_pure_P funcs) (rcomp_pure_P0 funcs).
Proof.
  intros funcs.
  pose (fun (l : list StackLanguage.ident) (a : aexp_Dan) (a0 : aexp_stack) =>
        fun (_: rcompile_aexp l a a0) =>
          rcomp_pure_P funcs l a a0) as P.
  pose (fun (l : list StackLanguage.ident) (adans : list aexp_Dan) (astks : list aexp_stack) =>
        fun (_: rcompile_args l adans astks) =>
          rcomp_pure_P0 funcs l adans astks) as P0.

  eapply rcompile_aexp_args_mut_ind with (P := P) (P0 := P0); unfold P, P0; unfold rcomp_pure_P, rcomp_pure_P0; intros.
  - constructor.
  - rewrite e. unfold_wf_aexp_in H1. econstructor.
    + eapply one_index_opt_always_geq_1.
    + assert (one_index_opt x map <= Datatypes.length map).
      eapply inside_implies_within_range'.
      eapply A. reflexivity. simpl. left. reflexivity.
      reflexivity.
      eapply le_plus_trans. assumption.
  - subst k. inversion H3. subst n0 dbenv0 fenv nenv0 m.
    constructor. lia.
    pose proof (nth_error_Some).
    assert (nth_error dbenv n <> None).
    unfold not. intros. rewrite H6 in H7. inversion H7.
    apply H4 in H7. eapply Nat.le_succ_l in H7.
    rewrite <- Nat.add_assoc.
    eapply plus_le_compat_l.
    rewrite Nat.add_1_r. assumption.
  - revert H4. invs H5. invs H2. intros.
    eapply var_map_wf_plus_dan_forwards in H3. destruct H3.
    constructor.
    + eapply H; try eassumption.
    + eapply H0; try eassumption.
  - revert H4. invs H5. invs H2. intros.
    eapply var_map_wf_minus_dan_forwards in H3. destruct H3.
    constructor.
    + eapply H; try eassumption.
    + eapply H0; try eassumption.
  - revert H3. invs H4. invs H1. eapply var_map_wf_app_dan_args_all in H2.
    intros. econstructor.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
      * assumption.
      * eassumption.
      * eassumption.
      * eassumption.
    + reflexivity.
    + rewrite H3. simpl. pose proof (FENV_WF := H0). unfold fenv_well_formed' in H0. destruct H0.
      remember (compile_fenv fenv_i f) as func'.
      pose proof (H10 := Heqfunc').
      unfold compile_fenv in Heqfunc'. unfold compile_function in Heqfunc'.
      remember (fenv_i f) as func.
      remember (pre_compile_function func) as pre.
      unfold pre_compile_function in Heqpre. destruct func eqn:?. simpl. simpl in *.
      rewrite Heqpre in Heqfunc'. simpl in Heqfunc'.
      replace Args with (StackLanguage.Args func').
      replace (Datatypes.length (construct_trans Body)) with (Return_pop (compile_fenv fenv_i f)).
      rewrite Nat.add_comm.
      rewrite H10.
      eapply frame_pure_of_compiled_fenv' with (i_body := DanTrickLanguage.Body (fenv_i f)).
      * reflexivity.
      * rewrite <- H3. eassumption.
      * reflexivity.
      * reflexivity.
      * pose proof (InForall := in_forall).
        specialize (InForall fun_Dan (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs {| DanTrickLanguage.Name := Name; DanTrickLanguage.Args := Args; Ret := Ret; DanTrickLanguage.Body := Body |} H11 OKparams).
        cbn beta in InForall. simpl in InForall. rewrite <- Heqfunc. simpl. eassumption.
      * simpl. reflexivity.
      * rewrite <- Heqfunc. simpl. eassumption.
      * eassumption.
      * rewrite <- Heqfunc. rewrite Heqf0. reflexivity.
      * simpl. rewrite <- Heqfunc. simpl. reflexivity.
      * rewrite <- H10. rewrite Heqfunc'. simpl. reflexivity.
      * rewrite Heqfunc'.  simpl. reflexivity.
    + rewrite H3.
      pose proof (frame_pure_of_return_expr fenv_i f funcs H0). rewrite Nat.add_comm. assumption.
  - constructor.
  - revert H4. invs H2. invs H3. invs H5. intros. constructor.
    + eapply H; try eassumption.
    + eapply H0; try eassumption.
Qed.

Local Definition rcomp_pure_P' (map: list ident) (adan: aexp_Dan) (astk: aexp_stack): Prop :=
  forall fenv_i fenv_s funcs,
    fenv_s = compile_fenv fenv_i ->
    fenv_well_formed' funcs fenv_i ->
    fun_app_well_formed fenv_i funcs adan ->
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    aexp_stack_pure_rel astk fenv_s.

Local Definition rcomp_pure_P0' (map: list ident) (adans: list aexp_Dan) (astks: list aexp_stack): Prop :=
  forall fenv_i fenv_s funcs,
    fenv_s = compile_fenv fenv_i ->
    fenv_well_formed' funcs fenv_i ->
    fun_app_args_well_formed fenv_i funcs adans ->
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    args_stack_pure_rel astks fenv_s.

Lemma rcomp_aexp_args_implies_pure :
  rcompile_aexp_args_mut_ind_theorem rcomp_pure_P' rcomp_pure_P0'.
Proof.
  rcompile_aexp_args_mutual_induction P P0 rcomp_pure_P' rcomp_pure_P0'; intros.
  - econstructor.
  - econstructor. subst.
    remember (one_index_opt x map) as n.
    revert Heqn.
    revert H1.
    revert x map.
    induction n; intros.
    + unfold one_index_opt in Heqn. destruct map; [ discriminate | ].
      destruct_discrim (string_dec s x).
    + intuition.
  - econstructor. rewrite e. intuition.
  - inversion H3. subst fenv wf_funcs a0 a3. econstructor; [ eapply H | eapply H0]; eassumption.
  - inversion H3. subst fenv wf_funcs a0 a3.  econstructor; [ eapply H | eapply H0]; eassumption.
  - inversion H2. subst fenv wf_funcs f0 args. pose proof (H3 := H1). unfold fenv_well_formed' in H1. destruct H1 as (NODUP & WF). econstructor.
    + eapply eq_refl.
    + eapply H; eassumption.
    + rewrite H0.
      pose proof (H9 := H6).
      destruct func eqn:? in H9.
      eapply frame_pure_of_compiled_fenv' with (i_body := DanTrickLanguage.Body func).
      * reflexivity.
      * 
        rewrite <- H0. eassumption.
      * reflexivity.
      * reflexivity.
      * pose proof (InForall := in_forall).
        specialize (InForall fun_Dan (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs func H7 OKparams).
        cbn beta in InForall. simpl in InForall. simpl. eassumption.
      * simpl. rewrite <- H9. simpl. rewrite Heqf0. simpl. reflexivity.
      * rewrite Heqf0. simpl. rewrite H9. reflexivity.
      * eassumption.
      * reflexivity.
      * reflexivity.
    + rewrite H0.
      eapply frame_pure_of_return_expr.
      eassumption.
    + pose proof (frame_pure_of_return_expr fenv_i f funcs H3). rewrite <- H0 in H1. eapply aexp_frame_implies_aexp_pure. eassumption.
  - econstructor.
  - inversion H3. subst fenv wf_funcs arg args. econstructor.
    eapply H; eassumption.
    eapply H0; eassumption.
Qed.

Local Definition P_imply_frame (idents: list ident) (a: aexp_Dan) (a': aexp_stack) :=
  forall dbenv fenv nenv n,
    a_Dan a dbenv fenv nenv n ->
    var_map_wf_wrt_aexp idents a ->
    aexp_frame_rule a' (compile_fenv fenv) (Datatypes.length idents + Datatypes.length dbenv).

Local Definition P0_imply_frame (idents: list ident) (args: list aexp_Dan) (args': list aexp_stack) :=
  forall dbenv fenv nenv vals,
    args_Dan args dbenv fenv nenv vals ->
    Forall (var_map_wf_wrt_aexp idents) args ->
    args_frame_rule args' (compile_fenv fenv) (Datatypes.length idents + Datatypes.length dbenv).

Local Definition P1_imply_frame (idents: list ident) (b: bexp_Dan) (b': bexp_stack) :=
  forall dbenv fenv nenv v,
    b_Dan b dbenv fenv nenv v ->
    var_map_wf_wrt_bexp idents b ->
    bexp_frame_rule b' (compile_fenv fenv) (Datatypes.length idents + Datatypes.length dbenv).

Local Definition P2_imply_frame (idents: list ident) (i: imp_Dan) (i': imp_stack) :=
  forall dbenv fenv nenv nenv',
    i_Dan i dbenv fenv nenv nenv' ->
    var_map_wf_wrt_imp idents i ->
    imp_frame_rule i' (compile_fenv fenv) (Datatypes.length idents + Datatypes.length dbenv) (Datatypes.length idents + Datatypes.length dbenv).

Lemma in_and_not_in_implies_not_equal :
  forall (A: Type) (x x': A) (xs: list A),
    In x xs ->
    ~ (In x' xs) ->
    x <> x'.
Proof.
  unfold not; intros.
  rewrite <- H1 in H0. apply H0 in H. assumption.
Qed.

Lemma in_implies_find_index_rel :
  forall idents x,
    In x idents ->
    NoDup idents ->
    exists n,
      find_index_rel idents x (Some n).
Proof.
  induction idents; intros.
  - invs H.
  - invs H.
    + exists 0. econstructor. reflexivity.
    + invs H0. apply in_and_not_in_implies_not_equal with (x := x) (x' := a) in H4; [ | assumption .. ]. apply IHidents in H1; [ | assumption ]. destruct H1. exists (S x0).
      constructor.
      * assumption.
      * assumption.
Qed.

Lemma comp_aexp_implies_pure :
  forall adan astk map,
    astk = compile_aexp adan (fun x => one_index_opt x map) (List.length map) ->
    forall fenv_i fenv_s dbenv nenv stk stk' val val' funcs,
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUN_APP: fun_app_well_formed fenv_i funcs adan),
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      fenv_s = compile_fenv fenv_i ->
      a_Dan adan dbenv fenv_i nenv val ->
      aexp_stack_sem astk fenv_s stk (stk', val') ->
      aexp_stack_pure_rel astk fenv_s.
Proof.
  pose proof (rcomp_aexp_args_implies_pure).
  intros.
  unfold rcompile_aexp_args_mut_ind_theorem, rcomp_pure_P', rcomp_pure_P0' in H.
  pose proof (compile_aexp_args_adequate_backwards).
  eapply H4 in H0.
  destruct H as (AEXP & _).
  eapply AEXP; try eassumption.
Qed.

Lemma comp_aexp_implies_pure' :
  forall adan astk map,
    astk = compile_aexp adan (fun x => one_index_opt x map) (List.length map) ->
    forall fenv_i fenv_s funcs,
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUN_APP: fun_app_well_formed fenv_i funcs adan),
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      fenv_s = compile_fenv fenv_i ->
      aexp_stack_pure_rel astk fenv_s.
Proof.
  pose proof (rcomp_aexp_args_implies_pure).
  intros.
  unfold rcompile_aexp_args_mut_ind_theorem, rcomp_pure_P', rcomp_pure_P0' in H.
  destruct H as (AEXP & _).
  pose proof (compile_aexp_args_adequate_backwards).
  eapply H in H0.
  eapply AEXP; try eassumption.
Qed.

Lemma comp_bexp_implies_pure' :
  forall bdan bstk map,
    bstk = compile_bexp bdan (fun x => one_index_opt x map) (List.length map) ->
    forall fenv_i fenv_s funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUN_APP: fun_app_bexp_well_formed fenv_i funcs bdan),
      fenv_s = compile_fenv fenv_i ->
      bexp_stack_pure_rel bstk fenv_s.
Proof.
  induction bdan; intros; try simpl in H; try subst; try econstructor.
  1-5: match goal with
    | |- bexp_stack_pure_rel (compile_bexp ?bdan _ _ ) _ =>
        match goal with
        | [ IH : forall (bstk: bexp_stack) (n_args: nat) (map: list string),
              bstk = compile_bexp bdan _ _ ->
              forall fenv_d fenv_s,
                fenv_s = compile_fenv fenv_d ->
                bexp_stack_pure_rel (compile_bexp bdan _ _) bstk _ |- _ ] =>
            eapply IH; try eapply eq_refl
        | [ IH : context [compile_bexp bdan _ _] |- _ ] =>
              eapply IH; try eapply eq_refl
        | _ => idtac
        end
       end.
  all: try solve [eassumption | invs FUN_APP; eassumption].
  all: invs FUN_APP; eapply comp_aexp_implies_pure'; eauto.
Qed.

Lemma comp_bexp_implies_pure :
  forall bdan bstk map,
    bstk = compile_bexp bdan (fun x => one_index_opt x map) (List.length map) ->
    forall fenv_i fenv_s dbenv nenv stk stk' val val' funcs,
      fenv_s = compile_fenv fenv_i ->
      forall (OKfuncs: funcs_okay_too funcs fenv_s),
      forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      forall (FENV_WF: fenv_well_formed' funcs fenv_i),
      forall (FUN_APP: fun_app_bexp_well_formed fenv_i funcs bdan),
      b_Dan bdan dbenv fenv_i nenv val ->
      bexp_stack_sem bstk fenv_s stk (stk', val') ->
      bexp_stack_pure_rel bstk fenv_s.
Proof.
  induction bdan; intros.
  - simpl in H. rewrite H. constructor.
  - simpl in H. rewrite H. constructor.
  - simpl in H. rewrite H. constructor. inversion H1. clear H3 H5 H6 H7 H8.
    rewrite H in H2. inversion H2. inversion FUN_APP.
    eapply IHbdan.
    + assert (compile_bexp bdan
    (fun x : DanTrickLanguage.ident => one_index_opt x map)
    (Datatypes.length map) = compile_bexp bdan
    (fun x : DanTrickLanguage.ident => one_index_opt x map)
    (Datatypes.length map)) by reflexivity.
      eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  - simpl in H. rewrite H in *. invc H2. invs H1. invs FUN_APP. econstructor.
    + eapply IHbdan1; [ eapply eq_refl | eapply eq_refl | eassumption  .. ].
    + eapply IHbdan2; [ eapply eq_refl | eapply eq_refl | eassumption .. ].
  - simpl in H. rewrite H in *. invc H2. invs H1. invs FUN_APP. econstructor.
    + eapply IHbdan1; [eapply eq_refl | eapply eq_refl | eassumption .. ].
    + eapply IHbdan2; [ eapply eq_refl | eapply eq_refl | eassumption .. ].
  - simpl in H. rewrite H in *. invc H2. invs H1. invs FUN_APP. econstructor; (eapply comp_aexp_implies_pure; solve [eapply eq_refl | eassumption]). 
Qed.



Scheme compile_prop_rel_sane_ind := Induction for compile_prop_rel Sort Prop.

Lemma bool_compile_prop_args_rel_implies_pure :
  forall c (dl: list bexp_Dan) (sl: list bexp_stack),
    compile_prop_args_rel c dl sl ->
    forall (map: list ident),
      c = comp_bool map ->
      forall fenv_i fenv_s dbenv nenv stk stk' dvals svals funcs,
        forall (OKfuncs: funcs_okay_too funcs fenv_s),
        forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
        fenv_s = compile_fenv fenv_i ->
        forall (FENV_WF: fenv_well_formed' funcs fenv_i),
        forall (FUN_APP: prop_args_rel (V := bool) (fun_app_bexp_well_formed fenv_i funcs) dl),
        eval_prop_args_rel (fun expr val =>
                         b_Dan expr dbenv fenv_i nenv val) dl dvals ->
        eval_prop_args_rel (fun expr val =>
                         bexp_stack_sem expr fenv_s stk (stk', val))
                      sl svals ->
        prop_args_rel (V := bool) (fun expr => StackPurestBase.bexp_stack_pure_rel
                           expr fenv_s) sl.
Proof.
  intros c dl sl. induction 1; intros.
  - econstructor.
  - invs H3. invs H2. unfold comp_bool in *.
    econstructor.
    + invs FUN_APP. eapply comp_bexp_implies_pure.
      * eapply eq_refl.
      * eapply eq_refl.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
    + eapply IHcompile_prop_args_rel; try eassumption.
      eapply eq_refl. reflexivity.
      invs FUN_APP. assumption.
Qed.

Lemma bool_compile_prop_args_rel_implies_pure' :
  forall c (dl: list bexp_Dan) (sl: list bexp_stack),
    compile_prop_args_rel c dl sl ->
    forall (map: list ident),
      c = comp_bool map ->
      forall fenv_i fenv_s funcs,
        forall (OKfuncs: funcs_okay_too funcs fenv_s),
        forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
        forall (FENV_WF: fenv_well_formed' funcs fenv_i),
        forall (FUN_APP: prop_args_rel (V := bool) (fun_app_bexp_well_formed fenv_i funcs) dl),
        fenv_s = compile_fenv fenv_i ->
        prop_args_rel (V := bool) (fun expr => StackPurestBase.bexp_stack_pure_rel
                           expr fenv_s) sl.
Proof.
  intros c dl sl. induction 1; intros.
  - econstructor.
  - invs FUN_APP. econstructor; subst; unfold comp_bool in *.
    + eapply comp_bexp_implies_pure'; eauto.
    + eapply IHcompile_prop_args_rel; eauto.
Qed.


Ltac eval_prop_rel_inversion num_repeats :=
  (do
    num_repeats (
         try match goal with
             | [ H : eval_prop_rel ?func ?prop |- _ ] =>
                 let n := numgoals in
                 invc H;
                 let n' := numgoals in
                 guard n = n'           
             end)).

Ltac bexp_inversion :=
  match goal with
  | [ H : bexp_stack_sem ?bexp _ _ _ |- _ ] =>
      match bexp with
      | True_Stk => fail
      | False_Stk => fail
      | _ => invc H
      end
  | [ H : b_Dan ?bexp _ _ _ _ |- _ ] =>
      match bexp with
      | TRUE_Dan => fail
      | FALSE_Dan => fail
      | _ => invc H
      end
  end.


Lemma bool_compile_prop_rel_implies_pure' :
  forall (dl: LogicProp bool bexp_Dan) c (sl: LogicProp bool bexp_stack),
    compile_prop_rel c dl sl ->
    forall (map: list ident),
      c = comp_bool map ->
      forall fenv_i fenv_s funcs,
      forall (OKfuncs: funcs_okay_too funcs fenv_s),
        forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
        forall (FENV_WF: fenv_well_formed' funcs fenv_i),
        forall (FUN_APP: prop_rel (V := bool) (fun_app_bexp_well_formed fenv_i funcs) dl),
        fenv_s = compile_fenv fenv_i ->
        prop_rel (fun expr => StackPurestBase.bexp_stack_pure_rel
                             expr fenv_s) sl.
Proof.
  intros dl c sl COMP. dependent induction COMP; intros; invs FUN_APP; try econstructor; unfold comp_bool in *; subst; try (eapply comp_bexp_implies_pure'; eauto).
  - eapply IHCOMP1; eauto. 
  - eapply IHCOMP2; eauto. 
  - eapply IHCOMP1; eauto.
  - eapply IHCOMP2; eauto. 
  - eapply bool_compile_prop_args_rel_implies_pure'; try eassumption; try eapply eq_refl.
Qed.

       

Lemma bool_compile_prop_rel_implies_pure :
  forall c (dl: LogicProp bool bexp_Dan) (sl: LogicProp bool bexp_stack),
    compile_prop_rel c dl sl ->
    forall (args: nat) (map: list ident),
      c = comp_bool map ->
      forall fenv_i fenv_s dbenv nenv stk stk' funcs,
      forall (OKfuncs: funcs_okay_too funcs fenv_s),
        forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
        forall (FENV_WF: fenv_well_formed' funcs fenv_i),
        forall (FUN_APP: prop_rel (V := bool) (fun_app_bexp_well_formed fenv_i funcs) dl),
        fenv_s = compile_fenv fenv_i ->
        eval_prop_rel (fun expr val =>
                         b_Dan expr dbenv fenv_i nenv val) dl ->
        eval_prop_rel (fun expr val =>
                         bexp_stack_sem expr fenv_s stk (stk', val))
                      sl ->
        prop_rel (fun expr => StackPurestBase.bexp_stack_pure_rel
                           expr fenv_s) sl.
Proof.
  intros.
  eapply bool_compile_prop_rel_implies_pure'; try eassumption; try eapply eq_refl.
Qed.




Lemma lp_bool_transrelation_implies_pure :
  forall (dl: LogicProp bool bexp_Dan) (sl: LogicProp bool bexp_stack) args map,
    lp_bool_transrelation args map dl sl ->
    forall fenv_i fenv_s dbenv nenv stk stk' funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      forall (FENV_WF: fenv_well_formed' funcs fenv_i),
      forall (FUN_APP: prop_rel (V := bool) (fun_app_bexp_well_formed fenv_i funcs) dl),
      fenv_s = compile_fenv fenv_i ->
      eval_prop_rel (fun boolexpr bval =>
                       b_Dan boolexpr dbenv fenv_i nenv bval) dl ->
      eval_prop_rel (fun boolexpr bval =>
                       bexp_stack_sem boolexpr fenv_s stk (stk', bval)) sl ->
      prop_rel (fun boolexpr => StackPurestBase.bexp_stack_pure_rel boolexpr fenv_s) sl.
Proof.
  intros. invs H.
  eapply bool_compile_prop_rel_implies_pure; try eassumption; try eapply eq_refl.
Qed.


Lemma logic_translation_preserves_pure :
  forall dan_prop args map stk_prop,
    lp_transrelation args map (Dan_lp_bool dan_prop) (MetaBool stk_prop) ->
    forall fenv_i fenv_s dbenv nenv stk stk' funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      forall (FENV_WF: fenv_well_formed' funcs fenv_i),
      forall (FUN_APP: prop_rel (V := bool) (fun_app_bexp_well_formed fenv_i funcs) dan_prop),
      fenv_s = compile_fenv fenv_i ->
      eval_prop_rel (fun boolexpr bval => b_Dan boolexpr dbenv fenv_i nenv bval) dan_prop ->
      eval_prop_rel (fun boolexpr bval => bexp_stack_sem boolexpr fenv_s stk (stk', bval)) stk_prop ->
      prop_rel (fun boolexpr => StackPurestBase.bexp_stack_pure_rel boolexpr fenv_s) stk_prop.
Proof.
  intros dan_prop args map stk_prop LP ifenv sfenv dbenv nenv stk stk' COMPILE B_DAN BEXP.
  inversion LP.
  eapply lp_bool_transrelation_implies_pure; eassumption.
Qed.

Lemma arith_compile_prop_args_rel_implies_pure' :
  forall (dl: list aexp_Dan) (sl: list aexp_stack) map,
    compile_prop_args_rel (comp_arith map) dl sl ->
    forall fenv_i fenv_s funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      forall (FENV_WF: fenv_well_formed' funcs fenv_i),
      forall (FUN_APP: prop_args_rel (V := nat) (fun_app_well_formed fenv_i funcs) dl),
      fenv_s = compile_fenv fenv_i ->
      prop_args_rel (V := nat) (fun expr =>
                  StackPurestBase.aexp_stack_pure_rel expr fenv_s)
               sl.
Proof.
  intros dl sl map COMP. dependent induction COMP; intros; unfold comp_arith in *; invs FUN_APP.
  - econstructor.
  - econstructor.
    eapply comp_aexp_implies_pure'; try eapply eq_refl; try eassumption.
    eapply IHCOMP; eauto.
Qed.

Lemma arith_compile_prop_rel_implies_pure' :
  forall (dl: LogicProp nat aexp_Dan) (sl: LogicProp nat aexp_stack) map,
    compile_prop_rel (comp_arith map) dl sl ->
    forall fenv_i fenv_s funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      forall (FENV_WF: fenv_well_formed' funcs fenv_i),
      forall (FUN_APP: prop_rel (V := nat) (fun_app_well_formed fenv_i funcs) dl),
      fenv_s = compile_fenv fenv_i ->
      prop_rel (fun expr =>
                  StackPurestBase.aexp_stack_pure_rel expr fenv_s)
               sl.
Proof.
  intros dl sl map COMP.
  dependent induction COMP; intros; try econstructor; unfold comp_arith;
    invs FUN_APP;
    try (eapply comp_aexp_implies_pure'; eauto);
    try solve [ eapply IHCOMP; try eapply eq_refl; try eassumption
              | eapply IHCOMP1; try eapply eq_refl; try eassumption
              | eapply IHCOMP2; try eapply eq_refl; try eassumption ];
    try reflexivity.
  eapply arith_compile_prop_args_rel_implies_pure'; eauto.
Qed.

Lemma arith_compile_prop_rel_implies_pure :
  forall (dl: LogicProp nat aexp_Dan) (sl: LogicProp nat aexp_stack) map,
    compile_prop_rel (comp_arith map) dl sl ->
    forall fenv_i fenv_s dbenv nenv stk stk' funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUN_APP: prop_rel (V := nat) (fun_app_well_formed fenv_i funcs) dl),
      fenv_s = compile_fenv fenv_i ->
      eval_prop_rel (fun expr val =>
                       a_Dan expr dbenv fenv_i nenv val) dl ->
      eval_prop_rel (fun expr val =>
                       aexp_stack_sem expr fenv_s stk (stk', val))
                    sl ->
      prop_rel (fun expr =>
                  StackPurestBase.aexp_stack_pure_rel expr fenv_s)
               sl.
Proof.
  intros. eapply arith_compile_prop_rel_implies_pure'; eassumption.
Qed.


Lemma lp_arith_translation_implies_pure :
  forall (dl: LogicProp nat aexp_Dan) (sl: LogicProp nat aexp_stack) args map,
    lp_arith_transrelation args map dl sl ->
    forall fenv_i fenv_s dbenv nenv stk stk' funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUN_APP: prop_rel (V := nat) (fun_app_well_formed fenv_i funcs) dl),
      fenv_s = compile_fenv fenv_i ->
      eval_prop_rel (fun expr val =>
                       a_Dan expr dbenv fenv_i nenv val) dl ->
      eval_prop_rel (fun expr val =>
                       aexp_stack_sem expr fenv_s stk (stk', val))
                    sl ->
      prop_rel (fun expr =>
                  StackPurestBase.aexp_stack_pure_rel expr fenv_s)
               sl.
Proof.
  intros dl sl args map COMP.
  intros ? ? ? ? ? ?.
  intros CFENV EVAL_DAN EVAL_STK.
  invs COMP.
  eapply arith_compile_prop_rel_implies_pure; eauto.
Qed.


Lemma arith_logic_translation_implies_pure :
  forall dan_prop args map stk_prop,
    lp_transrelation args map (Dan_lp_arith dan_prop) (MetaNat stk_prop) ->
    forall fenv_i fenv_s dbenv nenv stk stk' funcs,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    forall (FENV_WF: fenv_well_formed' funcs fenv_i),
    forall (FUN_APP: prop_rel (V := nat) (fun_app_well_formed fenv_i funcs) dan_prop),
      fenv_s = compile_fenv fenv_i ->
      eval_prop_rel (fun expr val =>
                       a_Dan expr dbenv fenv_i nenv val) dan_prop ->
      eval_prop_rel (fun expr val =>
                       aexp_stack_sem expr fenv_s stk (stk', val)) stk_prop ->
      prop_rel (fun expr =>
                  StackPurestBase.aexp_stack_pure_rel expr fenv_s)
               stk_prop.
Proof.
  intros ? ? ? ? LP.
  invs LP. intros ? ? ? ? ? ? FENV EVAL_DAN EVAL_STK.
  eapply lp_arith_translation_implies_pure; eauto.
Qed.



Lemma arith_compile_prop_args_rel_implies_pure :
  forall c (dl: list aexp_Dan) (sl: list aexp_stack),
    compile_prop_args_rel c dl sl ->
    forall (map: list ident),
      c = comp_arith map ->
      forall fenv_i fenv_s dbenv nenv stk stk' dvals svals funcs,
      forall (OKfuncs: funcs_okay_too funcs fenv_s),
      forall (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      forall (FENV_WF: fenv_well_formed' funcs fenv_i),
      forall (FUN_APP: prop_args_rel (V := nat) (fun_app_well_formed fenv_i funcs) dl),
        
        fenv_s = compile_fenv fenv_i ->
        eval_prop_args_rel (fun expr val =>
                              a_Dan expr dbenv fenv_i nenv val) dl dvals ->
        eval_prop_args_rel (fun expr val =>
                              aexp_stack_sem expr fenv_s stk (stk', val))
                           sl svals ->
        prop_args_rel (V := nat) (fun expr => StackPurestBase.aexp_stack_pure_rel
                                           expr fenv_s) sl.
Proof.
  intros c dl sl. induction 1; intros; inversion FUN_APP.
  - invs H2. constructor.
  - inversion H2. constructor. inversion H.
    + unfold comp_arith in H0. remember (phi arg) as arg'. rewrite H0 in Heqarg'. inversion H3.
      eapply comp_aexp_implies_pure; eassumption.
    + remember (phi arg) as arg'. rewrite H0 in Heqarg'. unfold comp_arith in Heqarg'. inversion H3. eapply comp_aexp_implies_pure; eassumption.
    + inversion H3. eapply IHcompile_prop_args_rel; eassumption.
Qed.
