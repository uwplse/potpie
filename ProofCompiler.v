From Coq Require Import String List Peano Arith Program.Equality.
From DanTrick Require Import StackLogic DanLogHoare DanTrickLanguage EnvToStack StackLanguage DanLogProp LogicProp StackLangTheorems StackLogicBase.
From DanTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From DanTrick Require Export ProofSubstitution ImpVarMapTheorems DanLogSubstAdequate.
From DanTrick Require Import DanImpHigherOrderRel ProofCompilerHelpers DanHoareWF.
From DanTrick Require Import ProofCompilerBase DanImpHigherOrderRelTheorems.
From DanTrick Require Import FunctionWellFormed CompilerAssumptionLogicTrans.
From DanTrick Require Import DanLogicHelpers.

(*
 * This is the file for the proof compiler, which compiles
 * proofs in DanTrickLogic to proofs in StackLogic.
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.


(*
 * This module includes test programs and proofs to test
 * the behavior of the proof compiler.
 *)
Module Tests.

(*
 * Source programs and proofs.
 *)
Module Source.

(* The max function, defined in another file *)
  Definition max : fun_Dan := max_fun.
  Check max.
  Compute max.

  (* A more concise version for simplicity *)
  Local Open Scope bool_scope.
  Definition maxSmall : fun_Dan :=
    {|
      DanTrickLanguage.Name := "maxSmall";
      DanTrickLanguage.Args := 2;
      Ret := "z";
      DanTrickLanguage.Body :=
        (IF_Dan
           (AND_Dan (LEQ_Dan (PARAM_Dan 1) (PARAM_Dan 0))
                    (NEG_Dan
                       (AND_Dan (LEQ_Dan (PARAM_Dan 1) (PARAM_Dan 0))
                                (LEQ_Dan (PARAM_Dan 0) (PARAM_Dan 1)))))
           (ASSIGN_Dan "z" (PARAM_Dan 0))
           (ASSIGN_Dan "z" (PARAM_Dan 1)))
    |}.

  Definition bexp_conditional :=
     (AND_Dan (LEQ_Dan (PARAM_Dan 1) (PARAM_Dan 0))
                    (NEG_Dan
                       (AND_Dan (LEQ_Dan (PARAM_Dan 1) (PARAM_Dan 0))
                                (LEQ_Dan (PARAM_Dan 0) (PARAM_Dan 1))))).

  Definition true_bool (b: bexp_Dan) : AbsEnv :=
    AbsEnvLP (Dan_lp_bool (UnaryProp _ _ (fun v => v = true) b)).

  Definition false_bool (b: bexp_Dan) : AbsEnv :=
    AbsEnvLP (Dan_lp_bool (UnaryProp _ _ (fun v => v = false) b)).

  Definition dan_log_true : AbsEnv :=
    AbsEnvLP (Dan_lp_arith (TrueProp _ _ )).
  Definition my_geq (a1 a2: aexp_Dan): AbsEnv :=
    AbsEnvLP (Dan_lp_arith (BinaryProp _ _ (fun a b => a >= b)
                                         a1
                                         a2)).
  Definition max_conclusion : AbsEnv :=
    AbsEnvAnd (true_bool (geq_Dan (VAR_Dan "z") (PARAM_Dan 0)))
                (true_bool (geq_Dan (VAR_Dan "z") (PARAM_Dan 1))).
 
  
  Definition param0gtparam1 : AbsEnv :=
    true_bool (gt_Dan (PARAM_Dan 0) (PARAM_Dan 1)).

  Definition notparam0gtparam1 : AbsEnv :=
    false_bool (gt_Dan (PARAM_Dan 0) (PARAM_Dan 1)).

  Definition param0geqparam0 : AbsEnv :=
    true_bool (geq_Dan (PARAM_Dan 0) (PARAM_Dan 0)).

  Definition param0geqparam1 : AbsEnv :=
    true_bool (geq_Dan (PARAM_Dan 0) (PARAM_Dan 1)).

  Definition param1geqparam0 : AbsEnv :=
    true_bool (geq_Dan (PARAM_Dan 1) (PARAM_Dan 0)).
  Definition param1geqparam1 : AbsEnv :=
    true_bool (geq_Dan (PARAM_Dan 1) (PARAM_Dan 1)).



  Ltac dan_log_inversion :=
    match goal with
    | [ H: AbsEnv_rel (AbsEnvAnd ?inner1 ?inner2) ?fenv ?dbenv ?nenv |- _ ] =>
        invc H;
        dan_log_inversion
    | [ H: AbsEnv_rel (AbsEnvOr ?inner1 ?inner2) _ _ _ |- _ ] =>
        invc H; try dan_log_inversion
    | [ H: AbsEnv_rel (AbsEnvLP ?lp) _ _ _ |- _ ] =>
        invc H; try dan_log_inversion
    | [ H: Dan_lp_rel (Dan_lp_arith ?lp) _ _ _ |- _ ] =>
        invc H; try dan_log_inversion
    | [ H: Dan_lp_rel (Dan_lp_bool ?lp) _ _ _ |- _ ] =>
        invc H; try dan_log_inversion
    | [ H: eval_prop_rel _ _ |- _ ] =>
        invc H; try dan_log_inversion
    | [ H: b_Dan ?b _ _ _ _ |- _ ] =>
        match b with
        | AND_Dan _ _ =>
            invc H; try dan_log_inversion
        | OR_Dan _ _ =>
            invc H; try dan_log_inversion
        | LEQ_Dan _ _ =>
            invc H; try dan_log_inversion
        | NEG_Dan _ =>
            invc H; try dan_log_inversion
        | geq_Dan _ _ =>
            invc H; try dan_log_inversion
        | gt_Dan _ _ =>
            unfold gt_Dan in H; invc H; try dan_log_inversion
        | lt_Dan _ _ =>
            unfold lt_Dan in H; invc H; try dan_log_inversion
        | eq_Dan _ _ =>
            unfold eq_Dan in H; invc H; try dan_log_inversion
        | neq_Dan _ _ =>
            unfold neq_Dan in H; invc H; try dan_log_inversion
        | _ =>
            idtac
        end
    | [ H: a_Dan ?a _ _ _ _ |- _ ] =>
        match a with
        | PLUS_Dan _ _ =>
            invc H; try dan_log_inversion
        | MINUS_Dan _ _ =>
            invc H; try dan_log_inversion
        | VAR_Dan _ =>
            invc H; try dan_log_inversion
        | _ =>
            idtac
        end
    end.

  Ltac dan_log_constructor :=
    match goal with
    | [ |- AbsEnv_rel _ _ _ _ ] =>
        econstructor; try dan_log_constructor
    | [ |- Dan_lp_rel _ _ _ _ ] =>
        econstructor; try dan_log_constructor
    | [ |- eval_prop_rel _ _ ] =>
        econstructor; try dan_log_constructor
    | [ |- b_Dan ?b _ _ _ _ ] =>
        match b with
        | AND_Dan _ _ =>
            econstructor; try dan_log_constructor
        | OR_Dan _ _ =>
            econstructor; try dan_log_constructor
        | LEQ_Dan _ _ =>
            econstructor; try dan_log_constructor
        | NEG_Dan _ =>
            econstructor; try dan_log_constructor
        | geq_Dan _ _ =>
            unfold geq_Dan; try dan_log_constructor
        | _ =>
            try eassumption
        end
    | [ |- a_Dan ?a _ _ _ _ ] =>
        match a with
        | PLUS_Dan _ _ =>
            econstructor; try dan_log_constructor
        | MINUS_Dan _ _ =>
            econstructor; try dan_log_constructor
        | VAR_Dan _ =>
            econstructor; try dan_log_constructor
        | _ =>
            try eassumption
        end
    end.

  
  Lemma aimpDanPP' fenv :
    aimpDan (AbsEnvAnd dan_log_true param0gtparam1)
            (AbsEnvAnd param0geqparam0 param0geqparam1) fenv.
  Proof.
    unfold aimpDan, param0gtparam1, param0geqparam0, param0geqparam1.
    intros.
    unfold true_bool in *. unfold dan_log_true in *.
    dan_log_inversion; a_Dan_elim.
    
    econstructor.
    - econstructor. econstructor.
      econstructor.
      econstructor. eassumption. eassumption.
      rewrite H1.
      apply Nat.leb_le. auto.
    - dan_log_constructor.
      rewrite H1.
      symmetry in H1.
      eapply Bool.andb_true_eq in H1.
      destruct H1.
      rewrite Bool.negb_andb in H0.
      rewrite H. reflexivity.
  Qed.

  Lemma aimpDanQQ' fenv :
    aimpDan max_conclusion max_conclusion fenv.
  Proof.
    unfold aimpDan.
    intros. assumption.
  Defined.
  

  Lemma secondaimpDanP'P fenv :
    aimpDan (AbsEnvAnd dan_log_true
                              notparam0gtparam1)
            (AbsEnvAnd param1geqparam0
                         param1geqparam1) fenv.
  Proof.
    unfold aimpDan, dan_log_true, notparam0gtparam1, param1geqparam0, param1geqparam1.
    intros.
    unfold false_bool in *. unfold true_bool in *.
    dan_log_inversion.
    a_Dan_elim.
    
    rewrite Bool.andb_false_iff in H1.
    destruct H1.
    - eapply Nat.leb_gt in H.
      dan_log_constructor.
      eapply Nat.leb_le. intuition.
      eapply Nat.leb_le. auto.
    - eapply Bool.negb_false_iff in H.
      symmetry in H.
      eapply Bool.andb_true_eq in H.
      destruct H.
      dan_log_constructor.
      symmetry in H0. assumption.
      eapply Nat.leb_le. auto.
  Defined.
  
  
  Definition maxSmallProof :=
    hl_Dan_if dan_log_true
              max_conclusion
              (gt_Dan (PARAM_Dan 0) (PARAM_Dan 1))
              (ASSIGN_Dan "z" (PARAM_Dan 0))
              (ASSIGN_Dan "z" (PARAM_Dan 1))
              init_fenv
              (hl_Dan_consequence
                 (AbsEnvAnd param0geqparam0 param0geqparam1)
                 max_conclusion
                 (AbsEnvAnd dan_log_true param0gtparam1)
                 max_conclusion
                 (ASSIGN_Dan "z" (PARAM_Dan 0))
                 init_fenv
                 (hl_Dan_assign
                    max_conclusion
                    init_fenv
                    "z"
                    (PARAM_Dan 0))
                 (aimpDanPP' init_fenv)
                 (aimpDanQQ' init_fenv))
              (hl_Dan_consequence
                 (AbsEnvAnd param1geqparam0
                              param1geqparam1)
                 max_conclusion
                 (AbsEnvAnd dan_log_true
                              notparam0gtparam1)
                 max_conclusion
                 (ASSIGN_Dan "z" (PARAM_Dan 1))
                 init_fenv
                 (hl_Dan_assign
                    max_conclusion
                    init_fenv
                    "z"
                    (PARAM_Dan 1))
                 (secondaimpDanP'P init_fenv)
                 (aimpDanQQ' init_fenv)).
  
    
  Lemma maxSmallLemma :
    forall fenv,
      hl_Dan dan_log_true (DanTrickLanguage.Body maxSmall) max_conclusion fenv.
  Proof.
    unfold maxSmall.
    simpl.
    intros.
    unfold dan_log_true, max_conclusion.
    eapply hl_Dan_if.
    - eapply hl_Dan_consequence.
      + assert (hl_Dan (AbsEnvAnd param0geqparam0 param0geqparam1)
                       (ASSIGN_Dan "z" (PARAM_Dan 0))
                       max_conclusion
                       fenv).
        * unfold param0geqparam0.
          unfold param0geqparam1.
          unfold true_bool.
          unfold max_conclusion.
          unfold true_bool.
          assert (DanLogSubst.subst_AbsEnv "z" (PARAM_Dan 0) (AbsEnvAnd
       (AbsEnvLP
          (Dan_lp_bool
             (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                (VAR_Dan "z" >=d PARAM_Dan 0))))
       (AbsEnvLP
          (Dan_lp_bool
             (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                (VAR_Dan "z" >=d PARAM_Dan 1))))) = (AbsEnvAnd
       (AbsEnvLP
          (Dan_lp_bool
             (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                (PARAM_Dan 0 >=d PARAM_Dan 0))))
       (AbsEnvLP
          (Dan_lp_bool
             (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                        (PARAM_Dan 0 >=d PARAM_Dan 1)))))).
          {
            simpl. unfold geq_Dan. reflexivity.
          }
          rewrite <- H.
          eapply hl_Dan_assign.
        * eassumption.
      + unfold atrueDan. unfold aimpDan.
        unfold param0geqparam0, param0geqparam1.
        unfold true_bool. intros.
        dan_log_inversion.
        a_Dan_elim.
        dan_log_constructor; rewrite H1.
        * eapply Nat.leb_le. auto.
        * symmetry in H1. eapply Bool.andb_true_eq in H1.
          destruct H1. symmetry in H. assumption.
      + apply aimpDanQQ'.
    - eapply hl_Dan_consequence.
      + assert (hl_Dan (DanLogSubst.subst_AbsEnv "z" (PARAM_Dan 1) max_conclusion) (ASSIGN_Dan "z" (PARAM_Dan 1)) max_conclusion fenv).
        {
          unfold max_conclusion. unfold true_bool.
          econstructor.
        }
        eassumption.
      + 
        apply secondaimpDanP'P.
      + apply aimpDanQQ'.
  Defined.


End Source.

(*
 * Target programs and proofs.
 *)
Module Target.
  Definition maxSmallCompiled : compiled_function := pre_compile_function_proof_amenable (Source.maxSmall).


  Definition maxSmallFun : StackLanguage.fun_stk := compiled_function_to_fun_stk maxSmallCompiled.
  Compute maxSmallFun.

  (* The max function in the target language *)
  Definition max : StackLanguage.fun_stk :=
    {|
      Name := "max";
      Args := 2;
      Body :=
      Seq_Stk 
        Push_Stk
        (Seq_Stk 
           Push_Stk
           (Seq_Stk
              Push_Stk
              (Seq_Stk
                 (Seq_Stk
                    (Assign_Stk 3 (Var_Stk 4))
                    (Assign_Stk 2 (Var_Stk 5)))
                 (If_Stk
                    (And_Stk
                       (Leq_Stk (Var_Stk 2) (Var_Stk 3))
                       (Neg_Stk
                          (And_Stk
                             (Leq_Stk (Var_Stk 2) (Var_Stk 3))
                             (Leq_Stk (Var_Stk 3) (Var_Stk 2)))))
                    (Assign_Stk 1 (Var_Stk 3))
                    (Assign_Stk 1 (Var_Stk 2))))));
      Return_expr := Var_Stk 1;
      Return_pop := 3
    |}.


  (* A more concise version for simplicity *)
  Definition maxSmall : StackLanguage.fun_stk := 
    {|
      Name := "maxSmall";
      Args := 2;
      Body :=
      Seq_Stk
        Push_Stk
        (If_Stk
           (And_Stk 
              (Leq_Stk (Var_Stk 3) (Var_Stk 2))
              (Neg_Stk
                 (And_Stk
                    (Leq_Stk (Var_Stk 3) (Var_Stk 2))
                    (Leq_Stk (Var_Stk 2) (Var_Stk 3)))))
           (Assign_Stk 1 (Var_Stk 2)) 
           (Assign_Stk 1 (Var_Stk 3)));
      Return_expr := Var_Stk 1;
      Return_pop := 1
    |}.

  Example maxSmallSame :
    maxSmall = maxSmallFun.
  Proof.
    reflexivity.
  Qed.

  
End Target.



Ltac rename_fresh_until_no_match :=
  match goal with
  | [ H: AbsEnv_prop_rel (var_map_wf_wrt_aexp ?map) (var_map_wf_wrt_bexp ?map) ?d |- _ ] =>
      let HWF := fresh "WF" in
      pose proof (HWF := H); clear H; revert HWF; rename_fresh_until_no_match
  | _ => intros
  end.

Program Definition hl_compile_skip (P : AbsEnv)
  (fenv : fun_env)
  (map : list DanTrickLanguage.ident)
  (func_list: list fun_Dan)
  (args : nat)
  (AIMPWF : aimp_always_wf func_list map args P SKIP_Dan P fenv (hl_Dan_skip P fenv))
  (s2 s1 : AbsState)
  (fenv0 : fun_env_stk)
  (i' : imp_stack)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map P s2)
  (H1 : i' = comp_code SKIP_Dan map args)
  (H2 : fenv0 = compile_fenv fenv)
  (H3 H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (IMPWF : imp_rec_rel (var_map_wf_wrt_imp map) SKIP_Dan):
  hl_stk s1 i' s2 fenv0.
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
  eapply logic_transrelation_deterministic in H; [ | eassumption ].
  rewrite H. simpl. constructor.
Defined.


(*
 * Talia: To eventually decouple the essence of proof compilation from its
 * correctness proof, I'm looking at some proof terms and trying to tease
 * apart the details of what is happening and document it. In doing so,
 * I'll probably simplify the terms a bit.
 *)


Definition hl_compile_skip_term_minimized 
  (P : AbsEnv)
  (fenv : fun_env)
  (map : list DanTrickLanguage.ident)
  (s2 s1 : AbsState)
  (args : nat)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map P s2)
  : hl_stk s1 (comp_code SKIP_Dan map args) s2 (compile_fenv fenv)
:=
  let fenv0 := compile_fenv fenv in (* compile the fun_env *)
  let prog := comp_code SKIP_Dan map args in (* compile the program *)
  let proof := hl_stk_skip s1 fenv0 in (* compose the compiled proof *)  
  eq_rect_r (* rewrite by proof of determinism of logic compilation to get correctness proof of proof *)
    (fun s3 : AbsState => hl_stk s1 prog s3 fenv0)
    proof
    (logic_transrelation_deterministic args map P s2 s1 H0 H).

Eval compute in (fun map args => comp_code SKIP_Dan map args).
Eval compute in (fun map => compile_imp SKIP_Dan (ident_list_to_map map) (Datatypes.length map)).

(*
 * This computes the logic translation instead of using the inductive relation.
 * Does this behave the same way? It's suspiciously simple.
 *)
Definition hl_compile_skip_term_minimized_alt
  (P : AbsEnv)
  (fenv : fun_env)
  (map : list DanTrickLanguage.ident)
  (args : nat)
  : hl_stk (comp_logic args map P) (comp_code SKIP_Dan map args) (comp_logic args map P) (compile_fenv fenv)
:=
  hl_stk_skip (comp_logic args map P) (compile_fenv fenv).


Program Definition hl_compile_assign (P : AbsEnv)
  (fenv : fun_env)
  (x : string)
  (a : aexp_Dan)
  (funcs: list fun_Dan)
  (map : list DanTrickLanguage.ident)
  (args : nat)
  (AIMPWF : aimp_always_wf funcs map args (DanLogSubst.subst_AbsEnv x a P) (x <- a) P fenv (hl_Dan_assign P fenv x a))
  (fenv0 : fun_env_stk)
  (s2 s1 : AbsState)
  (i' : imp_stack)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (x <- a))
  (OKfuncs: funcs_okay_too funcs fenv0)
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (H : logic_transrelation args map (DanLogSubst.subst_AbsEnv x a P) s1)
  (H0 : logic_transrelation args map P s2)
  (H1 : i' = comp_code (x <- a) map args)
  (H2 : fenv0 = compile_fenv fenv)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (DanLogSubst.subst_AbsEnv x a P))
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (x <- a)) :
  hl_stk s1 i' s2 fenv0.
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
  pose proof (H' := H).
    eapply logic_transrelation_substitution in H0.
    + simpl.
      econstructor.
      * invs_aimpwf_helper AIMPWF.
        remember_all.
        pose proof (rcomp_aexp_args_implies_pure) as PURE.
        unfold rcompile_aexp_args_mut_ind_theorem, TranslationPure.rcomp_pure_P', TranslationPure.rcomp_pure_P0' in PURE.
        destruct PURE as (AEXP & _).
        inversion FUN_APP.
        subst fenv0 wf_funcs x0 a0.
        eapply compile_aexp_args_adequate_backwards' in HeqARG0.
        eapply AEXP; try eassumption.
        eassumption.
      * eapply H0.
    + eapply H.
    + eapply dan_log_subst_adequacy; ereflexivity.
    + smart_unfold_wf_imp_in IMPWF.
      eapply WF''.
      econstructor.
      eapply String.eqb_eq; reflexivity.
    + smart_unfold_wf_imp_in IMPWF.
      invs WF'.
      assumption.
    + assumption.
    + ereflexivity.
    + ereflexivity.
    + ereflexivity.
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

Lemma rcomp_aexp_implies_pure :
  forall (map : list ident) (adan : aexp_Dan) (astk : aexp_stack) (funcs: list fun_Dan),
    rcompile_aexp map adan astk ->
    forall (fenv_i : DanTrickLanguage.ident -> fun_Dan)
      (OKfuncs: funcs_okay_too funcs (compile_fenv fenv_i))
      (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      fenv_well_formed' funcs fenv_i ->
      fun_app_well_formed fenv_i funcs adan ->
      StackPurestBase.aexp_stack_pure_rel astk (compile_fenv fenv_i).
Proof.
  destruct rcomp_aexp_args_implies_pure as (AEXP & _).
  unfold TranslationPure.rcomp_pure_P' in AEXP.
  intros. apply AEXP with (map := map) (adan := adan) (fenv_i := fenv_i) (funcs := funcs); eauto.
Defined.

Lemma imp_rec_rel_assign :
  forall (map: list ident) (x: ident) (a: aexp_Dan),
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

Lemma dan_log_subst_adequacy_simple :
  forall x a P,
    DanLogSubst.subst_AbsEnv_rel x a P (DanLogSubst.subst_AbsEnv x a P).
Proof.
  intros. apply dan_log_subst_adequacy.
  reflexivity.
Defined.

Lemma invs_fun_app_imp_well_formed_assign :
  forall fenv funcs x a,
    fun_app_imp_well_formed fenv funcs (x <- a) ->
    fun_app_well_formed fenv funcs a.
Proof.
  intros. invs H. assumption.
Defined.
  
Program Definition hl_compile_assign_small (P : AbsEnv)
  (fenv : fun_env)
  (x : string)
  (a : aexp_Dan)
  (map : list DanTrickLanguage.ident)
  (funcs: list fun_Dan)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (x <- a))
  (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (s2 s1 : AbsState)
  (args : nat)
  (H1 : logic_transrelation args map (DanLogSubst.subst_AbsEnv x a P) s1)
  (H2 : logic_transrelation args map P s2)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (DanLogSubst.subst_AbsEnv x a P))
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (x <- a)) :
  hl_stk s1 (comp_code (x <- a) map args) s2 (compile_fenv fenv).
Proof.
  constructor.
  - apply rcomp_aexp_implies_pure with (fenv_i := fenv) (map := map) (adan := a) (funcs := funcs).
    + apply (compile_aexp_args_adequate_backwards' map args).
      reflexivity.
    + assumption.
    + eapply inv_fun_app_imp_assign in FUN_APP. assumption.
    + eassumption.
    + eapply invs_fun_app_imp_well_formed_assign. eassumption.
  - apply imp_rec_rel_assign in H5. apply var_map_wf_wrt_imp_assign in H5.
    apply log_comp_adequacy_forward in H1. apply log_comp_adequacy_forward  in H2. rewrite <- H1. rewrite <- H2. 
    apply
      (logic_transrelation_substitution
         args map P
         (DanLogSubst.subst_AbsEnv x a P)
         (comp_logic args map
                     (DanLogSubst.subst_AbsEnv x a P))
         (comp_logic args map P)
         x a (ident_list_to_map map x)
         (compile_aexp a (ident_list_to_map map)
                       (Datatypes.length map))
         (ident_list_to_map map)).
    + apply log_comp_adequacy_backwards. reflexivity.
    + apply dan_log_subst_adequacy_simple.
    + apply (proj2 H5).
      constructor.
      apply (proj2 (String.eqb_eq _ _)). reflexivity.
    + apply proj1 in H5.
      apply inv_imp_forall_assign in H5.
      assumption.
    + assumption.
    + reflexivity.
    + reflexivity.
    + apply log_comp_adequacy_backwards. reflexivity.
    + reflexivity.
Defined.


Program Definition hl_compile_seq  (P Q R : AbsEnv)
  (i1 i2 : imp_Dan)
  (fenv : fun_env)
  (hl1 : hl_Dan P i1 R fenv)
  (hl2 : hl_Dan R i2 Q fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl1 : forall (map : list DanTrickLanguage.ident),
      fun_app_imp_well_formed fenv funcs i1 ->
      aimp_always_wf funcs map args P i1 R fenv hl1 ->
      forall (fenv0 : fun_env_stk) (s2 : AbsState) (i' : imp_stack) (s1 : AbsState),
        logic_transrelation args map P s1 ->
        logic_transrelation args map R s2 ->
        i' = compile_imp i1 (ident_list_to_map map) (Datatypes.length map) ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) R ->
        imp_rec_rel (var_map_wf_wrt_imp map) i1 -> hl_stk s1 i' s2 fenv0)
  (IHhl2 : forall (map : list DanTrickLanguage.ident),
      fun_app_imp_well_formed fenv funcs i2 ->
      aimp_always_wf funcs map args R i2 Q fenv hl2 ->
      forall (fenv0 : fun_env_stk) (s2 : AbsState) (i' : imp_stack) (s1 : AbsState),
        logic_transrelation args map R s1 ->
        logic_transrelation args map Q s2 ->
        i' = compile_imp i2 (ident_list_to_map map) (Datatypes.length map) ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) R ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) i2 -> hl_stk s1 i' s2 fenv0)
  (map : list DanTrickLanguage.ident)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (i1 ;; i2))
  (AIMPWF : aimp_always_wf funcs map args P (i1;; i2) Q fenv (hl_Dan_seq P Q R i1 i2 fenv hl1 hl2))
  (fenv0 : fun_env_stk)
  (s2 s1 : AbsState)
  (i' : imp_stack)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map Q s2)
  (H1 : i' = comp_code (i1;; i2) map args)
  (H2 : fenv0 = compile_fenv fenv)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q)
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (i1;; i2)) :
  hl_stk s1 i' s2 fenv0.
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
  simpl. econstructor.
  + eapply IHhl1; try eassumption; try ereflexivity.
    * invs FUN_APP; assumption.
    * invs_aimpwf_helper AIMPWF.
      eassumption.
    * assert (logic_transrelation args map R (comp_logic args map R)) by (eapply log_comp_adequacy; ereflexivity).
      eassumption.
      
    * invs_aimpwf_helper AIMPWF.
      assumption.
    * invs IMPWF.
      eassumption.
  + eapply IHhl2.
    invs FUN_APP. assumption.
    invs_aimpwf_helper AIMPWF. 
    eassumption.
    eapply log_comp_adequacy.
    ereflexivity.
    assumption.
    all: try reflexivity.
    invs_aimpwf_helper AIMPWF.
    assumption.
    assumption.
    invs IMPWF. eassumption.
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
  forall b i1 i2 P Q funcs map args fenv hl1 hl2,
    aimp_always_wf funcs map args P (when b then i1 else i2 done) Q fenv
                   (hl_Dan_if P Q b i1 i2 fenv hl1 hl2) ->
    aimp_always_wf funcs map args (afalseDan b P) i2 Q fenv hl2 /\
      aimp_always_wf funcs map args (atrueDan b P) i1 Q fenv hl1.
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
Qed.

Lemma inv_imp_rec_rel_seq :
  forall map i1 i2,
    imp_rec_rel (var_map_wf_wrt_imp map) (i1;; i2) ->
    imp_rec_rel (var_map_wf_wrt_imp map) i1 /\
      imp_rec_rel (var_map_wf_wrt_imp map) i2 /\
      var_map_wf_wrt_imp map (i1;; i2).
Proof.
  intros. inversion H. unfold DanImpHigherOrderRel.phi_t in phi. subst.
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
  

Program Definition hl_compile_seq_smaller  (P Q R : AbsEnv)
  (i1 i2 : imp_Dan)
  (fenv : fun_env)
  (hl1 : hl_Dan P i1 R fenv)
  (hl2 : hl_Dan R i2 Q fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl1 : forall (map : list DanTrickLanguage.ident),
      fun_app_imp_well_formed fenv funcs i1 ->
      aimp_always_wf funcs map args P i1 R fenv hl1 ->
      forall (s2 : AbsState) (s1 : AbsState),
        logic_transrelation args map P s1 ->
        logic_transrelation args map R s2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) R ->
        imp_rec_rel (var_map_wf_wrt_imp map) i1 ->
        hl_stk s1 (compile_imp i1 (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv))
  (IHhl2 : forall (map : list DanTrickLanguage.ident),
      fun_app_imp_well_formed fenv funcs i2 ->
      aimp_always_wf funcs map args R i2 Q fenv hl2 ->
      forall (s2 : AbsState) (s1 : AbsState),
        logic_transrelation args map R s1 ->
        logic_transrelation args map Q s2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) R ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) i2 ->
        hl_stk s1 (compile_imp i2 (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv))
  (map : list DanTrickLanguage.ident)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (i1 ;; i2))
  (AIMPWF : aimp_always_wf funcs map args P (i1;; i2) Q fenv (hl_Dan_seq P Q R i1 i2 fenv hl1 hl2))
  (s2 s1 : AbsState)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map Q s2)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q)
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (i1;; i2)) :
  hl_stk s1 (compile_imp (i1;; i2) (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv).
Proof.
  simpl. pose proof (inv_aimpwf_seq i1 i2 P Q R funcs map args fenv hl1 hl2 AIMPWF) as INV.
  apply inv_fun_app_imp_seq in FUN_APP.
  destruct FUN_APP as (FUN_APP1 & FUN_APP2).
  apply inv_imp_rec_rel_seq in H5.
  destruct H5 as (? & ? & ?).
  destruct INV as [AIMPWF1 [AIMPWF2 DLWF]].  econstructor.
  + eapply IHhl1; try eassumption; try ereflexivity.
    * apply log_comp_adequacy_backwards.
      eauto.
  + apply IHhl2 with (map := map).
    * assumption.
    * apply AIMPWF2.
    * apply log_comp_adequacy_backwards. reflexivity.
    * apply H0.
    * apply DLWF.
    * apply H4.
    * apply H2.
Defined.

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
  (b : bexp_Dan)
  (i1 i2 : imp_Dan)
  (fenv : fun_env)
  (hl1 : hl_Dan (atrueDan b P) i1 Q fenv)
  (hl2 : hl_Dan (afalseDan b P) i2 Q fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl1 : forall (map : list DanTrickLanguage.ident),
      fun_app_imp_well_formed fenv funcs i2 ->
      aimp_always_wf funcs map args (atrueDan b P) i1 Q fenv hl1 ->
      forall (fenv0 : fun_env_stk) (s2 : AbsState) (i' : imp_stack) (s1 : AbsState),
        logic_transrelation args map (atrueDan b P) s1 ->
        logic_transrelation args map Q s2 ->
        i' = compile_imp i1 (ident_list_to_map map) (Datatypes.length map) ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (atrueDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) i1 -> hl_stk s1 i' s2 fenv0)
  (IHhl2 : forall (map : list DanTrickLanguage.ident),
      fun_app_imp_well_formed fenv funcs i2 ->
      aimp_always_wf funcs map args (afalseDan b P) i2 Q fenv hl2 ->
      forall (fenv0 : fun_env_stk) (s2 : AbsState) (i' : imp_stack) (s1 : AbsState),
        logic_transrelation args map (afalseDan b P) s1 ->
        logic_transrelation args map Q s2 ->
        i' = compile_imp i2 (ident_list_to_map map) (Datatypes.length map) ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (afalseDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) i2 -> hl_stk s1 i' s2 fenv0)
  (map : list DanTrickLanguage.ident)
  
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (when b then i1 else i2 done))
  (AIMPWF : aimp_always_wf funcs map args P (when b then i1 else i2 done) Q fenv (hl_Dan_if P Q b i1 i2 fenv hl1 hl2))
  (SALVATION: terminator fenv args (atrueDan b P) Q i1 hl1)
  (DARKFATE: terminator fenv args (afalseDan b P) Q i2 hl2)
  (fenv0 : fun_env_stk)
  (OKfuncs: funcs_okay_too funcs fenv0)
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (s2 s1 : AbsState)
  (i': imp_stack)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map Q s2)
  (H1 : i' = comp_code (when b then i1 else i2 done) map args)
  (H2 : fenv0 = compile_fenv fenv)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q)
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (when b then i1 else i2 done)):
  hl_stk s1 i' s2 fenv0.
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
    pose proof (HL1 := fun d1 d2 i fenv hl func_list => hl_Dan_implication d1 d2 i fenv hl func_list args).
    pose proof (HL2 := HL1).
    specialize (HL1 (atrueDan b P) Q i1 fenv).
  specialize (HL2 (afalseDan b P) Q i2 fenv).
  apply inv_imp_rec_rel_if in IMPWF.
  apply inv_fun_app_imp_if in FUN_APP.
  destruct FUN_APP as (FUN_B & FUN_I1 & FUN_I2).
  destruct IMPWF as (IMPWF1 & IMPWF2 & IMPWF).
  econstructor.
  
  eapply comp_bexp_implies_pure'; try ereflexivity; try eassumption.
    + eapply hl_stk_consequence.
      * eapply HL1; try eassumption.
        -- invs_aimpwf_helper AIMPWF.
           unfold aimp_always_wf. eassumption.
        -- unfold comp_code. reflexivity.
        -- reflexivity.
        -- eapply log_comp_adequacy. ereflexivity.
        -- econstructor.
           assumption.
           econstructor.
           econstructor.
           econstructor.
           
           unfold_wf_imp_in IMPWF.
           invs WF'. 
           assumption.
      * unfold atrueDan. simpl. unfold atruestk.
        assert (comp_logic args map P = s1).
        eapply log_comp_adequacy; eassumption.
        rewrite H1.
        remember_all.
        rewrite Nat.add_comm in HeqARG0.
        subst.
        unfold ident_list_to_map.
        unfold comp_bool.
        eapply hl_dan_implication_helper'; try eassumption.
        reflexivity.
      * unfold aimpstk; intros.
        assumption.
    + eapply hl_stk_consequence.
      * eapply HL2; try eassumption.
        -- invs_aimpwf_helper AIMPWF. eassumption.
        -- unfold comp_code. reflexivity.
        -- reflexivity.
        -- log_comp_adequate.
        -- econstructor.
           assumption.
           econstructor. econstructor. econstructor.
           unfold_wf_imp_in IMPWF. invs WF'. eassumption.
      * unfold afalsestk, afalseDan, ident_list_to_map.
        simpl. remember_all. unfold comp_bool in HeqARG0.
        rewrite Nat.add_comm in HeqARG0.
        subst.
        eapply hl_dan_implication_helper'.
        log_comp_adequate.
        unfold ident_list_to_map.
        assert (comp_logic args map P = s1) by log_comp_adequate.
        rewrite H1. reflexivity.
      * eapply self_implication.
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

Program Definition hl_compile_if_then_smaller (P Q : AbsEnv)
        (b : bexp_Dan)
        (i1 : imp_Dan)
        (fenv : fun_env)
        (hl1 : hl_Dan (atrueDan b P) i1 Q fenv)
        (funcs: list fun_Dan)
        (args : nat)
        (IHhl1 : forall (map : list DanTrickLanguage.ident),
          forall (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
            (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
            fun_app_imp_well_formed fenv funcs i1 ->
            aimp_always_wf funcs map args (atrueDan b P) i1 Q fenv hl1 ->
            forall (s2 s1 : AbsState),
              logic_transrelation args map (atrueDan b P) s1 ->
              logic_transrelation args map Q s2 ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) (atrueDan b P) ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) Q ->
              imp_rec_rel (var_map_wf_wrt_imp map) i1 ->
              hl_stk s1
                     (compile_imp i1 (ident_list_to_map map) (Datatypes.length map))
                     s2 (compile_fenv fenv))
        (map : list DanTrickLanguage.ident)
        (FENV_WF : fenv_well_formed' funcs fenv)
        (FUN_APP : fun_app_imp_well_formed fenv funcs i1)
        (FUN_APP_B : fun_app_bexp_well_formed fenv funcs b)
        (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
        (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
        (AIMPWF1 : aimp_always_wf funcs map args (atrueDan b P) i1 Q fenv hl1)
        (SALVATION: terminator fenv args (atrueDan b P) Q i1 hl1)
        (s2 s1 : AbsState)
        (H : logic_transrelation args map P s1)
        (H0 : logic_transrelation args map Q s2)
        (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) P)
        (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) Q)
        (IMPWF1 : imp_rec_rel (var_map_wf_wrt_imp map) i1)
        (WF' : var_map_wf_wrt_bexp map b)
        (HL1 : forall (hl : hl_Dan (atrueDan b P) i1 Q fenv)
                 (func_list : list fun_Dan)
                 (idents : list DanLogicHelpers.ident),
            aimp_always_wf func_list idents args (atrueDan b P) i1 Q fenv hl ->
            forall (s1 s2 : AbsState) (i' : imp_stack) 
              (fenv' : fun_env_stk),
            forall (OKfuncs: funcs_okay_too func_list fenv')
              (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list),
              fenv_well_formed' func_list fenv ->
              fun_app_imp_well_formed fenv func_list i1 ->
              forall (SALVATION: terminator fenv args (atrueDan b P) Q i1 hl),
              i' = comp_code i1 idents args ->
              fenv' = compile_fenv fenv ->
              logic_transrelation args idents (atrueDan b P) s1 ->
              logic_transrelation args idents Q s2 ->
              imp_rec_rel (var_map_wf_wrt_imp idents) i1 ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
                               (var_map_wf_wrt_bexp idents) (atrueDan b P) ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
                               (var_map_wf_wrt_bexp idents) Q -> hl_stk s1 i' s2 fenv')
        (H1 : comp_logic args map P = s1):
  hl_stk
    (atruestk
       (compile_bexp b (ident_list_to_map map) (Datatypes.length map)) s1)
    (compile_imp i1 (ident_list_to_map map) (Datatypes.length map)) s2
    (compile_fenv fenv).
Proof.
  apply hl_stk_consequence with (P := comp_logic args map (atrueDan b P)) (Q := s2).
  * apply (HL1 hl1 funcs map AIMPWF1 _ s2 _ _ OKfuncs OKparams FENV_WF FUN_APP SALVATION); try reflexivity; try assumption.
    -- apply (log_comp_adequacy_backwards args map (atrueDan b P) (comp_logic args map (atrueDan b P))). reflexivity.
    -- constructor.
       assumption.
       constructor.
       constructor.
       constructor.
       assumption.
  * simpl. 
    rewrite H1.
    rewrite Nat.add_comm.
    subst.
    eapply hl_dan_implication_helper'; try eassumption.
    reflexivity.
  * unfold aimpstk; intros.
    assumption.
Defined.

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

Program Definition hl_compile_if_else_smaller (P Q : AbsEnv)
        (b : bexp_Dan)
        (i1 i2 : imp_Dan)
        (fenv : fun_env)
        (hl2 : hl_Dan (afalseDan b P) i2 Q fenv)
        (funcs: list fun_Dan)
        (args : nat)
        (IHhl2 : forall (map : list DanTrickLanguage.ident),
          forall (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
            (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
            fun_app_imp_well_formed fenv funcs i2 ->
            aimp_always_wf funcs map args (afalseDan b P) i2 Q fenv hl2 ->
            forall (s2 s1 : AbsState),
              logic_transrelation args map (afalseDan b P) s1 ->
              logic_transrelation args map Q s2 ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) (afalseDan b P) ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) Q ->
              imp_rec_rel (var_map_wf_wrt_imp map) i2 ->
              hl_stk s1
                     (compile_imp i2 (ident_list_to_map map) (Datatypes.length map))
                     s2 (compile_fenv fenv))
        (map : list DanTrickLanguage.ident)
        (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
        (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
        (FENV_WF : fenv_well_formed' funcs fenv)
        (FUN_APP : fun_app_imp_well_formed fenv funcs i2)
        (FUN_APP_B : fun_app_bexp_well_formed fenv funcs b)
        (AIMPWF2 : aimp_always_wf funcs map args (afalseDan b P) i2 Q fenv hl2)
        (DARKFATE: terminator fenv args (afalseDan b P) Q i2 hl2)
        (s2 s1 : AbsState)
        (H : logic_transrelation args map P s1)
        (H0 : logic_transrelation args map Q s2)
        (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) P)
        (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                               (var_map_wf_wrt_bexp map) Q)
        (IMPWF2 : imp_rec_rel (var_map_wf_wrt_imp map) i2)
        (IMPWF : var_map_wf_wrt_bexp map b)
        (HL2 : forall (hl : hl_Dan (afalseDan b P) i2 Q fenv)
                 (func_list : list fun_Dan)
                 (idents : list DanLogicHelpers.ident),
            aimp_always_wf func_list idents args (afalseDan b P) i2 Q fenv hl ->
            forall (s1 s2 : AbsState) (i' : imp_stack) 
              (fenv' : fun_env_stk),
            forall (OKfuncs: funcs_okay_too func_list fenv')
              (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list),
              fenv_well_formed' func_list fenv ->
              fun_app_imp_well_formed fenv func_list i2 ->
              forall (DARKFATE: terminator fenv args (afalseDan b P) Q i2 hl),
              i' = comp_code i2 idents args ->
              fenv' = compile_fenv fenv ->
              logic_transrelation args idents (afalseDan b P) s1 ->
              logic_transrelation args idents Q s2 ->
              imp_rec_rel (var_map_wf_wrt_imp idents) i2 ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
                               (var_map_wf_wrt_bexp idents) (afalseDan b P) ->
              AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
                               (var_map_wf_wrt_bexp idents) Q -> hl_stk s1 i' s2 fenv')
        (H1 : comp_logic args map P = s1):
  hl_stk
    (afalsestk
       (compile_bexp b (ident_list_to_map map) (Datatypes.length map)) s1)
    (compile_imp i2 (ident_list_to_map map) (Datatypes.length map)) s2
    (compile_fenv fenv).
Proof.
  apply hl_stk_consequence with (P := comp_logic args map (afalseDan b P)) (Q := s2).
  * apply HL2 with (hl := hl2) (idents := map) (func_list := funcs); try eassumption.
    -- reflexivity.
    -- reflexivity.
    -- apply log_comp_adequacy_backwards. reflexivity.
    -- constructor.
       assumption.
       constructor. constructor. constructor.
       assumption.
  * unfold afalsestk, afalseDan, ident_list_to_map.
    simpl.
    unfold comp_bool.
    rewrite Nat.add_comm.
    subst.
    apply hl_dan_implication_helper' with (d := P).
    apply log_comp_adequacy_backwards. reflexivity.
    reflexivity.
  * apply self_implication.
Defined.

Print hl_compile_if_else_smaller.

Program Definition hl_compile_if_smaller  (P Q : AbsEnv)
  (b : bexp_Dan)
  (i1 i2 : imp_Dan)
  (fenv : fun_env)
  (hl1 : hl_Dan (atrueDan b P) i1 Q fenv)
  (hl2 : hl_Dan (afalseDan b P) i2 Q fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl1 : forall (map : list DanTrickLanguage.ident),
      forall (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
        (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      fun_app_imp_well_formed fenv funcs i1 ->
      aimp_always_wf funcs map args (atrueDan b P) i1 Q fenv hl1 ->
      forall (s2 : AbsState) (s1 : AbsState),
        logic_transrelation args map (atrueDan b P) s1 ->
        logic_transrelation args map Q s2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (atrueDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) i1 ->
        hl_stk s1 (compile_imp i1 (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv))
  (IHhl2 : forall (map : list DanTrickLanguage.ident),
      forall (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
        (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
      fun_app_imp_well_formed fenv funcs i2 ->
      aimp_always_wf funcs map args (afalseDan b P) i2 Q fenv hl2 ->
      forall (s2 : AbsState) (s1 : AbsState),
        logic_transrelation args map (afalseDan b P) s1 ->
        logic_transrelation args map Q s2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (afalseDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) i2 ->
        hl_stk s1 (compile_imp i2 (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv))
  (map : list DanTrickLanguage.ident)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (when b then i1 else i2 done))
  (AIMPWF : aimp_always_wf funcs map args P (when b then i1 else i2 done) Q fenv (hl_Dan_if P Q b i1 i2 fenv hl1 hl2))
  (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (SALVATION: terminator fenv args (atrueDan b P) Q i1 hl1)
  (DARKFATE: terminator fenv args (afalseDan b P) Q i2 hl2)
  (s2 s1 : AbsState)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map Q s2)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q)
  (IMPWF : imp_rec_rel (var_map_wf_wrt_imp map) (when b then i1 else i2 done)):
  hl_stk s1 (comp_code (when b then i1 else i2 done) map args) s2 (compile_fenv fenv).
Proof.
  apply inv_fun_app_imp_if in FUN_APP.
  apply inv_imp_rec_rel_if in IMPWF.
  specialize (fun hl func_list => hl_Dan_implication (atrueDan b P) Q i1 fenv hl func_list args). intros HL1.
  specialize (fun hl func_list => hl_Dan_implication (afalseDan b P) Q i2 fenv hl func_list args). intros HL2.
  apply inv_aimpwf_if in AIMPWF. 
  assert (comp_logic args map P = s1) by (apply log_comp_adequacy_forward; eassumption).
  pose proof (proj1 IMPWF) as IMPWF1.
  pose proof (proj1 (proj2 IMPWF)) as IMPWF2.
  pose proof (proj2 (proj2 IMPWF)) as IMPWF3.
  apply var_map_wf_wrt_imp_if_imp_forall in IMPWF3.
  apply inv_imp_forall_if_get_cond in IMPWF3.
  pose proof (proj1 FUN_APP) as FUN_APPb.
  pose proof (proj1 (proj2 FUN_APP)) as FUN_APP1.
  pose proof (proj2 (proj2 FUN_APP)) as FUN_APP2.
  pose proof (proj1 AIMPWF) as AIMPWF1.
  pose proof (proj2 AIMPWF) as AIMPWF2.
  constructor. 
  apply comp_bexp_implies_pure' with (bdan := b) (bstk := compile_bexp b (ident_list_to_map map) (Datatypes.length map)) (map := map) (fenv_i := fenv) (fenv_s := compile_fenv fenv) (funcs := funcs); auto.
  + eapply hl_compile_if_then_smaller with (P := P) (Q := Q) (hl1 := hl1) (args := args) (funcs := funcs); try assumption.
  + apply hl_compile_if_else_smaller with (P := P) (Q := Q) (hl2 := hl2) (args := args) (funcs := funcs); try assumption.
Defined.


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
  (b : bexp_Dan)
  (i : imp_Dan)
  (fenv : fun_env)
  (hl : hl_Dan (atrueDan b P) i P fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl : forall map : list DanTrickLanguage.ident,
      aimp_always_wf funcs map args (atrueDan b P) i P fenv hl ->
      fun_app_imp_well_formed fenv funcs i ->
      forall (fenv0 : fun_env_stk) (s2 : AbsState) (i' : imp_stack) (s1 : AbsState),
        logic_transrelation args map (atrueDan b P) s1 ->
        logic_transrelation args map P s2 ->
        i' = compile_imp i (ident_list_to_map map) (Datatypes.length map) ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (atrueDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P ->
        imp_rec_rel (var_map_wf_wrt_imp map) i -> hl_stk s1 i' s2 fenv0)
  (map : list DanTrickLanguage.ident)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (while b loop i done))
  (AIMPWF : aimp_always_wf funcs map args P (while b loop i done) (afalseDan b P) fenv (hl_Dan_while P b i fenv hl))
  (fenv0 : fun_env_stk)
  (OKfuncs: funcs_okay_too funcs fenv0)
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (JOHNCONNOR: terminator fenv args (atrueDan b P) P i hl)
  (i' : imp_stack)
  (s2 s1 : AbsState)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map (afalseDan b P) s2)
  (H1 : i' = comp_code (while b loop i done) map args)
  (H2 : fenv0 = compile_fenv fenv)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (afalseDan b P))
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) (while b loop i done)) :
  hl_stk s1 i' s2 fenv0.
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
  pose proof (HL := hl_Dan_implication).
  specialize (HL (atrueDan b P) P i fenv).
  econstructor. eapply hl_stk_while.
  + eapply comp_bexp_implies_pure'; eauto. unfold ident_list_to_map. ereflexivity.
    eapply inv_fun_app_imp_while in FUN_APP. destruct FUN_APP. assumption.
  + eapply hl_stk_consequence.
    * eapply HL.
      -- invs_aimpwf_helper AIMPWF.
         eassumption.
      -- assumption.
      -- assumption.
      -- eassumption.
      -- eapply inv_fun_app_imp_while in FUN_APP. destruct FUN_APP. assumption.
      -- apply JOHNCONNOR. 
      -- unfold comp_code. reflexivity.
         
      -- reflexivity.
      -- log_comp_adequate.
      -- eassumption.
      -- invs IMPWF.
         assumption.
      -- econstructor; try eassumption.
         econstructor. econstructor. econstructor.
         smart_unfold_wf_imp_in IMPWF. invs WF'. assumption.
      -- assumption.
    * eapply compiling_afalse_atrue'.
      -- ereflexivity.
      -- right. split; ereflexivity.
      -- log_comp_adequate.
      -- eassumption.
    * eapply self_implication.
  + eapply self_implication.
  + eapply compiling_afalse_atrue'.
    * ereflexivity.
    * left. split; ereflexivity.
    * eassumption.
    * assumption.
Defined.

Lemma inv_aimpwf_while :
  forall funcs map args P b i fenv hl,
    aimp_always_wf funcs map args P (while b loop i done) (afalseDan b P) fenv (hl_Dan_while P b i fenv hl) ->
    aimp_always_wf funcs map args (atrueDan b P) i P fenv hl.
Proof.
  intros. invs H.
  - inversion HSkip.
  - inversion Heq.
  - inversion Heq.
  - inversion heq.
  - invs Heq.
    specialize (UIP_imp_refl _ Heq).
    intros. subst. simpl in *.
    specialize (DanLogPropDec.UIP_AbsEnv_refl _ HeqP).
    intros. subst. simpl in H0.
    invs H0.
    inversion_sigma_helper H8.
    unfold aimp_always_wf. assumption.
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

Lemma atrueDan_well_formed :
  forall map P b i,
    AbsEnv_prop_rel (var_map_wf_wrt_aexp map)
                     (var_map_wf_wrt_bexp map) P ->
    var_map_wf_wrt_imp map (while b loop i done) ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map)
                     (atrueDan b P).
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

Program Definition hl_compile_while_small (P : AbsEnv)
  (b : bexp_Dan)
  (i : imp_Dan)
  (fenv : fun_env)
  (hl : hl_Dan (atrueDan b P) i P fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl : forall map : list DanTrickLanguage.ident,
      fun_app_imp_well_formed fenv funcs i ->
      aimp_always_wf funcs map args (atrueDan b P) i P fenv hl ->
      forall (s2 : AbsState) (s1 : AbsState),
        logic_transrelation args map (atrueDan b P) s1 ->
        logic_transrelation args map P s2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (atrueDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P ->
        imp_rec_rel (var_map_wf_wrt_imp map) i ->
        hl_stk s1 (compile_imp i (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv))
  (map : list DanTrickLanguage.ident)
  (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs (while b loop i done))
  (AIMPWF : aimp_always_wf funcs map args P (while b loop i done) (afalseDan b P) fenv (hl_Dan_while P b i fenv hl))
  (JOHNCONNOR: terminator fenv args (atrueDan b P) P i hl)
  (s2 s1 : AbsState)
  (H : logic_transrelation args map P s1)
  (H0 : logic_transrelation args map (afalseDan b P) s2)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P)
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) (afalseDan b P))
  (IMPWF : imp_rec_rel (var_map_wf_wrt_imp map) (while b loop i done)) :
  hl_stk s1 (compile_imp (while b loop i done) (ident_list_to_map map) (Datatypes.length map)) s2 (compile_fenv fenv).
Proof.
  unfold comp_code in *; subst;
    simpl.
  apply inv_fun_app_imp_while in FUN_APP.
  apply inv_aimpwf_while in AIMPWF.
  apply inv_imp_rec_rel_while in IMPWF.
  destruct IMPWF.
  destruct FUN_APP.
  pose proof (HL := hl_Dan_implication).
  specialize (log_comp_adequacy_backwards args map (atrueDan b P) (comp_logic args map (atrueDan b P)) (@eq_refl _ (comp_logic args map (atrueDan b P)))). intros ATRUE.
  specialize (HL (atrueDan b P) P i fenv).
  econstructor. eapply hl_stk_while.
  + eapply comp_bexp_implies_pure'; eauto. unfold ident_list_to_map. ereflexivity.
  + eapply hl_stk_consequence with (P := (comp_logic args map (atrueDan b P))) (Q := s1) (Q' := s1).
    * eapply HL with (n_args := args) (idents := map) (hl := hl) (s1 := (comp_logic args map (atrueDan b P))) (s2 := s1) (func_list := funcs).
      -- assumption.
      -- assumption.
      -- assumption.
      -- assumption.
      -- eassumption.
      -- simpl in JOHNCONNOR; intuition. 
      -- reflexivity.
         
      -- reflexivity.
      -- apply ATRUE.
      -- assumption.
      -- assumption.
      -- apply atrueDan_well_formed with (i := i).
         ++ assumption.
         ++ assumption.
      -- assumption.
    * apply compiling_afalse_atrue' with (d := P) (n_args := args) (fenv := fenv) (afalsetrueDan := atrueDan).
      -- reflexivity.
      -- right. split; reflexivity.
      -- apply ATRUE.
      -- assumption.
    * apply self_implication.
  + apply self_implication.
  + apply compiling_afalse_atrue' with (afalsetrueDan := afalseDan) (fenv := fenv) (n_args := args) (d := P).
    * reflexivity.
    * left. split; reflexivity.
    * assumption.
    * assumption.
Defined.


Program Definition hl_compile_consequence (P Q P' Q' : AbsEnv)
  (c : imp_Dan)
  (fenv : fun_env)
  (hl : hl_Dan P c Q fenv)
  (a : (P' -->> P) fenv)
  (a0 : (Q -->> Q') fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl : forall map : list DanTrickLanguage.ident,
      fun_app_imp_well_formed fenv funcs c ->
      aimp_always_wf funcs map args P c Q fenv hl ->
      forall (fenv0 : fun_env_stk) (s2 : AbsState) (i' : imp_stack) (s1 : AbsState),
        logic_transrelation args map P s1 ->
        logic_transrelation args map Q s2 ->
        i' = compile_imp c (ident_list_to_map map) (Datatypes.length map) ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) c -> hl_stk s1 i' s2 fenv0)
  (map : list DanTrickLanguage.ident)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs c)
  (AIMPWF : aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0))
  (SARAHCONNOR : terminator fenv args P' Q' c (hl_Dan_consequence P Q P' Q' c fenv hl a a0))
  (s2 s1 : AbsState)
  (i' : imp_stack)
  (fenv0: fun_env_stk)
  (OKfuncs: funcs_okay_too funcs fenv0)
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (H : logic_transrelation args map P' s1)
  (H0 : logic_transrelation args map Q' s2)
  (H1 : i' = comp_code c map args)
  (H2 : fenv0 = compile_fenv fenv)
  (H3 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P')
  (H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q')
  (H5 : imp_rec_rel (var_map_wf_wrt_imp map) c):
  hl_stk s1 i' s2 fenv0.
Proof.
  unfold comp_code in *; subst;
    rename_fresh_until_no_match;
    match goal with
    | [ H: imp_rec_rel (var_map_wf_wrt_imp ?map) ?i |- _ ] =>
        let IMPWF := fresh "IMPWF" in
        pose proof (IMPWF := H); clear H
    | _ => idtac
    end.
  assert (logic_transrelation args map P (comp_logic args map P)) by log_comp_adequate.
  assert (logic_transrelation args map Q (comp_logic args map Q)) by log_comp_adequate.
  pose proof (a' := a).
  pose proof (a0' := a0).
  pose proof (IMPWF' := IMPWF).
  eapply imp_rec_rel_var_map_wf_adequacy in IMPWF'.
  eapply imp_rec_rel_self in IMPWF.
  unfold aimp_always_wf in AIMPWF.
  
  destruct (inv_aimpwf_consequence _ _ _ _ _ _ _ _ _ _ _ _ AIMPWF) as (lwf1 & lwf2 & lwf3 & lwf4 & lwf5 & lwf6 & lwf7 & lwf8 & rel1 & rel2 & rel3 & rel4 & _). 
  eapply aimpdan_to_aimpstk in a'; [ | try eassumption; try ereflexivity .. ].
  eapply aimpdan_to_aimpstk in a0'; [ | try eassumption; try ereflexivity .. ].
  + eapply hl_stk_consequence; [ | try eassumption .. ].
    eapply IHhl; try eassumption; try ereflexivity.
    * invs_aimpwf_helper AIMPWF; try (simpl in H3; invs H3).
      clear H17.
      inversion_sigma_helper H23.
      eassumption.
    * invs_aimpwf_helper AIMPWF; try (simpl in H3; invs H3).
      clear H17. inversion_sigma_helper H23. eassumption.
  + simpl in SARAHCONNOR. intuition.
  + simpl in SARAHCONNOR. intuition.
  + unfold_wf_imp_in IMPWF. eapply WF1.
  + simpl in SARAHCONNOR. intuition.
  + simpl in SARAHCONNOR. intuition. 
  + unfold_wf_imp_in IMPWF. eapply WF1.
Defined.

Lemma inv_aimpwf_consequence' :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    AbsEnv_prop_wf map P /\
      AbsEnv_prop_wf map Q /\
      aimp_always_wf funcs map args P c Q fenv hl.
Proof.
  intros. unfold aimp_always_wf in H. inversion H.
  - subst. inversion H0.
  - subst. inversion H0.
  - subst. inversion H0.
  - subst. inversion H0.
  - subst. inversion H0.
  - invs H0.
    inversion_sigma_helper H23.
    split; [ | split ]; assumption.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_P :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf funcs fenv P.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_P' :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf funcs fenv P'.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_Q :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf funcs fenv Q.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_Q' :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf funcs fenv Q'.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequenc_log_Dan_wf_map_Q :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf_map map Q.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_map_Q' :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf_map map Q'.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_map_P :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf_map map P.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma inv_aimpwf_consequence_log_Dan_wf_map_P' :
  forall funcs map args P' c Q' fenv P Q hl a a0,
    aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf_map map P'.
Proof.
  intros. pose proof (inv_aimpwf_consequence funcs map args P Q P' Q' c fenv hl a a0 H). intuition.
Qed.

Lemma imp_rec_rel_var_map_wf_nodup_idents :
  forall (idents: list ident) (c: imp_Dan),
    imp_rec_rel (var_map_wf_wrt_imp idents) c ->
    NoDup idents.
Proof.
  intros. eapply imp_rec_rel_self in H.
  unfold_wf_imp_in H. eapply WF.
Qed.
  

    
Program Definition hl_compile_consequence_smaller (P Q P' Q' : AbsEnv)
  (c : imp_Dan)
  (fenv : fun_env)
  (hl : hl_Dan P c Q fenv)
  (a : (P' -->> P) fenv)
  (a0 : (Q -->> Q') fenv)
  (funcs: list fun_Dan)
  (args : nat)
  (IHhl : forall map : list DanTrickLanguage.ident,
      fun_app_imp_well_formed fenv funcs c ->
      aimp_always_wf funcs map args P c Q fenv hl ->
      forall (s2 : AbsState) (s1 : AbsState),
        logic_transrelation args map P s1 ->
        logic_transrelation args map Q s2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q ->
        imp_rec_rel (var_map_wf_wrt_imp map) c -> hl_stk s1 (comp_code c map args) s2 (compile_fenv fenv))
  (map : list DanTrickLanguage.ident)
  (OKfuncs: funcs_okay_too funcs (compile_fenv fenv))
  (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs)
  (FENV_WF : fenv_well_formed' funcs fenv)
  (FUN_APP : fun_app_imp_well_formed fenv funcs c)
  (AIMPWF : aimp_always_wf funcs map args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0))
  (SARAHCONNOR : terminator fenv args P' Q' c (hl_Dan_consequence P Q P' Q' c fenv hl a a0))
  (s2 s1 : AbsState)
  (H : logic_transrelation args map P' s1)
  (H0 : logic_transrelation args map Q' s2)
  (WF_P' : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) P')
  (WF_Q' : AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) Q')
  (IMPWF : imp_rec_rel (var_map_wf_wrt_imp map) c):
  hl_stk s1 (comp_code c map args) s2 (compile_fenv fenv).
Proof.
  specialize (log_comp_adequacy_backwards args map P (comp_logic args map P) (eq_refl (comp_logic args map P))).
  intros LOGIC_P.
  specialize (log_comp_adequacy_backwards args map Q (comp_logic args map Q) (eq_refl (comp_logic args map Q))).
  intros LOGIC_Q.
  pose proof (WfP := inv_aimpwf_consequence_log_Dan_wf_P funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfP' := inv_aimpwf_consequence_log_Dan_wf_P' funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfQ := inv_aimpwf_consequence_log_Dan_wf_Q funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfQ' := inv_aimpwf_consequence_log_Dan_wf_Q' funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfMapP := inv_aimpwf_consequence_log_Dan_wf_map_P funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfMapP' := inv_aimpwf_consequence_log_Dan_wf_map_P' funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfMapQ := inv_aimpwf_consequenc_log_Dan_wf_map_Q funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  pose proof (WfMapQ' := inv_aimpwf_consequence_log_Dan_wf_map_Q' funcs map args P' c Q' fenv P Q hl a a0 AIMPWF).
  unfold aimp_always_wf in AIMPWF.
  apply inv_aimpwf_consequence' in AIMPWF.
  pose proof (proj1 AIMPWF) as WF1.
  pose proof (proj1 (proj2 AIMPWF)) as WF2.
  pose proof (proj2 (proj2 AIMPWF)) as AIMPWF'.
  simpl in SARAHCONNOR. 
  pose proof (imp_rec_rel_var_map_wf_nodup_idents _ _ IMPWF).
  apply aimpdan_to_aimpstk with (s1 := s1) (s2 := (comp_logic args map P)) (fenv' := compile_fenv fenv) (n_args := args) (idents := map) (func_list := funcs) in a; auto.
  apply aimpdan_to_aimpstk with (s1 := (comp_logic args map Q)) (s2 := s2) (fenv' := compile_fenv fenv) (n_args := args) (idents := map) (func_list := funcs) in a0; auto.
  apply hl_stk_consequence with (P := comp_logic args map P) (Q := comp_logic args map Q); [ | try eassumption .. ].
  apply IHhl; eauto.
  - apply (proj1 (proj2 (proj2 (proj2 SARAHCONNOR)))).
  - apply (proj2 (proj2 (proj2 (proj2 SARAHCONNOR)))).
  - apply (proj1 (proj2 (proj2 SARAHCONNOR))).
  - apply (proj1 (proj2 SARAHCONNOR)).
Defined.

Definition induction_P (d: AbsEnv) (i: imp_Dan) (d0: AbsEnv) (f: fun_env) (hl: hl_Dan d i d0 f): Type :=
  forall (funcs: list fun_Dan),
    fenv_well_formed' funcs f ->
  forall (map: list DanTrickLanguage.ident) (args : nat)
    (s1: AbsState) (i': imp_stack)
    (s2: AbsState) (fenv: fun_env_stk),
  forall (OKfuncs: funcs_okay_too funcs fenv)
    (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
    fun_app_imp_well_formed f funcs i ->
    aimp_always_wf funcs map args d i d0 f hl ->
    logic_transrelation args map d s1 ->
    logic_transrelation args map d0 s2 ->
    forall (ARNOLD: terminator f args d d0 i hl),
    i' = comp_code i map args ->
    fenv = compile_fenv f ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d0 ->
    imp_rec_rel (var_map_wf_wrt_imp map) i ->
    hl_stk s1 i' s2 fenv.

Program Definition hl_compile (d1 d2: AbsEnv) (i: imp_Dan) (fenv: fun_env) (hl: hl_Dan d1 i d2 fenv): induction_P d1 i d2 fenv hl.
Proof.
  unfold induction_P. intros ? ? ? ? ? ? ? ? ? ? ? AIMPWF.
  revert OKfuncs. revert OKparams. revert fenv0 s2 i' s1. revert H0.
  
  dependent induction hl; intros.
  - apply hl_compile_skip with (P := P) (args := args) (fenv := fenv) (map := map) (func_list := funcs); assumption.
  - apply hl_compile_assign with (P := P) (args := args) (fenv := fenv) (x := x) (a := a) (map := map) (funcs := funcs); assumption.
  - apply hl_compile_seq with (P := P) (Q := Q) (R := R) (hl1 := hl1) (hl2 := hl2) (args := args) (map := map) (funcs := funcs); try assumption.
    intros. rewrite <- H13 in H4. subst fenv0. eapply IHhl1; try eassumption. simpl in ARNOLD. eapply ARNOLD.
    intros. rewrite <- H13 in H4. subst fenv0. eapply IHhl2; try eassumption. simpl in ARNOLD. eapply ARNOLD.
  - apply hl_compile_if with (P := P) (args := args) (Q := Q) (hl1 := hl1) (hl2 := hl2) (map := map) (funcs := funcs); try assumption; intros; subst; simpl in ARNOLD; try intuition.
    eapply IHhl1; eauto. invs H0.
    assumption.
    eapply IHhl2; eauto.
    
  - apply hl_compile_while with (P := P) (args := args) (hl := hl) (map := map) (funcs := funcs); try assumption; intros; subst; simpl in ARNOLD; try eapply ARNOLD.
    eapply IHhl; eauto.
    eapply ARNOLD.
  - apply hl_compile_consequence with (P := P) (Q := Q) (P' := P') (Q' := Q') (args := args) (hl := hl) (a := a) (a0 := a0) (map := map) (funcs := funcs); try assumption; try (eapply ARNOLD).
    intros; subst. eapply IHhl; eauto.
    eapply ARNOLD.
Defined.

Program Definition hl_compile_smaller (d1 d2: AbsEnv) (i: imp_Dan) (fenv: fun_env) (hl: hl_Dan d1 i d2 fenv): induction_P d1 i d2 fenv hl.
Proof.
  unfold induction_P. intros ? ? ? ? ? ? ? ? ? ? ? AIMPWF.
  revert OKfuncs OKparams. revert fenv0 s2 i' s1. revert H0.
  dependent induction hl; intros; subst.
  - apply hl_compile_skip_term_minimized with (P := P) (args := args) (fenv := fenv) (map := map); simpl in ARNOLD; try intuition.
  - apply hl_compile_assign_small with (P := P) (args := args) (fenv := fenv) (x := x) (a := a) (map := map) (funcs := funcs); try assumption.
  - apply hl_compile_seq_smaller with (P := P) (Q := Q) (R := R) (hl1 := hl1) (hl2 := hl2) (args := args) (map := map) (funcs := funcs); try assumption; intros.
    + eapply IHhl1; eauto. apply (proj1 ARNOLD).
    + eapply IHhl2; eauto. apply (proj1 (proj2 ARNOLD)).
  - subst. apply hl_compile_if_smaller with (P := P) (args := args) (Q := Q) (hl1 := hl1) (hl2 := hl2) (map := map) (funcs := funcs); try assumption; intros.
    + eapply IHhl1; eauto. apply (proj1 ARNOLD).
    + eapply IHhl2; eauto. apply (proj1 (proj2 ARNOLD)).
    + apply (proj1 ARNOLD).
    + apply (proj1 (proj2 ARNOLD)).
  - apply hl_compile_while_small with (P := P) (args := args) (hl := hl) (map := map) (funcs := funcs); try assumption; try (eapply ARNOLD).
    intros. apply IHhl with (map := map0) (args := args) (funcs := funcs); eauto. eapply ARNOLD.
  - apply hl_compile_consequence_smaller with (P := P) (Q := Q) (P' := P') (Q' := Q') (args := args) (hl := hl) (a := a) (a0 := a0) (map := map) (funcs := funcs); eauto; simpl in ARNOLD; try intuition.
    apply IHhl with (map := map0) (args := args) (funcs := funcs); try assumption; reflexivity.
Defined.


End Tests.
