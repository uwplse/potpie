From Coq Require Import String List Peano Arith Program.Equality.
From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
(* From Imp_LangTrick Require Import LogicTranslationBackwards TranslationPure LogicTranslationAdequate LogicTrans. *)
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel ProofCompilerHelpers Imp_LangHoareWF.
From Imp_LangTrick Require Import ProofCompilerBase Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import FunctionWellFormed
CompilerAssumptionLogicTrans ParamsWellFormed.
From Imp_LangTrick Require Import Imp_LangLogicHelpers FactEnvTranslator.

(*
 * This is the file for the proof compiler, which compiles
 * proofs in Imp_LangTrickLogic to proofs in StackLogic.
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.


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
  Definition max : fun_Imp_Lang := max_fun.
  Check max.
  Compute max.

  (* A more concise version for simplicity *)
  Local Open Scope bool_scope.
  Definition maxSmall : fun_Imp_Lang :=
    {|
      Imp_LangTrickLanguage.Name := "maxSmall";
      Imp_LangTrickLanguage.Args := 2;
      Ret := "z";
      Imp_LangTrickLanguage.Body :=
        (IF_Imp_Lang
           (AND_Imp_Lang (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (PARAM_Imp_Lang 0))
                    (NEG_Imp_Lang
                       (AND_Imp_Lang (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (PARAM_Imp_Lang 0))
                                (LEQ_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1)))))
           (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0))
           (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1)))
    |}.

  Definition bexp_conditional :=
     (AND_Imp_Lang (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (PARAM_Imp_Lang 0))
                    (NEG_Imp_Lang
                       (AND_Imp_Lang (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (PARAM_Imp_Lang 0))
                                (LEQ_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1))))).

  Definition true_bool (b: bexp_Imp_Lang) : AbsEnv :=
    AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ (fun v => v = true) b)).

  Definition false_bool (b: bexp_Imp_Lang) : AbsEnv :=
    AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ (fun v => v = false) b)).

  Definition imp_lang_log_true : AbsEnv :=
    AbsEnvLP (Imp_Lang_lp_arith (TrueProp _ _ )).
  Definition my_geq (a1 a2: aexp_Imp_Lang): AbsEnv :=
    AbsEnvLP (Imp_Lang_lp_arith (BinaryProp _ _ (fun a b => a >= b)
                                         a1
                                         a2)).
  Definition max_conclusion : AbsEnv :=
    AbsEnvAnd (true_bool (geq_Imp_Lang (VAR_Imp_Lang "z") (PARAM_Imp_Lang 0)))
                (true_bool (geq_Imp_Lang (VAR_Imp_Lang "z") (PARAM_Imp_Lang 1))).
 
  
  Definition param0gtparam1 : AbsEnv :=
    true_bool (gt_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1)).

  Definition notparam0gtparam1 : AbsEnv :=
    false_bool (gt_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1)).

  Definition param0geqparam0 : AbsEnv :=
    true_bool (geq_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 0)).

  Definition param0geqparam1 : AbsEnv :=
    true_bool (geq_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1)).

  Definition param1geqparam0 : AbsEnv :=
    true_bool (geq_Imp_Lang (PARAM_Imp_Lang 1) (PARAM_Imp_Lang 0)).
  Definition param1geqparam1 : AbsEnv :=
    true_bool (geq_Imp_Lang (PARAM_Imp_Lang 1) (PARAM_Imp_Lang 1)).



  Ltac imp_lang_log_inversion :=
    match goal with
    | [ H: AbsEnv_rel (AbsEnvAnd ?inner1 ?inner2) ?fenv ?dbenv ?nenv |- _ ] =>
        invc H;
        imp_lang_log_inversion
    | [ H: AbsEnv_rel (AbsEnvOr ?inner1 ?inner2) _ _ _ |- _ ] =>
        invc H; try imp_lang_log_inversion
    | [ H: AbsEnv_rel (AbsEnvLP ?lp) _ _ _ |- _ ] =>
        invc H; try imp_lang_log_inversion
    | [ H: Imp_Lang_lp_rel (Imp_Lang_lp_arith ?lp) _ _ _ |- _ ] =>
        invc H; try imp_lang_log_inversion
    | [ H: Imp_Lang_lp_rel (Imp_Lang_lp_bool ?lp) _ _ _ |- _ ] =>
        invc H; try imp_lang_log_inversion
    | [ H: eval_prop_rel _ _ |- _ ] =>
        invc H; try imp_lang_log_inversion
    | [ H: b_Imp_Lang ?b _ _ _ _ |- _ ] =>
        match b with
        | AND_Imp_Lang _ _ =>
            invc H; try imp_lang_log_inversion
        | OR_Imp_Lang _ _ =>
            invc H; try imp_lang_log_inversion
        | LEQ_Imp_Lang _ _ =>
            invc H; try imp_lang_log_inversion
        | NEG_Imp_Lang _ =>
            invc H; try imp_lang_log_inversion
        | geq_Imp_Lang _ _ =>
            invc H; try imp_lang_log_inversion
        | gt_Imp_Lang _ _ =>
            unfold gt_Imp_Lang in H; invc H; try imp_lang_log_inversion
        | lt_Imp_Lang _ _ =>
            unfold lt_Imp_Lang in H; invc H; try imp_lang_log_inversion
        | eq_Imp_Lang _ _ =>
            unfold eq_Imp_Lang in H; invc H; try imp_lang_log_inversion
        | neq_Imp_Lang _ _ =>
            unfold neq_Imp_Lang in H; invc H; try imp_lang_log_inversion
        | _ =>
            idtac "Don't inversion " H
        end
    | [ H: a_Imp_Lang ?a _ _ _ _ |- _ ] =>
        match a with
        | PLUS_Imp_Lang _ _ =>
            invc H; try imp_lang_log_inversion
        | MINUS_Imp_Lang _ _ =>
            invc H; try imp_lang_log_inversion
        | VAR_Imp_Lang _ =>
            invc H; try imp_lang_log_inversion
        | _ =>
            idtac "Don't inversion " H
        end
    end.

  Ltac imp_lang_log_constructor :=
    match goal with
    | [ |- AbsEnv_rel _ _ _ _ ] =>
        econstructor; try imp_lang_log_constructor
    | [ |- Imp_Lang_lp_rel _ _ _ _ ] =>
        econstructor; try imp_lang_log_constructor
    | [ |- eval_prop_rel _ _ ] =>
        econstructor; try imp_lang_log_constructor
    | [ |- b_Imp_Lang ?b _ _ _ _ ] =>
        match b with
        | AND_Imp_Lang _ _ =>
            econstructor; try imp_lang_log_constructor
        | OR_Imp_Lang _ _ =>
            econstructor; try imp_lang_log_constructor
        | LEQ_Imp_Lang _ _ =>
            econstructor; try imp_lang_log_constructor
        | NEG_Imp_Lang _ =>
            econstructor; try imp_lang_log_constructor
        | geq_Imp_Lang _ _ =>
            unfold geq_Imp_Lang; try imp_lang_log_constructor
        | _ =>
            idtac "Don't econstructor " b;
            try eassumption
        end
    | [ |- a_Imp_Lang ?a _ _ _ _ ] =>
        match a with
        | PLUS_Imp_Lang _ _ =>
            econstructor; try imp_lang_log_constructor
        | MINUS_Imp_Lang _ _ =>
            econstructor; try imp_lang_log_constructor
        | VAR_Imp_Lang _ =>
            econstructor; try imp_lang_log_constructor
        | _ =>
            idtac "Don't econstructor " a;
            try eassumption
        end
    end.

  
  Lemma aimpImp_LangPP' fenv :
    aimpImp_Lang (AbsEnvAnd imp_lang_log_true param0gtparam1)
            (AbsEnvAnd param0geqparam0 param0geqparam1) fenv.
  Proof.
    unfold aimpImp_Lang, param0gtparam1, param0geqparam0, param0geqparam1.
    intros.
    unfold true_bool in *. unfold imp_lang_log_true in *.
    imp_lang_log_inversion; a_Imp_Lang_elim.
    
    econstructor.
    - econstructor. econstructor.
      econstructor.
      econstructor. eassumption. eassumption.
      rewrite H1.
      apply Nat.leb_le. auto.
    - imp_lang_log_constructor.
      rewrite H1.
      symmetry in H1.
      eapply Bool.andb_true_eq in H1.
      destruct H1.
      rewrite Bool.negb_andb in H0.
      rewrite H. reflexivity.
  Qed.

  Lemma aimpImp_LangQQ' fenv :
    aimpImp_Lang max_conclusion max_conclusion fenv.
  Proof.
    unfold aimpImp_Lang.
    intros. assumption.
  Defined.
  

  Lemma secondaimpImp_LangP'P fenv :
    aimpImp_Lang (AbsEnvAnd imp_lang_log_true
                              notparam0gtparam1)
            (AbsEnvAnd param1geqparam0
                         param1geqparam1) fenv.
  Proof.
    unfold aimpImp_Lang, imp_lang_log_true, notparam0gtparam1, param1geqparam0, param1geqparam1.
    intros.
    unfold false_bool in *. unfold true_bool in *.
    imp_lang_log_inversion.
    a_Imp_Lang_elim.
    
    rewrite Bool.andb_false_iff in H1.
    destruct H1.
    - eapply Nat.leb_gt in H.
      imp_lang_log_constructor.
      eapply Nat.leb_le. intuition.
      eapply Nat.leb_le. auto.
    - eapply Bool.negb_false_iff in H.
      symmetry in H.
      eapply Bool.andb_true_eq in H.
      destruct H.
      imp_lang_log_constructor.
      symmetry in H0. assumption.
      eapply Nat.leb_le. auto.
  Defined.

Definition imp_list := ((AbsEnvAnd imp_lang_log_true param0gtparam1), (AbsEnvAnd param0geqparam0 param0geqparam1)) :: ((AbsEnvAnd imp_lang_log_true notparam0gtparam1), (AbsEnvAnd param1geqparam0 param1geqparam1))::nil. 

Lemma zeroth_impliction : nth_error imp_list 0 = Some
  (AbsEnvAnd imp_lang_log_true param0gtparam1,
   AbsEnvAnd param0geqparam0 param0geqparam1).
Proof. 
  simpl; apply eq_refl. 
Qed. 

Lemma first_implication : nth_error imp_list 1 = Some
  (AbsEnvAnd imp_lang_log_true notparam0gtparam1,
   AbsEnvAnd param1geqparam0 param1geqparam1).
Proof.
  simpl; apply eq_refl. 
Qed. 

Lemma imp_list_valid : forall fenv, fact_env_valid imp_list fenv.
Proof.
  unfold fact_env_valid. intros. destruct H.
  + pose proof pair_equal_spec (AbsEnvAnd imp_lang_log_true param0gtparam1) P (AbsEnvAnd param0geqparam0 param0geqparam1) Q. destruct H0. specialize (H0 H). destruct H0. subst. apply aimpImp_LangPP'.
  + destruct H. 
    * pose proof pair_equal_spec (AbsEnvAnd imp_lang_log_true notparam0gtparam1) P (AbsEnvAnd param1geqparam0 param1geqparam1) Q. destruct H0. specialize (H0 H). destruct H0. subst. apply secondaimpImp_LangP'P.
    * destruct H.
Qed.
  
  Definition maxSmallProof :=
    hl_Imp_Lang_if imp_lang_log_true
              max_conclusion
              (gt_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1))
              (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0))
              (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1))
              imp_list
              init_fenv
              (hl_Imp_Lang_consequence_pre
                 (AbsEnvAnd param0geqparam0 param0geqparam1)
                 max_conclusion
                 (AbsEnvAnd imp_lang_log_true param0gtparam1)
                 (* max_conclusion *)
                 (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0))
                 0
                 imp_list
                 init_fenv
                 (hl_Imp_Lang_assign
                    max_conclusion
                    imp_list
                    init_fenv
                    "z"
                    (PARAM_Imp_Lang 0))
                 zeroth_impliction
                 (aimpImp_LangPP' init_fenv))
              (hl_Imp_Lang_consequence_pre
                 (AbsEnvAnd param1geqparam0
                              param1geqparam1)
                 max_conclusion
                 (AbsEnvAnd imp_lang_log_true
                              notparam0gtparam1)
                 (* max_conclusion *)
                 (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1))
                 1
                 imp_list
                 init_fenv
                 (hl_Imp_Lang_assign
                    max_conclusion
                    imp_list
                    init_fenv
                    "z"
                    (PARAM_Imp_Lang 1))
                  first_implication
                 (secondaimpImp_LangP'P init_fenv)).
  
    
  Lemma maxSmallLemma :
    forall fenv,
      hl_Imp_Lang imp_lang_log_true (Imp_LangTrickLanguage.Body maxSmall) max_conclusion imp_list fenv.
  Proof.
    unfold maxSmall.
    simpl.
    intros.
    unfold imp_lang_log_true, max_conclusion.
    eapply hl_Imp_Lang_if.
    - eapply hl_Imp_Lang_consequence_pre.
      + assert (hl_Imp_Lang (AbsEnvAnd param0geqparam0 param0geqparam1)
                       (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0))
                       max_conclusion
                       imp_list
                       fenv).
        * unfold param0geqparam0.
          unfold param0geqparam1.
          unfold true_bool.
          unfold max_conclusion.
          unfold true_bool.
          assert (Imp_LangLogSubst.subst_AbsEnv "z" (PARAM_Imp_Lang 0) (AbsEnvAnd
       (AbsEnvLP
          (Imp_Lang_lp_bool
             (UnaryProp bool bexp_Imp_Lang (fun v : bool => v = true)
                (VAR_Imp_Lang "z" >=d PARAM_Imp_Lang 0))))
       (AbsEnvLP
          (Imp_Lang_lp_bool
             (UnaryProp bool bexp_Imp_Lang (fun v : bool => v = true)
                (VAR_Imp_Lang "z" >=d PARAM_Imp_Lang 1))))) = (AbsEnvAnd
       (AbsEnvLP
          (Imp_Lang_lp_bool
             (UnaryProp bool bexp_Imp_Lang (fun v : bool => v = true)
                (PARAM_Imp_Lang 0 >=d PARAM_Imp_Lang 0))))
       (AbsEnvLP
          (Imp_Lang_lp_bool
             (UnaryProp bool bexp_Imp_Lang (fun v : bool => v = true)
                        (PARAM_Imp_Lang 0 >=d PARAM_Imp_Lang 1)))))).
          {
            simpl. unfold geq_Imp_Lang. reflexivity.
          }
          rewrite <- H.
          eapply hl_Imp_Lang_assign.
        * eassumption.
      + apply zeroth_impliction.  
      + unfold atrueImp_Lang. unfold aimpImp_Lang.
        unfold param0geqparam0, param0geqparam1.
        unfold true_bool. intros.
        imp_lang_log_inversion.
        a_Imp_Lang_elim.
        imp_lang_log_constructor; rewrite H1.
        * eapply Nat.leb_le. auto.
        * symmetry in H1. eapply Bool.andb_true_eq in H1.
          destruct H1. symmetry in H. assumption.
      (* + apply aimpImp_LangQQ'. *)
    - eapply hl_Imp_Lang_consequence_pre.
      + assert (hl_Imp_Lang (Imp_LangLogSubst.subst_AbsEnv "z" (PARAM_Imp_Lang 1) max_conclusion) (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1)) max_conclusion imp_list fenv).
        {
          unfold max_conclusion. unfold true_bool.
          econstructor.
        }
        eassumption.
      + apply first_implication.
      +  
        apply secondaimpImp_LangP'P.
      (* + apply aimpImp_LangQQ'. *)
  Defined.


End Source. 


Ltac rename_fresh_until_no_match :=
  match goal with
  | [ H: AbsEnv_prop_rel (var_map_wf_wrt_aexp ?map) (var_map_wf_wrt_bexp ?map) ?d |- _ ] =>
      let HWF := fresh "WF" in
      pose proof (HWF := H); clear H; revert HWF; rename_fresh_until_no_match
  | _ => intros
  end.

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

End Tests. 
