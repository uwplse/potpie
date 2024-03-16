From Coq Require Import String List Peano Arith Program.Equality.
From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangHoareWF Imp_LangTrickTactics Imp_LangLogicHelpers LogicPropDec Imp_LangLogPropDec Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import FunctionWellFormed CompilerAssumptionLogicTrans FactEnvTranslator.
From Imp_LangTrick Require Import UIPList.
From Coq.Logic Require Import Eqdep_dec.


(*
 * 
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.

Definition aimp_always_wf (func_list: list fun_Imp_Lang) (idents: list ident) (num_args: nat) (P: AbsEnv) (i: imp_Imp_Lang) (Q: AbsEnv) (fenv: fun_env) (facts : implication_env) (hl: hl_Imp_Lang P i Q facts fenv): Prop :=
  hl_Imp_Lang_wf fenv func_list idents num_args P Q i facts hl.

Ltac inv_aimp_wf :=
  match goal with
  | [ H: aimp_always_wf ?func_list ?idents ?i |- aimp_always_wf ?func_list ?idents ?i' ] =>
      unfold aimp_always_wf in *;
      invs H;
      eassumption
  | [ H: aimp_always_wf ?func_list ?idents ?i |- _ ] =>
      unfold aimp_always_wf in *;
      invs H
  end.

Ltac not_eq := right; intros neq; invs neq.


  

Lemma imp_Imp_Lang_dec :
  forall (i1 i2: imp_Imp_Lang),
    {i1 = i2} + {i1 <> i2}.
Proof.
  induction i1; induction i2; try (left; reflexivity);
    match goal with
    | [ |- { ?l = ?r } + { _ } ] =>
        match l with
        | ?imp_lang_op _ _ _ =>
            match r with
            | imp_lang_op _ _ _ =>
                idtac
            | _ =>
                not_eq; try discrim_neq
            end
        | ?imp_lang_op _ _ =>
            match r with
            | imp_lang_op _ _ =>
                idtac
            | _ =>
                not_eq; try discrim_neq
            end
        | ?imp_lang_op =>
            not_eq; try discrim_neq
        end
    end.
  - pose proof (bexp_Imp_Lang_dec).
    specialize (H b b0).
    specialize (IHi1_1 i2_1).
    specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2, H; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (IHi1 i2).
    pose proof (bexp_Imp_Lang_dec).
    specialize (H b b0).
    destruct IHi1, H; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (string_dec x x0).
    specialize (aexp_Imp_Lang_dec a a0).
    intros.
    destruct H, H0; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (IHi1_1 i2_1).
    specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2; try (subst; left; reflexivity); not_eq; try discrim_neq.
Qed.

Lemma UIP_refl_bexp :
  forall b: bexp_Imp_Lang,
  forall H: b = b,
    H = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ bexp_Imp_Lang_dec b b eq_refl H).
Qed.

Lemma UIP_imp_refl :
  forall (i: imp_Imp_Lang)
    (p: i = i),
    p = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ imp_Imp_Lang_dec i i eq_refl p).
Qed.

(** There is only ever one fenv that we are using. *)
Axiom UIP_fun_env_refl :
  forall (fenv: fun_env)
    (p: fenv = fenv),
    p = eq_refl.

Local Open Scope type_scope.

Lemma UIP_aexp_refl :
  forall (a: aexp_Imp_Lang)
    (p: a = a),
    p = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ aexp_Imp_Lang_dec a a eq_refl p).
Qed.

Lemma UIP_fact_env : 
  forall (fact_env: implication_env)
    (eq1 eq2: fact_env = fact_env), 
    eq1 = eq2.
Proof.
  unfold implication_env. intros fact_env. apply UIP_to_list.
  apply UIP_to_pair. unfold UIP. apply UIP_AbsEnv.
Qed. 

Lemma UIP_fact_env_refl : 
  forall (fact_env: implication_env)
    (eq: fact_env = fact_env), 
    eq = eq_refl.
Proof.
  intros.
  pose proof (UIP_AbsEnv).
  exact (UIP_fact_env fact_env eq (@eq_refl _ fact_env)).
Qed.

Ltac inversion_sigma_helper H :=
  let Heq := fresh "Heq" in
  let Heq_rect := fresh "Heq_rect" in
  inversion_sigma_on_as H ipattern:([Heq Heq_rect ]);
  match goal with
  | [ H' : ?l = ?l |- _ ] =>
      match H' with
      | Heq =>
          let ltype := type of l in
          match ltype with
          | AbsEnv =>
              specialize (UIP_AbsEnv_refl _ Heq)
          | imp_Imp_Lang =>
              specialize (UIP_imp_refl _ Heq)
          | bexp_Imp_Lang =>
              specialize (UIP_refl_bexp _ Heq)
          | aexp_Imp_Lang =>
              specialize (UIP_aexp_refl _ Heq)
          | fun_env =>
              specialize (UIP_fun_env_refl _ Heq)
          | implication_env => 
              specialize (UIP_fact_env_refl _ Heq)
          end;
          intros; subst;
          simpl in *;
          try (inversion_sigma_helper Heq_rect)
      | _ =>
          fail
      end
  end.

Ltac invs_aimpwf_helper H :=
  let Htype := type of H in
  match Htype with
  | aimp_always_wf _ _ _ _ _ _ _ =>
      unfold aimp_always_wf in H
  | _ =>
      idtac
  end;
  invs H;
  try match goal with
    | [ H' : ?l = ?r |- _ ] =>
        let ltype := type of l in
        match ltype with
        | imp_Imp_Lang =>
            match l with
            | ?imp_lang_op _ _ _ =>
                match r with
                | imp_lang_op _ _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?imp_lang_op _ _ =>
                match r with
                | imp_lang_op _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?imp_lang_op =>
                invs H'
            end
        | _ =>
            fail 1
        end
       end;
  try match goal with
      | [ H' : ?p = @eq_rect ?a _ _ _ ?b ?Heq |- _ ] =>
          invs Heq
          ;
            specialize (UIP_imp_refl _ Heq) || specialize (UIP_AbsEnv_refl _ Heq)
          ;
            intros; subst; simpl in *;
          try match goal with
              | [ H'' : ?p = @eq_rect ?a _ _ _ ?b ?Heq' |- _ ] =>
                  invs Heq'
                  ;
                    specialize (UIP_imp_refl _ Heq') || specialize (UIP_AbsEnv_refl _ Heq')
                  ;
                    intros; subst; simpl in *
              end;
          invs H';
          try match goal with
              | [ H' : existT _ _ _ = existT _ _ _ |- _ ] =>
                  inversion_sigma_helper H'
              end;
          try match goal with
              | [ H' : existT _ _ _ = existT _ _ _ |- _ ] =>
                  inversion_sigma_helper H'
              end
      | [ H' : _ =
       hl_Imp_Lang_consequence_pre ?P0 ?Q0 ?P ?Q ?i ?fenv ?hl ?aimp1 ?aimp2 ?last |- _ ] =>
          invs H'
      | [ H' : _ =
        hl_Imp_Lang_consequence_post ?P0 ?Q0 ?P ?Q ?i ?fenv ?hl ?aimp1 ?aimp2 ?last |- _ ] =>
            invs H'
       end;
  simpl in H.
                             
 

Ltac invs_aimpwf_test :=
  match goal with
    | [ H' : ?l = ?r |- _ ] =>
        let ltype := type of l in
        match ltype with
        | imp_Imp_Lang =>
            match l with
            | ?imp_lang_op _ _ _ =>
                match r with
                | imp_lang_op _ _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?imp_lang_op _ _ =>
                match r with
                | imp_lang_op _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?imp_lang_op =>
                invs H'
            end
        | _ => idtac ltype; fail 1
        end
  end.

Lemma imp_lang_log_prop_rel_preserved_by_hl_imp_lang_post :
  forall (P: AbsEnv)  (i: imp_Imp_Lang) (R: AbsEnv) (func_list: list fun_Imp_Lang) (idents: list ident) (num_args: nat) (fenv: fun_env) (facts : implication_env),
  forall (H: hl_Imp_Lang P i R facts fenv),
    aimp_always_wf func_list idents num_args P i R fenv facts H ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) R.
Proof.
  intros.
  invs_aimpwf_helper H0; try eassumption.
  unfold AbsEnv_prop_wf in H3.
  unfold afalseImp_Lang.
  invs H2.
  invs H10.
  destruct H1.
  invs H1.
  econstructor. eassumption. econstructor. econstructor. econstructor. eassumption.
Qed.

Lemma fun_app_well_formed_preserved_by_imp_lang_aexp_update (fenv : fun_env)
      (func_list : list fun_Imp_Lang)
      (a : aexp_Imp_Lang):
  forall (x : ident)
    (a1 : aexp_Imp_Lang)
    (idents : list ident)
    (FUNassign : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (WFupdate : var_map_wf_wrt_aexp idents (imp_lang_aexp_update x a1 a))
    (WFa : var_map_wf_wrt_aexp idents a)
    (FUNa : fun_app_well_formed fenv func_list a),
    fun_app_well_formed fenv func_list (imp_lang_aexp_update x a1 a).
Proof.
  induction a using aexp_Imp_Lang_ind2; intros.
  - simpl. constructor.
  - simpl. invs FUNassign.
    destruct (eqb x x0); assumption.
  - simpl. assumption.
  - simpl. invs FUNa. invs FUNassign. eapply var_map_wf_plus_imp_lang_forwards in WFa. destruct WFa. simpl in WFupdate.
    eapply var_map_wf_plus_imp_lang_forwards in WFupdate.
    destruct WFupdate as (WFupdate1 & WFupdate2).
    constructor; eauto.
  - simpl. invs FUNa. invs FUNassign. eapply var_map_wf_minus_imp_lang_forwards in WFa. destruct WFa. simpl in WFupdate.
    eapply var_map_wf_minus_imp_lang_forwards in WFupdate.
    destruct WFupdate as (WFupdate1 & WFupdate2).
    constructor; eauto.
  - invc FUNa. eapply var_map_wf_app_imp_lang_args_all in WFa. simpl in WFupdate.
    eapply var_map_wf_app_imp_lang_args_all in WFupdate.
    simpl. econstructor; eauto.
    clear H5.
    revert H2. revert WFa. revert WFupdate. induction H; intros.
    + simpl. econstructor; eauto.
    + simpl. simpl in WFupdate. invs WFupdate. invs WFa. invs H2.
      econstructor; eauto.
    + rewrite map_length. assumption.
Qed.

Lemma fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update (fenv : fun_env)
      (func_list : list fun_Imp_Lang)
      (b : bexp_Imp_Lang):
  forall (x : ident)
    (a1 : aexp_Imp_Lang)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WFassign : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (FUNb : fun_app_bexp_well_formed fenv func_list b)
    (WFb : var_map_wf_wrt_bexp idents b)
    (WFupdate : var_map_wf_wrt_bexp idents (imp_lang_bexp_update x a1 b)),
    fun_app_bexp_well_formed fenv func_list (imp_lang_bexp_update x a1 b).
Proof.
  induction b; intros; simpl; invs FUN_APP.
  - constructor.
  - constructor.
  - simpl in *. eapply var_map_wf_neg_imp_lang in WFupdate; eauto.
    eapply var_map_wf_neg_imp_lang in WFb; eauto.
    econstructor. eapply IHb; eauto. invs FUNb. assumption.
  - simpl in *. eapply var_map_wf_and_or_imp_lang_forwards in WFupdate; eauto. destruct WFupdate as (WFupdate1 & WFupdate2).
    eapply var_map_wf_and_or_imp_lang_forwards in WFb; eauto. destruct WFb as (WFb1 & WFb2).
    invc FUNb. rename H4 into FUNb1. rename H5 into FUNb2.
    econstructor; eauto.
  - simpl in *. eapply var_map_wf_and_or_imp_lang_forwards in WFupdate; eauto. destruct WFupdate as (WFupdate1 & WFupdate2).
    eapply var_map_wf_and_or_imp_lang_forwards in WFb; eauto. destruct WFb as (WFb1 & WFb2).
    invc FUNb. rename H4 into FUNb1. rename H5 into FUNb2.
    econstructor; eauto.
  - simpl in *. eapply var_map_wf_leq_imp_lang_forwards in WFupdate; eauto. destruct WFupdate as (WFupdate1 & WFupdate2).
    eapply var_map_wf_leq_imp_lang_forwards in WFb; eauto. destruct WFb as (WFb1 & WFb2).
    invc FUNb. rename H4 into FUNb1. rename H5 into FUNb2.
    invs WFassign.
    econstructor; eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eauto.
Qed.

Lemma lp_aexp_fun_app_well_formed_preserved_by_transformation (fenv : fun_env)
      (func_list : list fun_Imp_Lang)
      (l1: LogicProp nat aexp_Imp_Lang):
  forall (x : ident)
    (a1 : aexp_Imp_Lang)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H5 : prop_rel (var_map_wf_wrt_aexp idents)
                   (transform_prop_exprs l1
                                         (fun a : aexp_Imp_Lang => imp_lang_aexp_update x a1 a)))
    (H3 : prop_rel (var_map_wf_wrt_aexp idents) l1)
    (H2 : prop_rel (fun_app_well_formed fenv func_list) l1),
    prop_rel (fun_app_well_formed fenv func_list)
             (transform_prop_exprs l1 (fun a : aexp_Imp_Lang => imp_lang_aexp_update x a1 a)).
Proof.
  induction l1; intros.
  - constructor.
  - constructor.
  - invc H5. invc H3. invc H2. invs FUN_APP.
    constructor.
    eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eauto.
  - invc H5. invc H3. invc H2. invs FUN_APP. econstructor; eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eauto.
  - invc H5. invc H3. invc H2.
    simpl. constructor; eauto.
  - invc H5. invc H3. invc H2.
    simpl. constructor; eauto.
  - invc H5. invc H3. invc H2. invs FUN_APP. econstructor; eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eauto.
  - invc H5. invc H3. invc H2. econstructor. invs FUN_APP.
    revert H5. revert H3. revert H4. revert H1.
    induction a_list; intros.
    + constructor.
    + invc H1. invc H4. invc H3.
      constructor; eauto.
      eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eauto.
Qed.


Lemma lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation (fenv : fun_env)
      (func_list : list fun_Imp_Lang)
      (l1 : LogicProp bool bexp_Imp_Lang):
  forall (x : ident)
    (a1 : aexp_Imp_Lang)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WFassign : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H2 : prop_rel (var_map_wf_wrt_bexp idents) l1)
    (H4 : prop_rel (var_map_wf_wrt_bexp idents)
                   (transform_prop_exprs l1
                                         (fun b : bexp_Imp_Lang => imp_lang_bexp_update x a1 b)))
    (H6 : prop_rel (fun_app_bexp_well_formed fenv func_list) l1),
    prop_rel (fun_app_bexp_well_formed fenv func_list)
             (transform_prop_exprs l1 (fun b : bexp_Imp_Lang => imp_lang_bexp_update x a1 b)).
Proof.
  induction l1; intros; invc H2; invc H4; invc H6.
  - constructor.
  - constructor.
  - constructor. eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
  - constructor; eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
    all: eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
  - constructor. revert H3. revert H2. revert H1. induction a_list; intros.
    + constructor.
    + invc H1. invc H2. invc H3. constructor; eauto.
      eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
Qed.


Lemma lp_aexp_wf_preserved_by_AbsEnv_subst (fenv : fun_env)
      (func_list : list fun_Imp_Lang)
      (l : LogicProp nat aexp_Imp_Lang):
  forall (x : ident)
    (a1 : aexp_Imp_Lang)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H5 : lp_Imp_Lang_wf func_list fenv (Imp_Lang_lp_arith l))
    (H3 : prop_rel (var_map_wf_wrt_aexp idents)
                   (transform_prop_exprs l
                                         (fun a : aexp_Imp_Lang => imp_lang_aexp_update x a1 a)))
    (H2 : prop_rel (var_map_wf_wrt_aexp idents) l),
    lp_Imp_Lang_wf func_list fenv
              (Imp_LangLogSubst.subst_Imp_Lang_lp x a1 (Imp_Lang_lp_arith l)).
Proof.
  induction l; intros; econstructor; invc H5.
  - econstructor.
  - econstructor.
  - econstructor. invc H3. invc H2. invc H4.
    eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eassumption.
  - simpl.
    invc H3. invc H2. invc H4. econstructor; eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eassumption.
  - simpl. invc H3. invc H2. invc H4.
    econstructor; eauto; eapply lp_aexp_fun_app_well_formed_preserved_by_transformation; eauto.
  - simpl. invc H3. invc H2. invc H4.
    econstructor; eauto; eapply lp_aexp_fun_app_well_formed_preserved_by_transformation; eauto.
  - simpl.
    invc H3. invc H2. invc H4. econstructor; eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eassumption.
  - invc H3. invc H2. invc H4. revert H1 H3 H2.
    constructor.
    induction a_list; intros.
    + constructor.
    + invc H1. invc H2. invc H3. simpl.  constructor.
      * eapply fun_app_well_formed_preserved_by_imp_lang_aexp_update; eauto.
      * eapply IHa_list; eauto.
Qed.

Lemma lp_bexp_wf_preserved_by_AbsEnv_subst (fenv : fun_env)
      (func_list : list fun_Imp_Lang)
      (l : LogicProp bool bexp_Imp_Lang):
  forall (x : ident)
    (a1 : aexp_Imp_Lang)
    (idents : list ident)
    (n_args : nat)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WFassign : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (WFlp : lp_bool_wf func_list fenv l)
    (WFupdate : prop_rel (var_map_wf_wrt_bexp idents)
                   (transform_prop_exprs l
                                         (fun b : bexp_Imp_Lang => imp_lang_bexp_update x a1 b)))
    (WF : prop_rel (var_map_wf_wrt_bexp idents) l),
    lp_Imp_Lang_wf func_list fenv (Imp_LangLogSubst.subst_Imp_Lang_lp x a1 (Imp_Lang_lp_bool l)).
Proof.
  induction l; intros; constructor.
  - constructor.
  - constructor.
  - constructor.
    invc WFlp. invc WF. invc WFupdate.
    rename a into b.
    eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
  - invc WFlp. invc WFupdate. invc WF.
    constructor; eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
  - invc WF. invc WFupdate. invc WFlp. simpl. econstructor; eauto.
    eapply lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation; eassumption.
    eapply lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation; eassumption.
  - invc WFlp. invc WF. invc WFupdate. simpl. constructor; eauto.
    all: eapply lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation; eassumption.
  - invc WFlp. invc WFupdate. invc WF.
    constructor; eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
  - econstructor. invc WF. invc WFlp. invc WFupdate. revert H1 H2 H3.
    induction a_list; intros.
    + constructor.
    + invc H1. invc H2. invc H3.
      simpl; constructor.
      * eapply fun_app_bexp_well_formed_preserved_by_imp_lang_bexp_update; eassumption.
      * eapply IHa_list; eauto.
Qed.

Lemma inv_aimpwf_consequence_pre :
  forall func_list idents n_args P Q P' c fenv n facts hl a imp,
    aimp_always_wf func_list idents n_args P' c Q fenv facts (hl_Imp_Lang_consequence_pre P Q P' c n facts fenv hl a imp) ->
    log_Imp_Lang_wf func_list fenv P /\ log_Imp_Lang_wf func_list fenv Q /\
    log_Imp_Lang_wf func_list fenv P' /\
    log_Imp_Lang_wf_map idents Q /\ 
    log_Imp_Lang_wf_map idents P /\ log_Imp_Lang_wf_map idents P' /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) P /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) Q /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) P' /\
    AbsEnv_prop_rel (all_params_ok_aexp n_args) (all_params_ok_bexp n_args) P /\
    AbsEnv_prop_rel (all_params_ok_aexp n_args) (all_params_ok_bexp n_args) Q /\
    AbsEnv_prop_rel (all_params_ok_aexp n_args) (all_params_ok_bexp n_args) P' /\
    imp_rec_rel (var_map_wf_wrt_imp idents) c /\
    hl_Imp_Lang_wf fenv func_list idents n_args P Q c facts hl.
Proof.
  intros. invs H; invs H0. inversion_sigma_helper H18. intuition.
Qed.

Lemma inv_aimpwf_consequence_post :
  forall func_list idents n_args P Q Q' c fenv n facts hl a imp,
    aimp_always_wf func_list idents n_args P c Q' fenv facts (hl_Imp_Lang_consequence_post P Q Q' c n facts fenv hl a imp) ->
    log_Imp_Lang_wf func_list fenv P /\ log_Imp_Lang_wf func_list fenv Q /\
    log_Imp_Lang_wf func_list fenv Q' /\
    log_Imp_Lang_wf_map idents P /\ 
    log_Imp_Lang_wf_map idents Q /\ log_Imp_Lang_wf_map idents Q' /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) P /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) Q /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) Q' /\
    AbsEnv_prop_rel (all_params_ok_aexp n_args) (all_params_ok_bexp n_args) P /\
    AbsEnv_prop_rel (all_params_ok_aexp n_args) (all_params_ok_bexp n_args) Q /\
    AbsEnv_prop_rel (all_params_ok_aexp n_args) (all_params_ok_bexp n_args) Q' /\
    imp_rec_rel (var_map_wf_wrt_imp idents) c /\
    hl_Imp_Lang_wf fenv func_list idents n_args P Q c facts hl.
Proof.
  intros. invs H; invs H0. inversion_sigma_helper H18. subst. intuition.
Qed.

(* This is a refactoring of specialized automation for efficiency *)
Lemma inv_aimpwf_seq:
  forall i1 i2 P Q R funcs map args facts fenv hl1 hl2,
    aimp_always_wf funcs map args P (i1;; i2) Q fenv facts (hl_Imp_Lang_seq P Q R facts fenv i1 i2 hl1 hl2) ->
    aimp_always_wf funcs map args P i1 R fenv facts hl1 /\
      aimp_always_wf funcs map args R i2 Q fenv facts hl2 /\
      AbsEnv_prop_wf map R.
Proof.
  intros. unfold aimp_always_wf in H. inversion H.
  - inversion HSkip.
  - inversion Heq.
  - invs Heq. specialize (UIP_imp_refl _ Heq).
    intros. subst. simpl in *. invs H0.
    inversion_sigma_helper H18.
    inversion_sigma_helper H19.
    unfold aimp_always_wf. split; try split; try split; assumption.
  - inversion heq.
  - inversion Heq.
  - inversion H0.
  - inversion H0. 
Qed.

(* More opaque lemmas to invert wellformedness *)
Lemma inv_aimpwf_if:
  forall i1 i2 P Q b facts fenv n_args idents func_list hl1 hl2,
    aimp_always_wf func_list idents n_args P (when b then i1 else i2 done) Q fenv facts (hl_Imp_Lang_if P Q b i1 i2 facts fenv hl1 hl2) ->
    aimp_always_wf func_list idents n_args (atrueImp_Lang b P) i1 Q fenv facts hl1 /\
    aimp_always_wf func_list idents n_args (afalseImp_Lang b P) i2 Q fenv facts hl2.
Proof.
  intros. unfold aimp_always_wf in H. inversion H. 
  - inversion HSkip. 
  - inversion Heq.
  - inversion Heq.
  - invs heq. specialize (UIP_imp_refl _ heq).
    intros. subst. simpl in *. invs H0.
    inversion_sigma_helper H13.
    inversion_sigma_helper H14.
    unfold aimp_always_wf. split; assumption.
  - inversion Heq.
  - inversion H0.
  - inversion H0. 
Qed.

Lemma inv_fun_app_when:
  forall i1 i2 b fenv func_list,
    fun_app_imp_well_formed fenv func_list (when b then i1 else i2 done) ->
    fun_app_bexp_well_formed fenv func_list b /\ fun_app_imp_well_formed fenv func_list i1 /\ fun_app_imp_well_formed fenv func_list i2.
Proof.
  intros. invs H. intuition.
Qed.

Lemma inv_imp_rec_rel_when : forall b idents i1 i2,
  imp_rec_rel (var_map_wf_wrt_imp idents) (when b then i1 else i2 done) ->
  imp_rec_rel (var_map_wf_wrt_imp idents) i1 /\ imp_rec_rel (var_map_wf_wrt_imp idents) i2 /\ var_map_wf_wrt_imp idents (when b then i1 else i2 done).
Proof.
  intros. invs H. intuition.
Qed. 


(** Definition to make the following lemmas agnostic to whether the
  * function is afalseImp_Lang/afalsestk or atrueImp_Lang/atruestk. *)
Local Definition isAfalseOrAtrue (afalsetrueImp_Lang: bexp_Imp_Lang -> AbsEnv -> AbsEnv) (afalsetruestk: bexp_stack -> AbsState -> AbsState): Prop :=
  (afalsetrueImp_Lang = afalseImp_Lang /\ afalsetruestk = afalsestk) \/ (afalsetrueImp_Lang = atrueImp_Lang /\ afalsetruestk = atruestk).

Lemma absand_distribution :
  forall (s1 s2 s3: AbsState) (fenv: fun_env_stk) (stk: stack),
    absstate_match_rel
      (AbsAnd (AbsAnd s1 s2) s3) fenv stk <->
      absstate_match_rel (AbsAnd (AbsAnd s1 s3) (AbsAnd s2 s3)) fenv stk.
Proof.
  split; intros; invs H.
  - invs H2. constructor; constructor; auto.
  - invs H2. constructor; auto. constructor; auto.
    invs H5. auto.
Qed.

Lemma absor_distribution :
  forall (s1 s2 s3: AbsState) (fenv: fun_env_stk) (stk: stack),
    absstate_match_rel (AbsAnd (AbsOr s1 s2) s3) fenv stk <->
      absstate_match_rel (AbsOr (AbsAnd s1 s3) (AbsAnd s2 s3)) fenv stk.
Proof.
  split; intros; invs H.
  - invs H2.
    + econstructor; econstructor; eassumption.
    + eapply RelAbsOrRight. econstructor; eassumption.
  - invs H4. econstructor.
    + econstructor. eassumption.
    + eassumption.
  - invs H4. econstructor.
    + eapply RelAbsOrRight. eassumption.
    + eassumption.
Qed.

Lemma absor_dissolution :
  forall (s1 s2: AbsState) (fenv: fun_env_stk) (stk: stack),
    absstate_match_rel (AbsOr s1 s2) fenv stk <->
      (absstate_match_rel s1 fenv stk \/ absstate_match_rel s2 fenv stk).
Proof.
  split; intros; invs H.
  - left. assumption.
  - right. assumption.
  - econstructor. assumption.
  - eapply RelAbsOrRight. assumption.
Qed.

Lemma absand_dissolution :
  forall (s1 s2: AbsState) (fenv: fun_env_stk) (stk: stack),
    absstate_match_rel (AbsAnd s1 s2) fenv stk <->
      (absstate_match_rel s1 fenv stk /\ absstate_match_rel s2 fenv stk).
Proof.
  split; intros; invs H; intuition. constructor; auto.
Qed.

Ltac absand_destruct H :=
  eapply absand_dissolution in H; destruct H.