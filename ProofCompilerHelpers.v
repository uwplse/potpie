From Coq Require Import String List Peano Arith Program.Equality.
From DanTrick Require Import StackLogic DanLogHoare DanTrickLanguage EnvToStack StackLanguage DanLogProp LogicProp StackLangTheorems StackLogicBase.
From DanTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From DanTrick Require Export ProofSubstitution ImpVarMapTheorems DanLogSubstAdequate.
From DanTrick Require Import DanImpHigherOrderRel ProofCompilerBase DanHoareWF DanTrickTactics DanLogicHelpers LogicPropDec DanLogPropDec DanImpHigherOrderRelTheorems.
From DanTrick Require Import FunctionWellFormed CompilerAssumptionLogicTrans.

From Coq.Logic Require Import Eqdep_dec.

(*
 * 
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Definition aimp_always_wf (func_list: list fun_Dan) (idents: list ident) (num_args: nat) (P: AbsEnv) (i: imp_Dan) (Q: AbsEnv) (fenv: fun_env) (hl: hl_Dan P i Q fenv): Prop :=
  hl_Dan_wf fenv func_list idents num_args P Q i hl.

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


  

Lemma imp_Dan_dec :
  forall (i1 i2: imp_Dan),
    {i1 = i2} + {i1 <> i2}.
Proof.
  induction i1; induction i2; try (left; reflexivity);
    match goal with
    | [ |- { ?l = ?r } + { _ } ] =>
        match l with
        | ?dan_op _ _ _ =>
            match r with
            | dan_op _ _ _ =>
                idtac
            | _ =>
                not_eq; try discrim_neq
            end
        | ?dan_op _ _ =>
            match r with
            | dan_op _ _ =>
                idtac
            | _ =>
                not_eq; try discrim_neq
            end
        | ?dan_op =>
            not_eq; try discrim_neq
        end
    end.
  - pose proof (bexp_Dan_dec).
    specialize (H b b0).
    specialize (IHi1_1 i2_1).
    specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2, H; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (IHi1 i2).
    pose proof (bexp_Dan_dec).
    specialize (H b b0).
    destruct IHi1, H; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (string_dec x x0).
    specialize (aexp_Dan_dec a a0).
    intros.
    destruct H, H0; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (IHi1_1 i2_1).
    specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2; try (subst; left; reflexivity); not_eq; try discrim_neq.
Qed.

Lemma UIP_refl_bexp :
  forall b: bexp_Dan,
  forall H: b = b,
    H = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ bexp_Dan_dec b b eq_refl H).
Qed.

Lemma UIP_imp_refl :
  forall (i: imp_Dan)
    (p: i = i),
    p = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ imp_Dan_dec i i eq_refl p).
Qed.

(** There is only ever one fenv that we are using. *)
Axiom UIP_fun_env_refl :
  forall (fenv: fun_env)
    (p: fenv = fenv),
    p = eq_refl.

Local Open Scope type_scope.

Lemma UIP_aexp_refl :
  forall (a: aexp_Dan)
    (p: a = a),
    p = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ aexp_Dan_dec a a eq_refl p).
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
          | imp_Dan =>
              specialize (UIP_imp_refl _ Heq)
          | bexp_Dan =>
              specialize (UIP_refl_bexp _ Heq)
          | aexp_Dan =>
              specialize (UIP_aexp_refl _ Heq)
          | fun_env =>
              specialize (UIP_fun_env_refl _ Heq)
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
        | imp_Dan =>
            match l with
            | ?dan_op _ _ _ =>
                match r with
                | dan_op _ _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?dan_op _ _ =>
                match r with
                | dan_op _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?dan_op =>
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
       hl_Dan_consequence ?P0 ?Q0 ?P ?Q ?i ?fenv ?hl ?aimp1 ?aimp2 |- _ ] =>
          invs H'
       end;
  simpl in H.
                             
 

Ltac invs_aimpwf_test :=
  match goal with
    | [ H' : ?l = ?r |- _ ] =>
        let ltype := type of l in
        match ltype with
        | imp_Dan =>
            match l with
            | ?dan_op _ _ _ =>
                match r with
                | dan_op _ _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?dan_op _ _ =>
                match r with
                | dan_op _ _ =>
                    idtac
                | _ =>
                    invs H'
                end
            | ?dan_op =>
                invs H'
            end
        | _ => fail 1
        end
  end.

Lemma dan_log_prop_rel_preserved_by_hl_dan_post :
  forall (P: AbsEnv)  (i: imp_Dan) (R: AbsEnv) (func_list: list fun_Dan) (idents: list ident) (num_args: nat) (fenv: fun_env),
  forall (H: hl_Dan P i R fenv),
    aimp_always_wf func_list idents num_args P i R fenv H ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) R.
Proof.
  intros.
  invs_aimpwf_helper H0; try eassumption.
  unfold AbsEnv_prop_wf in H3.
  unfold afalseDan.
  invs H2.
  invs H10.
  destruct H1.
  invs H1.
  econstructor. eassumption. econstructor. econstructor. econstructor. eassumption.
Qed.

Lemma fun_app_well_formed_preserved_by_dan_aexp_update (fenv : fun_env)
      (func_list : list fun_Dan)
      (a : aexp_Dan):
  forall (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (FUNassign : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (WFupdate : var_map_wf_wrt_aexp idents (dan_aexp_update x a1 a))
    (WFa : var_map_wf_wrt_aexp idents a)
    (FUNa : fun_app_well_formed fenv func_list a),
    fun_app_well_formed fenv func_list (dan_aexp_update x a1 a).
Proof.
  induction a using aexp_Dan_ind2; intros.
  - simpl. constructor.
  - simpl. invs FUNassign.
    destruct (eqb x x0); assumption.
  - simpl. assumption.
  - simpl. invs FUNa. invs FUNassign. eapply var_map_wf_plus_dan_forwards in WFa. destruct WFa. simpl in WFupdate.
    eapply var_map_wf_plus_dan_forwards in WFupdate.
    destruct WFupdate as (WFupdate1 & WFupdate2).
    constructor; eauto.
  - simpl. invs FUNa. invs FUNassign. eapply var_map_wf_minus_dan_forwards in WFa. destruct WFa. simpl in WFupdate.
    eapply var_map_wf_minus_dan_forwards in WFupdate.
    destruct WFupdate as (WFupdate1 & WFupdate2).
    constructor; eauto.
  - invc FUNa. eapply var_map_wf_app_dan_args_all in WFa. simpl in WFupdate.
    eapply var_map_wf_app_dan_args_all in WFupdate.
    simpl. econstructor; eauto.
    clear H5.
    revert H2. revert WFa. revert WFupdate. induction H; intros.
    + simpl. econstructor; eauto.
    + simpl. simpl in WFupdate. invs WFupdate. invs WFa. invs H2.
      econstructor; eauto.
    + rewrite map_length. assumption.
Qed.

Lemma fun_app_bexp_well_formed_preserved_by_dan_bexp_update (fenv : fun_env)
      (func_list : list fun_Dan)
      (b : bexp_Dan):
  forall (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WFassign : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (FUNb : fun_app_bexp_well_formed fenv func_list b)
    (WFb : var_map_wf_wrt_bexp idents b)
    (WFupdate : var_map_wf_wrt_bexp idents (dan_bexp_update x a1 b)),
    fun_app_bexp_well_formed fenv func_list (dan_bexp_update x a1 b).
Proof.
  induction b; intros; simpl; invs FUN_APP.
  - constructor.
  - constructor.
  - simpl in *. eapply var_map_wf_neg_dan in WFupdate; eauto.
    eapply var_map_wf_neg_dan in WFb; eauto.
    econstructor. eapply IHb; eauto. invs FUNb. assumption.
  - simpl in *. eapply var_map_wf_and_or_dan_forwards in WFupdate; eauto. destruct WFupdate as (WFupdate1 & WFupdate2).
    eapply var_map_wf_and_or_dan_forwards in WFb; eauto. destruct WFb as (WFb1 & WFb2).
    invc FUNb. rename H4 into FUNb1. rename H5 into FUNb2.
    econstructor; eauto.
  - simpl in *. eapply var_map_wf_and_or_dan_forwards in WFupdate; eauto. destruct WFupdate as (WFupdate1 & WFupdate2).
    eapply var_map_wf_and_or_dan_forwards in WFb; eauto. destruct WFb as (WFb1 & WFb2).
    invc FUNb. rename H4 into FUNb1. rename H5 into FUNb2.
    econstructor; eauto.
  - simpl in *. eapply var_map_wf_leq_dan_forwards in WFupdate; eauto. destruct WFupdate as (WFupdate1 & WFupdate2).
    eapply var_map_wf_leq_dan_forwards in WFb; eauto. destruct WFb as (WFb1 & WFb2).
    invc FUNb. rename H4 into FUNb1. rename H5 into FUNb2.
    invs WFassign.
    econstructor; eapply fun_app_well_formed_preserved_by_dan_aexp_update; eauto.
Qed.

Lemma lp_aexp_fun_app_well_formed_preserved_by_transformation (fenv : fun_env)
      (func_list : list fun_Dan)
      (l1: LogicProp nat aexp_Dan):
  forall (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H5 : prop_rel (var_map_wf_wrt_aexp idents)
                   (transform_prop_exprs l1
                                         (fun a : aexp_Dan => dan_aexp_update x a1 a)))
    (H3 : prop_rel (var_map_wf_wrt_aexp idents) l1)
    (H2 : prop_rel (fun_app_well_formed fenv func_list) l1),
    prop_rel (fun_app_well_formed fenv func_list)
             (transform_prop_exprs l1 (fun a : aexp_Dan => dan_aexp_update x a1 a)).
Proof.
  induction l1; intros.
  - constructor.
  - constructor.
  - invc H5. invc H3. invc H2. invs FUN_APP.
    constructor.
    eapply fun_app_well_formed_preserved_by_dan_aexp_update; eauto.
  - invc H5. invc H3. invc H2. invs FUN_APP. econstructor; eapply fun_app_well_formed_preserved_by_dan_aexp_update; eauto.
  - invc H5. invc H3. invc H2.
    simpl. constructor; eauto.
  - invc H5. invc H3. invc H2.
    simpl. constructor; eauto.
  - invc H5. invc H3. invc H2. invs FUN_APP. econstructor; eapply fun_app_well_formed_preserved_by_dan_aexp_update; eauto.
  - invc H5. invc H3. invc H2. econstructor. invs FUN_APP.
    revert H5. revert H3. revert H4. revert H1.
    induction a_list; intros.
    + constructor.
    + invc H1. invc H4. invc H3.
      constructor; eauto.
      eapply fun_app_well_formed_preserved_by_dan_aexp_update; eauto.
Qed.


Lemma lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation (fenv : fun_env)
      (func_list : list fun_Dan)
      (l1 : LogicProp bool bexp_Dan):
  forall (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WFassign : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H2 : prop_rel (var_map_wf_wrt_bexp idents) l1)
    (H4 : prop_rel (var_map_wf_wrt_bexp idents)
                   (transform_prop_exprs l1
                                         (fun b : bexp_Dan => dan_bexp_update x a1 b)))
    (H6 : prop_rel (fun_app_bexp_well_formed fenv func_list) l1),
    prop_rel (fun_app_bexp_well_formed fenv func_list)
             (transform_prop_exprs l1 (fun b : bexp_Dan => dan_bexp_update x a1 b)).
Proof.
  induction l1; intros; invc H2; invc H4; invc H6.
  - constructor.
  - constructor.
  - constructor. eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
  - constructor; eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
    all: eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
  - constructor. revert H3. revert H2. revert H1. induction a_list; intros.
    + constructor.
    + invc H1. invc H2. invc H3. constructor; eauto.
      eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
Qed.


Lemma lp_aexp_wf_preserved_by_AbsEnv_subst (fenv : fun_env)
      (func_list : list fun_Dan)
      (l : LogicProp nat aexp_Dan):
  forall (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H5 : lp_Dan_wf func_list fenv (Dan_lp_arith l))
    (H3 : prop_rel (var_map_wf_wrt_aexp idents)
                   (transform_prop_exprs l
                                         (fun a : aexp_Dan => dan_aexp_update x a1 a)))
    (H2 : prop_rel (var_map_wf_wrt_aexp idents) l),
    lp_Dan_wf func_list fenv
              (DanLogSubst.subst_Dan_lp x a1 (Dan_lp_arith l)).
Proof.
  induction l; intros; econstructor; invc H5.
  - econstructor.
  - econstructor.
  - econstructor. invc H3. invc H2. invc H4.
    eapply fun_app_well_formed_preserved_by_dan_aexp_update; eassumption.
  - simpl.
    invc H3. invc H2. invc H4. econstructor; eapply fun_app_well_formed_preserved_by_dan_aexp_update; eassumption.
  - simpl. invc H3. invc H2. invc H4.
    econstructor; eauto; eapply lp_aexp_fun_app_well_formed_preserved_by_transformation; eauto.
  - simpl. invc H3. invc H2. invc H4.
    econstructor; eauto; eapply lp_aexp_fun_app_well_formed_preserved_by_transformation; eauto.
  - simpl.
    invc H3. invc H2. invc H4. econstructor; eapply fun_app_well_formed_preserved_by_dan_aexp_update; eassumption.
  - invc H3. invc H2. invc H4. revert H1 H3 H2.
    constructor.
    induction a_list; intros.
    + constructor.
    + invc H1. invc H2. invc H3. simpl.  constructor.
      * eapply fun_app_well_formed_preserved_by_dan_aexp_update; eauto.
      * eapply IHa_list; eauto.
Qed.

Lemma lp_bexp_wf_preserved_by_AbsEnv_subst (fenv : fun_env)
      (func_list : list fun_Dan)
      (l : LogicProp bool bexp_Dan):
  forall (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (n_args : nat)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (WFassign : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (WFlp : lp_bool_wf func_list fenv l)
    (WFupdate : prop_rel (var_map_wf_wrt_bexp idents)
                   (transform_prop_exprs l
                                         (fun b : bexp_Dan => dan_bexp_update x a1 b)))
    (WF : prop_rel (var_map_wf_wrt_bexp idents) l),
    lp_Dan_wf func_list fenv (DanLogSubst.subst_Dan_lp x a1 (Dan_lp_bool l)).
Proof.
  induction l; intros; constructor.
  - constructor.
  - constructor.
  - constructor.
    invc WFlp. invc WF. invc WFupdate.
    rename a into b.
    eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
  - invc WFlp. invc WFupdate. invc WF.
    constructor; eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
  - invc WF. invc WFupdate. invc WFlp. simpl. econstructor; eauto.
    eapply lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation; eassumption.
    eapply lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation; eassumption.
  - invc WFlp. invc WF. invc WFupdate. simpl. constructor; eauto.
    all: eapply lp_bexp_fun_app_bexp_well_formed_preserved_by_transformation; eassumption.
  - invc WFlp. invc WFupdate. invc WF.
    constructor; eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
  - econstructor. invc WF. invc WFlp. invc WFupdate. revert H1 H2 H3.
    induction a_list; intros.
    + constructor.
    + invc H1. invc H2. invc H3.
      simpl; constructor.
      * eapply fun_app_bexp_well_formed_preserved_by_dan_bexp_update; eassumption.
      * eapply IHa_list; eauto.
Qed.
 

Lemma lp_Dan_wf_preserved_by_AbsEnv_subst (fenv : fun_env)
      (func_list : list fun_Dan)
      (s : Dan_lp):
  forall 
    (x : ident)
    (a1 : aexp_Dan)
    (idents : list ident)
    (n_args : nat)
    (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
    (s0 : MetavarPred)
    (WF' : var_map_wf_wrt_imp idents (x <- a1))
    (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
    (H11 : log_Dan_wf func_list fenv (AbsEnvLP s))
    (H3 : lp_transrelation n_args idents (DanLogSubst.subst_Dan_lp x a1 s) s0)
    (H2 : Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                          (var_map_wf_wrt_bexp idents) (DanLogSubst.subst_Dan_lp x a1 s))
    (H4 : Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                          (var_map_wf_wrt_bexp idents) s),
    lp_Dan_wf func_list fenv (DanLogSubst.subst_Dan_lp x a1 s).
Proof.
  destruct s; intros.
  - invc H11. invc H3. invc H2. invc H4.
    eapply lp_aexp_wf_preserved_by_AbsEnv_subst; eassumption.
  - invc H11. invc H3. invc H2. invc H4. invc H5. clear H6.
    eapply lp_bexp_wf_preserved_by_AbsEnv_subst; eassumption.
Qed.

Lemma log_Dan_wf_preserved_by_AbsEnv_subst (fenv: fun_env) (func_list: list fun_Dan)
      (Q': AbsEnv):
  forall 
      (x: ident)
      (a1: aexp_Dan)
      (idents: list ident)
      (n_args: nat)
      (s1: AbsState)
      (FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a1))
      (H1 : logic_transrelation
              n_args idents
              (DanLogSubst.subst_AbsEnv x a1 Q') s1)
      (H4 : AbsEnv_prop_rel
              (var_map_wf_wrt_aexp idents)
              (var_map_wf_wrt_bexp idents)
              (DanLogSubst.subst_AbsEnv x a1 Q'))
      (H5 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
                             (var_map_wf_wrt_bexp idents) Q')
      (WF' : var_map_wf_wrt_imp idents (x <- a1))
      (WF : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a1))
      (H11 : log_Dan_wf func_list fenv Q'),
  log_Dan_wf func_list fenv (DanLogSubst.subst_AbsEnv x a1 Q').
Proof.
  induction Q'; intros.
  - econstructor.
    invc H1. invc H4. invc H5.
    eapply lp_Dan_wf_preserved_by_AbsEnv_subst; eassumption.
  - invc H1. invc H4. invc H5. invc H11. simpl. constructor. 
    + eapply IHQ'1; eassumption.
    + eapply IHQ'2; eassumption.   
  - simpl. invc H1. invc H4. invc H5. invc H11. simpl. constructor.
    + eapply IHQ'1; eassumption.
    + eapply IHQ'2; eassumption.   
Qed.

Lemma inv_aimpwf_consequence :
  forall func_list idents n_args P Q P' Q' c fenv hl a a0,
    aimp_always_wf func_list idents n_args P' c Q' fenv (hl_Dan_consequence P Q P' Q' c fenv hl a a0) ->
    log_Dan_wf func_list fenv P /\ log_Dan_wf func_list fenv Q /\
    log_Dan_wf func_list fenv P' /\ log_Dan_wf func_list fenv Q' /\
    log_Dan_wf_map idents Q /\ log_Dan_wf_map idents Q' /\
    log_Dan_wf_map idents P /\ log_Dan_wf_map idents P' /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) P /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) Q /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) P' /\
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) Q' /\
    hl_Dan_wf fenv func_list idents n_args P Q c hl.
Proof.
  intros. invs H; invs H0. inversion_sigma_helper H22. subst. intuition.
Qed.

(* This is a refactoring of specialized automation for efficiency *)
Lemma inv_aimpwf_seq:
  forall i1 i2 P Q R funcs map args fenv hl1 hl2,
    aimp_always_wf funcs map args P (i1;; i2) Q fenv (hl_Dan_seq P Q R i1 i2 fenv hl1 hl2) ->
    aimp_always_wf funcs map args P i1 R fenv hl1 /\
      aimp_always_wf funcs map args R i2 Q fenv hl2 /\
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
Qed.

(* More opaque lemmas to invert wellformedness *)
Lemma inv_aimpwf_if:
  forall i1 i2 P Q b fenv n_args idents func_list hl1 hl2,
    aimp_always_wf func_list idents n_args P (when b then i1 else i2 done) Q fenv (hl_Dan_if P Q b i1 i2 fenv hl1 hl2) ->
    aimp_always_wf func_list idents n_args (atrueDan b P) i1 Q fenv hl1 /\
    aimp_always_wf func_list idents n_args (afalseDan b P) i2 Q fenv hl2.
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

(* Had to split this definition to find the culprit for inefficiency *)
Definition hl_Dan_implication_2 (P : AbsEnv)
(fenv : fun_env)
(x : string)
(a : aexp_Dan)
(func_list : list fun_Dan)
(n_args : nat)
(idents : list ident)
(AIMPWF : aimp_always_wf func_list idents n_args
           (DanLogSubst.subst_AbsEnv x a P) 
           (x <- a) P fenv (hl_Dan_assign P fenv x a))
(s1 s2 : AbsState)
(i' : imp_stack)
(fenv' : fun_env_stk)
(OKfuncs : funcs_okay_too func_list fenv')
(OKparams : Forall
             (fun func : fun_Dan =>
              all_params_ok (DanTrickLanguage.Args func)
                (DanTrickLanguage.Body func)) func_list)
(FENV_WF : fenv_well_formed' func_list fenv)
(FUN_APP : fun_app_imp_well_formed fenv func_list (x <- a))
(GENESYS : terminator fenv n_args
            (DanLogSubst.subst_AbsEnv x a P) P 
            (x <- a) (hl_Dan_assign P fenv x a))
(H : i' =
    compile_imp (x <- a) (ident_list_to_map idents)
      (Datatypes.length idents))
(H0 : fenv' = compile_fenv fenv)
(H1 : logic_transrelation n_args idents
       (DanLogSubst.subst_AbsEnv x a P) s1)
(H2 : logic_transrelation n_args idents P s2)
(H3 : imp_rec_rel (var_map_wf_wrt_imp idents) (x <- a))
(H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents)
       (DanLogSubst.subst_AbsEnv x a P))
(H5 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) P)
: 
hl_stk s1 i' s2 fenv'.
Proof.
pose proof (WF := H3). clear H3.
    eapply imp_rec_rel_var_map_wf_adequacy in WF.  unfold var_map_wf_wrt_imp in WF. 


destruct WF as (WF1 & WF2 & WF3).
    eapply imp_Dan_wf_inversion_assign in WF2.
    eapply logic_transrelation_substitution in H2; [ | eapply H1 | | | eapply WF2 | .. ]; try eassumption; try ereflexivity.
    subst.
    econstructor.
    + remember_all. unfold ident_list_to_map in HeqARG0. eapply comp_aexp_implies_pure' in HeqARG0.
      * eassumption.
      * eassumption.
      * invs FUN_APP.
        eassumption.
      * assumption.
      * assumption.
      * eassumption.
    + eassumption.
    + eapply dan_log_subst_adequacy.
      reflexivity.
    + eapply WF3. econstructor. eapply String.eqb_eq. reflexivity.
Defined.

Definition hl_Dan_implication_3 (P Q R : AbsEnv)
(i1 i2 : imp_Dan)
fenv
(hl1 : hl_Dan P i1 R fenv)
(hl2 : hl_Dan R i2 Q fenv)
(IHhl1 : forall (func_list : list fun_Dan)
          (n_args : nat)
          (idents : list ident),
        aimp_always_wf func_list idents
          n_args P i1 R fenv hl1 ->
        forall (s1 s2 : AbsState)
          (i' : imp_stack)
          (fenv' : fun_env_stk),
        funcs_okay_too func_list fenv' ->
        Forall
          (fun func : fun_Dan =>
           all_params_ok
             (DanTrickLanguage.Args func)
             (DanTrickLanguage.Body func))
          func_list ->
        fenv_well_formed' func_list fenv ->
        fun_app_imp_well_formed fenv
          func_list i1 ->
        terminator fenv n_args P R i1 hl1 ->
        i' = comp_code i1 idents n_args ->
        fenv' = compile_fenv fenv ->
        logic_transrelation n_args idents P
          s1 ->
        logic_transrelation n_args idents R
          s2 ->
        imp_rec_rel
          (var_map_wf_wrt_imp idents) i1 ->
        AbsEnv_prop_rel
          (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) P ->
        AbsEnv_prop_rel
          (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) R ->
        hl_stk s1 i' s2 fenv')
(IHhl2 : forall (func_list : list fun_Dan)
          (n_args : nat)
          (idents : list ident),
        aimp_always_wf func_list idents
          n_args R i2 Q fenv hl2 ->
        forall (s1 s2 : AbsState)
          (i' : imp_stack)
          (fenv' : fun_env_stk),
        funcs_okay_too func_list fenv' ->
        Forall
          (fun func : fun_Dan =>
           all_params_ok
             (DanTrickLanguage.Args func)
             (DanTrickLanguage.Body func))
          func_list ->
        fenv_well_formed' func_list fenv ->
        fun_app_imp_well_formed fenv
          func_list i2 ->
        terminator fenv n_args R Q i2 hl2 ->
        i' = comp_code i2 idents n_args ->
        fenv' = compile_fenv fenv ->
        logic_transrelation n_args idents R
          s1 ->
        logic_transrelation n_args idents Q
          s2 ->
        imp_rec_rel
          (var_map_wf_wrt_imp idents) i2 ->
        AbsEnv_prop_rel
          (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) R ->
        AbsEnv_prop_rel
          (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) Q ->
        hl_stk s1 i' s2 fenv')
func_list
n_args
idents
(AIMPWF : aimp_always_wf func_list idents
           n_args P (i1;; i2) Q fenv
           (hl_Dan_seq P Q R i1 i2 fenv hl1
              hl2))
(s1 s2 : AbsState)
(i' : imp_stack)
fenv'
(OKfuncs : funcs_okay_too func_list fenv')
(OKparams : Forall
             (fun func : fun_Dan =>
              all_params_ok
                (DanTrickLanguage.Args func)
                (DanTrickLanguage.Body func))
             func_list)
(FENV_WF : fenv_well_formed' func_list fenv)
(FUN_APP : fun_app_imp_well_formed fenv
            func_list (i1;; i2))
(GENESYS : terminator fenv n_args P Q
            (i1;; i2)
            (hl_Dan_seq P Q R i1 i2 fenv hl1
               hl2))
(H : i' =
    compile_imp (i1;; i2)
      (ident_list_to_map idents)
      (Datatypes.length idents))
(H0 : fenv' = compile_fenv fenv)
(H1 : logic_transrelation n_args idents P s1)
(H2 : logic_transrelation n_args idents Q s2)
(H3 : imp_rec_rel (var_map_wf_wrt_imp idents)
       (i1;; i2))
(H4 : AbsEnv_prop_rel
       (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) P)
(H5 : AbsEnv_prop_rel
       (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) Q):
hl_stk s1 i' s2 fenv'.
Proof.
simpl in H. rewrite H.
   apply inv_aimpwf_seq in AIMPWF.
    econstructor.
    - eapply IHhl1; try solve [ eassumption
            | ereflexivity
            | invs FUN_APP; eassumption
            | eassumption
            | eapply log_comp_adequacy; ereflexivity
            | invs H3; eassumption ].
      + apply (proj1 AIMPWF).
      + simpl in GENESYS. apply (proj1 GENESYS).
      + simpl in GENESYS. intuition. 
    - eapply IHhl2; try solve [ eassumption
            | ereflexivity
            | invs FUN_APP; eassumption
            | eassumption
            | eapply log_comp_adequacy; ereflexivity
            | invs H3; eassumption ].
      + apply (proj2 AIMPWF).
      + simpl in GENESYS. apply (proj1 (proj2 GENESYS)).
      + simpl in GENESYS. intuition. 
Defined.

Definition hl_Dan_implication_4 (P Q : AbsEnv)
(b : bexp_Dan)
(i1 i2 : imp_Dan)
fenv
(hl1 : hl_Dan (atrueDan b P) i1 Q fenv)
(hl2 : hl_Dan (afalseDan b P) i2 Q fenv)
(IHhl1 : forall (func_list : list fun_Dan) (n_args : nat)
          (idents : list ident),
        aimp_always_wf func_list idents n_args 
          (atrueDan b P) i1 Q fenv hl1 ->
        forall (s1 s2 : AbsState) (i' : imp_stack)
          (fenv' : fun_env_stk),
        funcs_okay_too func_list fenv' ->
        Forall
          (fun func : fun_Dan =>
           all_params_ok (DanTrickLanguage.Args func)
             (DanTrickLanguage.Body func)) func_list ->
        fenv_well_formed' func_list fenv ->
        fun_app_imp_well_formed fenv func_list i1 ->
        terminator fenv n_args (atrueDan b P) Q i1 hl1 ->
        i' = comp_code i1 idents n_args ->
        fenv' = compile_fenv fenv ->
        logic_transrelation n_args idents (atrueDan b P) s1 ->
        logic_transrelation n_args idents Q s2 ->
        imp_rec_rel (var_map_wf_wrt_imp idents) i1 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) (atrueDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) Q -> hl_stk s1 i' s2 fenv')
(IHhl2 : forall (func_list : list fun_Dan) (n_args : nat)
          (idents : list ident),
        aimp_always_wf func_list idents n_args 
          (afalseDan b P) i2 Q fenv hl2 ->
        forall (s1 s2 : AbsState) (i' : imp_stack)
          (fenv' : fun_env_stk),
        funcs_okay_too func_list fenv' ->
        Forall
          (fun func : fun_Dan =>
           all_params_ok (DanTrickLanguage.Args func)
             (DanTrickLanguage.Body func)) func_list ->
        fenv_well_formed' func_list fenv ->
        fun_app_imp_well_formed fenv func_list i2 ->
        terminator fenv n_args (afalseDan b P) Q i2 hl2 ->
        i' = comp_code i2 idents n_args ->
        fenv' = compile_fenv fenv ->
        logic_transrelation n_args idents (afalseDan b P) s1 ->
        logic_transrelation n_args idents Q s2 ->
        imp_rec_rel (var_map_wf_wrt_imp idents) i2 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) (afalseDan b P) ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
          (var_map_wf_wrt_bexp idents) Q -> hl_stk s1 i' s2 fenv')
func_list
n_args
idents
(AIMPWF : aimp_always_wf func_list idents n_args P
           (when b then i1 else i2 done) Q fenv
           (hl_Dan_if P Q b i1 i2 fenv hl1 hl2))
s1 s2 i' fenv'
(OKfuncs : funcs_okay_too func_list fenv')
(OKparams : Forall
             (fun func : fun_Dan =>
              all_params_ok (DanTrickLanguage.Args func)
                (DanTrickLanguage.Body func)) func_list)
(FENV_WF : fenv_well_formed' func_list fenv)
(FUN_APP : fun_app_imp_well_formed fenv func_list
            (when b then i1 else i2 done))
(GENESYS : terminator fenv n_args P Q (when b then i1 else i2 done)
            (hl_Dan_if P Q b i1 i2 fenv hl1 hl2))
(H : i' =
    compile_imp (when b then i1 else i2 done)
      (ident_list_to_map idents) (Datatypes.length idents))
(H0 : fenv' = compile_fenv fenv)
(H1 : logic_transrelation n_args idents P s1)
(H2 : logic_transrelation n_args idents Q s2)
(H3 : imp_rec_rel (var_map_wf_wrt_imp idents)
       (when b then i1 else i2 done))
(H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) P)
(H5 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) Q)
:
hl_stk s1 i' s2 fenv'.
Proof.
subst. simpl. apply inv_aimpwf_if in AIMPWF. apply inv_fun_app_when in FUN_APP. apply inv_imp_rec_rel_when in H3.
    econstructor.
    + eapply comp_bexp_implies_pure'.
      ereflexivity. eassumption. eassumption.
      eassumption. apply (proj1 FUN_APP).
      reflexivity.
    + eapply Hoare_Stk_consequence_pre.
      * simpl in GENESYS. eapply (IHhl1 _ _ _ (proj1 AIMPWF)); auto.
        -- apply (proj1 (proj2 FUN_APP)).
        -- apply (proj1 GENESYS). 
        -- eapply log_comp_adequacy. ereflexivity.
        -- apply (proj1 H3).
        -- apply proj2 in H3. apply proj2 in H3. unfold_wf_imp_in H3. invs WF'.
           econstructor.
           ++ assumption.
           ++ econstructor. econstructor. econstructor.
              assumption.
      * simpl.
        assert (s1 = comp_logic n_args idents P).
        {
          symmetry.
          eapply log_comp_adequacy. assumption.
        } 
        remember_all.
        rewrite HeqARG0. rewrite <- H.
        unfold aimpstk.
        intros.
        rewrite HeqARG1 in H0. inversion_clear H0.
        econstructor.
        -- assumption.
        -- pose proof (IMP:= hl_dan_implication_helper).
           unfold aimpstk in IMP. rewrite Nat.add_comm. unfold comp_bool.
           rewrite HeqARG.
           eapply IMP.
           ++ eapply H1.
           ++ ereflexivity.
           ++ econstructor.
              rewrite HeqARG in H6. eassumption.
              rewrite HeqARG in H7. eassumption.
    + eapply Hoare_Stk_consequence_pre.
      pose proof (WF := H3); clear H3.
      * eapply IHhl2; 
          try solve [ apply (proj2 AIMPWF) | eassumption
            | ereflexivity
            | eassumption
            | eapply log_comp_adequacy; ereflexivity ].
        apply (proj2 (proj2 FUN_APP)). simpl in GENESYS; intuition. apply (proj1 (proj2 WF)).
        econstructor. assumption.
        constructor. constructor. constructor.
        apply proj2 in WF. apply proj2 in WF.
        unfold_wf_imp_in WF. invs WF'. assumption.
      * unfold afalsestk, aimpstk, afalseDan. simpl.
        assert (comp_logic n_args idents P = s1) by (eapply log_comp_adequacy; assumption).
        symmetry in H.
        rewrite <- H.
        intros stk.
        intros.
        econstructor.
        -- invs H0. eassumption.
        -- revert H0. revert stk. unfold comp_bool.
           fold (aimpstk (AbsAnd s1
                                 (BaseState AbsStkTrue
                                            (MetaBool
                                               (UnaryProp bool bexp_stack (fun bval : bool => bval = false)
                                                          (compile_bexp b (ident_list_to_map idents)
                                                                        (Datatypes.length idents + n_args))))))
                         (BaseState (AbsStkSize (n_args + Datatypes.length idents))
                                    (MetaBool
                                       (UnaryProp bool bexp_stack (fun bval : bool => bval = false)
                                                  (compile_bexp b
                                                                (fun x : DanTrickLanguage.ident => one_index_opt x idents)
                                                                (Datatypes.length idents + n_args))))) (compile_fenv fenv)).
        
           intros.
           pose proof (IMP := hl_dan_implication_helper).
           unfold aimpstk in IMP.
           rewrite Nat.add_comm.
           eapply IMP. eapply H1. ereflexivity. eassumption.
Defined.

Definition hl_Dan_implication_5 (P : AbsEnv) b i fenv
(hl : hl_Dan (atrueDan b P) i P fenv)
(IHhl : forall (func_list : list fun_Dan) (n_args : nat)
         (idents : list ident),
       aimp_always_wf func_list idents n_args 
         (atrueDan b P) i P fenv hl ->
       forall (s1 s2 : AbsState) (i' : imp_stack)
         (fenv' : fun_env_stk),
       funcs_okay_too func_list fenv' ->
       Forall
         (fun func : fun_Dan =>
          all_params_ok (DanTrickLanguage.Args func)
            (DanTrickLanguage.Body func)) func_list ->
       fenv_well_formed' func_list fenv ->
       fun_app_imp_well_formed fenv func_list i ->
       terminator fenv n_args (atrueDan b P) P i hl ->
       i' = comp_code i idents n_args ->
       fenv' = compile_fenv fenv ->
       logic_transrelation n_args idents (atrueDan b P) s1 ->
       logic_transrelation n_args idents P s2 ->
       imp_rec_rel (var_map_wf_wrt_imp idents) i ->
       AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
         (var_map_wf_wrt_bexp idents) (atrueDan b P) ->
       AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
         (var_map_wf_wrt_bexp idents) P -> hl_stk s1 i' s2 fenv')
func_list
n_args
idents
(AIMPWF : aimp_always_wf func_list idents n_args P
           (while b loop i done) (afalseDan b P) fenv
           (hl_Dan_while P b i fenv hl))
s1 s2 i' fenv'
(OKfuncs : funcs_okay_too func_list fenv')
(OKparams : Forall
             (fun func : fun_Dan =>
              all_params_ok (DanTrickLanguage.Args func)
                (DanTrickLanguage.Body func)) func_list)
(FENV_WF : fenv_well_formed' func_list fenv)
(FUN_APP : fun_app_imp_well_formed fenv func_list
            (while b loop i done))
(GENESYS : terminator fenv n_args P (afalseDan b P)
            (while b loop i done) (hl_Dan_while P b i fenv hl))
(H : i' =
    compile_imp (while b loop i done) (ident_list_to_map idents)
      (Datatypes.length idents))
(H0 : fenv' = compile_fenv fenv)
(H1 : logic_transrelation n_args idents P s1)
(H2 : logic_transrelation n_args idents (afalseDan b P) s2)
(H3 : imp_rec_rel (var_map_wf_wrt_imp idents) (while b loop i done))
(H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) P)
(H5 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) (afalseDan b P))
:
hl_stk s1 i' s2 fenv'.
Proof.
subst.
    unfold comp_code. simpl.
    econstructor.
    + eapply hl_stk_while.
      * remember_all.
        invs FUN_APP.
        eapply comp_bexp_implies_pure'; eauto. reflexivity.
      * assert (logic_transrelation n_args idents (atrueDan b P) (comp_logic n_args idents (atrueDan b P))).
        -- eapply log_comp_adequacy.
           reflexivity.
        -- pose proof (WF := H3); clear H3.
           
           eapply IHhl with
             (s1 := comp_logic n_args idents (atrueDan b P)) (s2 := s1) (i' := compile_imp i (ident_list_to_map idents) (Datatypes.length idents)) in H;
             try solve [ eassumption | invs FUN_APP; eassumption | ereflexivity | invs WF; eassumption ].
             eapply hl_stk_consequence.
             ++ eassumption.
             ++ unfold aimpstk. intros. unfold atruestk, atrueDan in *.
                simpl.
                pose proof (IMP := hl_dan_implication_helper).
                unfold aimpstk in IMP.
                unfold ident_list_to_map in IMP.
                rewrite Nat.add_comm.
                invs H0.
                econstructor.
                ** eapply H7.
                ** eapply IMP.
                   eapply H1. ereflexivity.
                   econstructor.
                   --- assert (comp_logic n_args idents P = s1).
                       eapply log_comp_adequacy.
                       assumption.
                       rewrite <- H3.
                       assumption.
                   --- assumption.
             ++ assert (comp_logic n_args idents P = s1) by (eapply log_comp_adequacy; assumption).
                rewrite <- H0. unfold aimpstk.
                intros; eassumption.
            ++ unfold aimp_always_wf; invs_aimpwf_helper AIMPWF; eassumption.
            ++ simpl in GENESYS; intuition.
            ++  unfold atrueDan; econstructor; [ eassumption | econstructor; econstructor; econstructor; invs WF; unfold_wf_imp_in H8; invs WF'; eassumption ].
    + assert (comp_logic n_args idents P = s1) by (eapply log_comp_adequacy; assumption).
      unfold aimpstk.
      rewrite <- H.
      intros; eassumption.
    + unfold afalsestk.
      assert (comp_logic n_args idents (afalseDan b P) = s2) by (eapply log_comp_adequacy; eassumption).
      rewrite <- H.
      unfold aimpstk, afalseDan.
      simpl.
      intros.
      pose proof (IMP := hl_dan_implication_helper).
      unfold aimpstk in IMP.
      rewrite Nat.add_comm.
      econstructor.
      invs H0.
      assumption.
      eapply IMP.
      eapply H1.
      ereflexivity.
      assert (comp_logic n_args idents P = s1) by (eapply log_comp_adequacy; eassumption).
      rewrite <- H6. assumption.
Defined.

Definition hl_Dan_implication_6_1 P Q P' Q' c fenv
(hl : hl_Dan P c Q fenv)
(IHhl : forall (func_list : list fun_Dan) (n_args : nat) (idents : list ident),
       aimp_always_wf func_list idents n_args P c Q fenv hl ->
       forall (s1 s2 : AbsState) (i' : imp_stack) (fenv' : fun_env_stk),
       funcs_okay_too func_list fenv' ->
       Forall
         (fun func : fun_Dan =>
          all_params_ok (DanTrickLanguage.Args func)
            (DanTrickLanguage.Body func)) func_list ->
       fenv_well_formed' func_list fenv ->
       fun_app_imp_well_formed fenv func_list c ->
       terminator fenv n_args P Q c hl ->
       i' = comp_code c idents n_args ->
       fenv' = compile_fenv fenv ->
       logic_transrelation n_args idents P s1 ->
       logic_transrelation n_args idents Q s2 ->
       imp_rec_rel (var_map_wf_wrt_imp idents) c ->
       AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
         (var_map_wf_wrt_bexp idents) P ->
       AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
         (var_map_wf_wrt_bexp idents) Q -> hl_stk s1 i' s2 fenv')
func_list n_args idents
(AIMPWF : log_Dan_wf func_list fenv P /\
         log_Dan_wf func_list fenv Q /\
         log_Dan_wf func_list fenv P' /\
         log_Dan_wf func_list fenv Q' /\
         log_Dan_wf_map idents Q /\
         log_Dan_wf_map idents Q' /\
         log_Dan_wf_map idents P /\
         log_Dan_wf_map idents P' /\
         AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
           (var_map_wf_wrt_bexp idents) P /\
         AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
           (var_map_wf_wrt_bexp idents) Q /\
         AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
           (var_map_wf_wrt_bexp idents) P' /\
         AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
           (var_map_wf_wrt_bexp idents) Q' /\
         hl_Dan_wf fenv func_list idents n_args P Q c hl)
s1 s2 i' fenv'
(OKfuncs : funcs_okay_too func_list fenv')
(OKparams : Forall
             (fun func : fun_Dan =>
              all_params_ok (DanTrickLanguage.Args func)
                (DanTrickLanguage.Body func)) func_list)
(FENV_WF : fenv_well_formed' func_list fenv)
(FUN_APP : fun_app_imp_well_formed fenv func_list c)
(GENESYS : terminator fenv n_args P Q c hl /\
          log_terminates_always fenv n_args P /\
          log_terminates_always fenv n_args P' /\
          log_terminates_always fenv n_args Q /\
          log_terminates_always fenv n_args Q')
(H : i' = compile_imp c (ident_list_to_map idents) (Datatypes.length idents))
(H0 : fenv' = compile_fenv fenv)
(H1 : logic_transrelation n_args idents P' s1)
(H2 : logic_transrelation n_args idents Q' s2)
(WF : imp_rec_rel (var_map_wf_wrt_imp idents) c)
(H5 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) Q')
ARG
(H3 : logic_transrelation n_args idents P ARG)
ARG0
(H7 : logic_transrelation n_args idents Q ARG0)
(a' : (s1 --->>> ARG) fenv')
(a0' : (Q -->> Q') fenv)
(WF' : var_map_wf_wrt_imp idents c)
:
hl_stk s1 i' s2 fenv'.
Proof.
   eapply hl_stk_consequence; [ | try eassumption .. ].
      eapply IHhl. 
      -- apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AIMPWF))))))))))).
      -- apply OKfuncs.
      -- eassumption.
      -- eassumption.
      -- assumption.
      -- apply (proj1 GENESYS).
      -- eassumption.
      -- eassumption. 
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AIMPWF))))))))). 
      -- apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AIMPWF)))))))))).
      -- eapply aimpdan_to_aimpstk with (s1 := ARG0) (s2 := s2) (fenv' := fenv') in a0'; try eassumption; simpl in GENESYS; try intuition. 
      unfold_wf_imp_in WF'. apply (proj1 WF0).
Qed.

Definition hl_Dan_implication_6 P Q P' Q' c fenv 
(hl : hl_Dan P c Q fenv)
(a : (P' -->> P) fenv)
(a0 : (Q -->> Q') fenv)
(IHhl : forall (func_list : list fun_Dan) (n_args : nat)
         (idents : list ident),
       aimp_always_wf func_list idents n_args P c Q fenv hl ->
       forall (s1 s2 : AbsState) (i' : imp_stack)
         (fenv' : fun_env_stk),
       funcs_okay_too func_list fenv' ->
       Forall
         (fun func : fun_Dan =>
          all_params_ok (DanTrickLanguage.Args func)
            (DanTrickLanguage.Body func)) func_list ->
       fenv_well_formed' func_list fenv ->
       fun_app_imp_well_formed fenv func_list c ->
       terminator fenv n_args P Q c hl ->
       i' = comp_code c idents n_args ->
       fenv' = compile_fenv fenv ->
       logic_transrelation n_args idents P s1 ->
       logic_transrelation n_args idents Q s2 ->
       imp_rec_rel (var_map_wf_wrt_imp idents) c ->
       AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
         (var_map_wf_wrt_bexp idents) P ->
       AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
         (var_map_wf_wrt_bexp idents) Q -> hl_stk s1 i' s2 fenv')
func_list n_args idents
(AIMPWF : aimp_always_wf func_list idents n_args P' c Q' fenv
           (hl_Dan_consequence P Q P' Q' c fenv hl a a0))
s1 s2 i' fenv'
(OKfuncs : funcs_okay_too func_list fenv')
(OKparams : Forall
             (fun func : fun_Dan =>
              all_params_ok (DanTrickLanguage.Args func)
                (DanTrickLanguage.Body func)) func_list)
(FENV_WF : fenv_well_formed' func_list fenv)
(FUN_APP : fun_app_imp_well_formed fenv func_list c)
(GENESYS : terminator fenv n_args P Q c hl /\
          log_terminates_always fenv n_args P /\
          log_terminates_always fenv n_args P' /\
          log_terminates_always fenv n_args Q /\
          log_terminates_always fenv n_args Q')
(H : i' =
    compile_imp c (ident_list_to_map idents)
      (Datatypes.length idents))
(H0 : fenv' = compile_fenv fenv)
(H1 : logic_transrelation n_args idents P' s1)
(H2 : logic_transrelation n_args idents Q' s2)
(WF : imp_rec_rel (var_map_wf_wrt_imp idents) c)
(H4 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) P')
(H5 : AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
       (var_map_wf_wrt_bexp idents) Q')
:
hl_stk s1 i' s2 fenv'.
Proof.
    pose proof (H3 := logic_transrelation_to_compiled n_args idents P).
    pose proof (H7 := logic_transrelation_to_compiled n_args idents Q).
    remember_all_in H3.
    remember_all_in H7.
    simpl in GENESYS.
    apply inv_aimpwf_consequence in AIMPWF.
    pose proof (WF' := WF).
    eapply imp_rec_rel_self in WF'.
    eapply aimpdan_to_aimpstk with (s1 := s1) (s2 := ARG) (fenv' := fenv') in a;
    [ | eassumption | eassumption |  |  | try eassumption .. ].
    + eapply hl_Dan_implication_6_1; eauto.
    + eassumption. 
    + eassumption.
    + apply (proj1 (proj2 (proj2 AIMPWF))). 
    + apply (proj1 AIMPWF). 
    + apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AIMPWF))))))).
    + simpl in GENESYS. apply (proj1 (proj2 (proj2 GENESYS))).
    + simpl in GENESYS. apply (proj1 (proj2 GENESYS)).
    + unfold_wf_imp_in WF'. apply (proj1 WF0).
    + apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AIMPWF))))))))).
Defined.

Print hl_Dan_implication_6.


Definition hl_Dan_implication (d1 d2: AbsEnv) (i: imp_Dan) (fenv: fun_env) (hl: hl_Dan d1 i d2 fenv)
           (func_list: list fun_Dan)
           (n_args : nat)
           (idents: list ident)
  (AIMPWF: aimp_always_wf func_list idents n_args d1 i d2 fenv hl):
  forall (s1 s2: AbsState) (i': imp_stack) (fenv': fun_env_stk),
  forall (OKfuncs: funcs_okay_too func_list fenv')
    (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
    (FENV_WF: fenv_well_formed' func_list fenv)
    (FUN_APP: fun_app_imp_well_formed fenv func_list i)
    (GENESYS: terminator fenv n_args d1 d2 i hl),
    i' = comp_code i idents n_args ->
    fenv' = compile_fenv fenv ->
    logic_transrelation n_args idents d1 s1 ->
    logic_transrelation n_args idents d2 s2 ->
    imp_rec_rel (var_map_wf_wrt_imp idents) i ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d1 ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d2 ->
    
    hl_stk s1 i' s2 fenv'.
Proof.
  dependent induction hl; unfold comp_code; intros.
  - subst.
    eapply log_comp_determ in H1; [ | eapply H2].
    subst. simpl. econstructor.
  - eapply hl_Dan_implication_2; eauto.
  - apply (hl_Dan_implication_3 P Q R i1 i2 fenv hl1 hl2 IHhl1 IHhl2 func_list n_args idents); auto.
  - apply (hl_Dan_implication_4 P Q b i1 i2 fenv hl1 hl2 IHhl1 IHhl2 func_list n_args idents); auto.
  - eapply hl_Dan_implication_5; eauto.
  - eapply hl_Dan_implication_6; eauto.
Defined.

Lemma hl_dan_implication_helper' :
  forall s1 ARG b idents n_args fenv d my_fun,
    logic_transrelation n_args idents d s1 ->
  ARG = AbsAnd s1
               (BaseState AbsStkTrue
                          (MetaBool
                             (UnaryProp bool bexp_stack
                                        my_fun
                                        (compile_bexp b (ident_list_to_map idents)
                                                      (Datatypes.length idents))))) ->
  (ARG --->>>
       (AbsAnd
          s1
          (BaseState (AbsStkSize (Datatypes.length idents + n_args))
                     (MetaBool
                        (UnaryProp bool bexp_stack my_fun
                                   (compile_bexp b (ident_list_to_map idents)
                                                 (Datatypes.length idents))))))) 
    (compile_fenv fenv).
Proof.
  induction s1; unfold aimpstk; intros; subst; invs H1.
  - econstructor. assumption.
    econstructor. invs H6.
    invs H. invs H3.
    assumption.
    invs H6. assumption.
  - econstructor. assumption.
    econstructor.
    invs H6. invs H. invs H1. eapply IHs1_1 in H10; [ | ereflexivity ].
    unfold aimpstk in H10. assert (absstate_match_rel (AbsAnd s1_1 (BaseState AbsStkTrue (MetaBool (UnaryProp bool bexp_stack my_fun (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)))))) (compile_fenv fenv) stk).
    {
      econstructor.
      invs H5. eassumption.
      assumption.
    }
    eapply H10 in H0. invs H0. invs H15. assumption.
    invs H6. assumption.
  - econstructor. assumption.
    econstructor.
    invs H6. invs H. invs H1. invs H5.
    + eapply IHs1_1 in H10; [ | ereflexivity].
      unfold aimpstk in H10. assert (absstate_match_rel (AbsAnd s1_1 (BaseState AbsStkTrue (MetaBool (UnaryProp bool bexp_stack my_fun (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)))))) (compile_fenv fenv) stk).
      {
        econstructor. eassumption. assumption.
      }
      eapply H10 in H0. invs H0. invs H16.
      assumption.
    + eapply IHs1_2 in H11; [ | ereflexivity ].
      unfold aimpstk in H11. assert (absstate_match_rel (AbsAnd s1_2 (BaseState AbsStkTrue (MetaBool (UnaryProp bool bexp_stack my_fun (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)))))) (compile_fenv fenv) stk) by (econstructor; eassumption).
      eapply H11 in H0. invs H0. invs H16.
      assumption.
    + invs H6. assumption.
Qed.





Ltac log_comp_adequate :=
  match goal with
  | [ |- logic_transrelation _ _ _ _ ] =>
      eapply log_comp_adequacy; ereflexivity
  | [ |- comp_logic _ _ _ = _ ] =>
      eapply log_comp_adequacy; eassumption
  | [ |- _ = comp_logic _ _ _ ] =>
      symmetry; eapply log_comp_adequacy; eassumption
  end.


(** Definition to make the following lemmas agnostic to whether the
  * function is afalseDan/afalsestk or atrueDan/atruestk. *)
Local Definition isAfalseOrAtrue (afalsetrueDan: bexp_Dan -> AbsEnv -> AbsEnv) (afalsetruestk: bexp_stack -> AbsState -> AbsState): Prop :=
  (afalsetrueDan = afalseDan /\ afalsetruestk = afalsestk) \/ (afalsetrueDan = atrueDan /\ afalsetruestk = atruestk).

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

Lemma compiling_afalse_atrue :
  forall (d: AbsEnv) (s s': AbsState) (n_args: nat) (idents: list ident) (fenv: fun_env) (fenv': fun_env_stk) (b: bexp_Dan) (afalsetrueDan: bexp_Dan -> AbsEnv -> AbsEnv) (afalsetruestk: bexp_stack -> AbsState -> AbsState),
    fenv' = compile_fenv fenv ->
    isAfalseOrAtrue afalsetrueDan afalsetruestk ->
    logic_transrelation n_args idents (afalsetrueDan b d) s' ->
    logic_transrelation n_args idents d s ->
    (s' --->>> (afalsetruestk (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)) s)) fenv'.
Proof.
  induction d; unfold isAfalseOrAtrue in *; intros; destruct H0; destruct H0; subst; unfold aimpstk; intros; unfold afalseDan in *; unfold atrueDan in *; unfold atruestk, afalsestk in *.
  - invs H1.
    invs H6.
    invs H8. invs H7.
    invs H9.
    invs H0.
    invs H2. eapply lp_comp_determ in H11; [ | eapply H5].
    subst.
    unfold comp_bool in H.
    invs H.
    invs H13.
    econstructor.
    + assumption.
    + econstructor; [ econstructor | eassumption].
  - invs H1. invs H2. invs H6. invs H8.
    eapply lp_comp_determ  in H5; [ | eapply H7].
    subst. invs H9.
    invs H5. invs H0.
    unfold comp_bool in *.
    econstructor.
    + invs H. assumption.
    + econstructor; [ econstructor | ].
      invs H. invs H13. eassumption.
  - invs H1. invs H2. eapply absand_distribution. econstructor.
    fold (afalsestk (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)) s0).
    unfold aimpstk in *.
    eapply IHd1; try ereflexivity.
    left; split; ereflexivity.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    invs H6.
    eapply log_comp_determ in H7; [ | eapply H9]; subst.
    eapply log_comp_determ in H10; [ | eapply H12]; subst.
    invs H. invs H4.
    econstructor; eassumption.
    eapply log_comp_determ in H2; [ | eapply H6 ]; subst.
    invs H8. invs H4. invs H5. invs H0.
    unfold comp_bool in *.
    invs H. invs H9.
    invs H13.
    econstructor.
    eassumption.
    econstructor. econstructor. eassumption.
  - invs H1. invs H2. eapply log_comp_determ in H2; [ | eapply H6]; subst.
    invs H8. invs H4. invs H5. invs H0.
    eapply absand_distribution. econstructor.
    + invs H. invs H9.
      econstructor. assumption.
      econstructor. econstructor. invs H13. eassumption.
    + invs H. invs H9. invs H13. econstructor. assumption.
      econstructor. econstructor. eassumption.
  - invs H1. invs H2. eapply log_comp_determ in H2; [ | eapply H6]; subst.
    invs H8. invc H4. invc H5. invc H0.
    eapply absor_distribution. eapply absor_distribution in H.
    eapply absor_dissolution in H. eapply absor_dissolution.
    destruct H.
    + left. invs H. invs H9.
      econstructor; [ eassumption | econstructor; [econstructor | eassumption ]].
    + right. invs H. invs H9.
      econstructor; [ | econstructor; [ econstructor | ]]; eassumption.
  - invs H1. invs H2. eapply log_comp_determ in H2; [ |  eapply H6]; subst.
    invs H8. invc H4. invc H5. invc H0.
    eapply absor_distribution, absor_dissolution. eapply absor_distribution, absor_dissolution in H.
    destruct H.
    + left. invs H. invs H9. econstructor; [ | econstructor; [ econstructor | ]]; eassumption.
    + right. invs H. invs H9. econstructor; [ | econstructor; [ econstructor | ]]; eassumption.
Qed.

Lemma compiling_afalse_atrue' :
  forall (d: AbsEnv) (s s': AbsState) (n_args: nat) (idents: list ident) (fenv: fun_env) (fenv': fun_env_stk) (b: bexp_Dan) (afalsetrueDan: bexp_Dan -> AbsEnv -> AbsEnv) (afalsetruestk: bexp_stack -> AbsState -> AbsState),
    fenv' = compile_fenv fenv ->
    isAfalseOrAtrue afalsetrueDan afalsetruestk ->
    logic_transrelation n_args idents (afalsetrueDan b d) s' ->
    logic_transrelation n_args idents d s ->
    ((afalsetruestk (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)) s) --->>> s') fenv'.
Proof.
  induction d; intros; unfold isAfalseOrAtrue in *; destruct H0; destruct H0; subst; unfold aimpstk; intros; unfold afalsestk, atruestk in *.
  - invs H1. invs H2. eapply log_comp_determ in H2; [ | eapply H6]; subst.
    invs H8. invc H4. invc H7. invc H0.
    invs H. invs H9. invs H3.
    econstructor; econstructor; assumption.
  - invs H1. invs H2. eapply log_comp_determ in H2; [ | eapply H6]; subst.
    invs H8. invc H4. invc H7. invc H0.
    invs H. invs H9. invs H3.
    econstructor; econstructor; assumption.
  - invc H1. invs H2.
    eapply log_comp_determ in H2; [ | eapply H6 ]; subst.
    invs H8. invc H3. invc H4. invc H0.
    invs H. invs H7. invs H7. invs H2.
    absand_destruct H.
    eapply absand_distribution; eapply absand_dissolution. split.
    + eapply IHd1; try ereflexivity. left; split; ereflexivity.
      econstructor. eassumption.
      eassumption.
      eassumption.
      econstructor.
      invs H2. eassumption.
      econstructor; eassumption.
    + eapply IHd2; try ereflexivity. left; split; ereflexivity.
      econstructor; eassumption.
      eassumption.
      econstructor; eassumption.
  - invc H1. invs H2.
    eapply log_comp_determ in H2; [ | eapply H6 ]; subst.
    invs H8. invc H3. invc H4. invc H0.
    invs H. invs H7. invs H7. invs H2.
    absand_destruct H.
    eapply absand_distribution; eapply absand_dissolution. split.
    + eapply IHd1; try ereflexivity. right; split; ereflexivity.
      econstructor. eassumption.
      eapply H8.
      eassumption.
      econstructor.
      invs H2. eassumption.
      econstructor; eassumption.
    + eapply IHd2; try ereflexivity. right; split; ereflexivity.
      econstructor; eassumption.
      eassumption.
      econstructor; eassumption.
  - invc H1. invs H2. eapply log_comp_determ in H2; [ | eapply H6]; subst.
    invs H8. invc H3. invc H4.  invc H0.
    eapply absor_distribution, absor_dissolution in H.
    eapply absor_distribution, absor_dissolution.
    destruct H.
    + left. eapply IHd1; try ereflexivity. left; split; ereflexivity.
      econstructor; eassumption.
      eassumption.
      simpl. eassumption.
    + right. eapply IHd2; try ereflexivity. left; split; ereflexivity.
      econstructor; eassumption.
      eassumption.
      simpl. eassumption.
  - invc H1. invs H2. eapply log_comp_determ in H2; [ | eapply H6]; subst.
    invs H8. invc H3. invc H4.  invc H0.
    eapply absor_distribution, absor_dissolution in H.
    eapply absor_distribution, absor_dissolution.
    destruct H.
    + left. eapply IHd1; try ereflexivity. right; split; ereflexivity.
      econstructor; eassumption.
      eassumption.
      simpl. eassumption.
    + right. eapply IHd2; try ereflexivity. right; split; ereflexivity.
      econstructor; eassumption.
      eassumption.
      simpl. eassumption.
Qed.
