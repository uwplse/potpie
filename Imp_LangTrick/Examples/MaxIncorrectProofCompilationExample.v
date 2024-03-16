From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick Require Import TranslationPure Imp_LangTrickLanguage.
From Imp_LangTrick Require Import ProofCompiler FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy ProofCompilableCodeCompiler.
From Imp_LangTrick Require Import TerminatesForSure BuggyProofCompiler ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
From Imp_LangTrick Require Import AimpWfAndCheckProofAuto.

Import Tests.

Local Open Scope string_scope.
Local Open Scope list_scope.
Module IncorrectlyCompiledFenvExample_ModuleVersion.
  Local Definition maxSmallCompMap := "z" :: nil.
  Local Definition maxSmallCompProg := (IF_Imp_Lang (gt_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1)) (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0)) (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1))).

  Local Definition comp_map := "z" :: "y" :: "x" :: nil.

  Local Definition maxSmallStkIncorrect := BuggyProofCompiler.CC.compile_imp maxSmallCompProg comp_map (List.length comp_map).

  Eval compute in maxSmallStkIncorrect.

  Local Definition maxFunctionImp_Lang := 
    {| Imp_LangTrickLanguage.Name := "max"
    ; Imp_LangTrickLanguage.Args := 2
    ; Ret := "z"
    ; Imp_LangTrickLanguage.Body := maxSmallCompProg|}.

  Local Definition maxFunctionStkIncorrect :=
    compile_function maxFunctionImp_Lang.

  Eval compute in maxFunctionStkIncorrect.

  Local Definition fenvMaxIn :=
    update "max" maxFunctionImp_Lang init_fenv.

  Local Definition funcs := ((fenvMaxIn "id") :: (fenvMaxIn "max") :: nil).

  Local Definition fenvsMaxIncorrectIn := update "max" maxFunctionStkIncorrect init_fenv_stk.

  Definition maxSmallProofMaxFenv :=
  hl_Imp_Lang_if Source.imp_lang_log_true
            Source.max_conclusion
            (gt_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1))
            (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0))
            (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1))
            Source.imp_list
            fenvMaxIn
            (hl_Imp_Lang_consequence_pre
               (AbsEnvAnd Source.param0geqparam0 Source.param0geqparam1)
               Source.max_conclusion
               (AbsEnvAnd Source.imp_lang_log_true Source.param0gtparam1)
               (* max_conclusion *)
               (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0))
               0
               Source.imp_list
               fenvMaxIn
               (hl_Imp_Lang_assign
                  Source.max_conclusion
                  Source.imp_list
                  fenvMaxIn
                  "z"
                  (PARAM_Imp_Lang 0))
               Source.zeroth_impliction
               (Source.aimpImp_LangPP' fenvMaxIn))
            (hl_Imp_Lang_consequence_pre
               (AbsEnvAnd Source.param1geqparam0
                            Source.param1geqparam1)
               Source.max_conclusion
               (AbsEnvAnd Source.imp_lang_log_true
                            Source.notparam0gtparam1)
               (* max_conclusion *)
               (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1))
               1
               Source.imp_list
               fenvMaxIn
               (hl_Imp_Lang_assign
                  Source.max_conclusion
                  Source.imp_list
                  fenvMaxIn
                  "z"
                  (PARAM_Imp_Lang 1))
                Source.first_implication
                (Source.secondaimpImp_LangP'P fenvMaxIn)).

  Local Open Scope imp_langtrick_scope.
  Lemma comparator_terminates : 
forall dbenv fenv nenv, 
  List.length dbenv >= 2 ->
  b_Imp_Lang (PARAM_Imp_Lang 0 >d PARAM_Imp_Lang 1) dbenv fenv nenv true \/ b_Imp_Lang (PARAM_Imp_Lang 0 >d PARAM_Imp_Lang 1) dbenv fenv nenv false.
Proof.
  unfold gt_Imp_Lang. unfold lt_Imp_Lang. intros.
  destruct dbenv. invs H. destruct dbenv. invs H. invs H1. simpl in H.
  unfold neq_Imp_Lang. unfold eq_Imp_Lang.
  remember (andb (Nat.leb n0 n) (negb (andb (Nat.leb n0 n) (Nat.leb n n0)))) as b.
  destruct b.
  - left. rewrite Heqb. econstructor.
    + econstructor; econstructor; simpl; try lia; reflexivity.
    + econstructor. econstructor; econstructor; econstructor; simpl; try lia; reflexivity.
  - right. rewrite Heqb. econstructor; econstructor; econstructor; simpl; try lia; try reflexivity; econstructor; econstructor; simpl; try lia; try reflexivity.
Qed.

Lemma args_terminate_max_proof : 
  forall a1 a2, 
  (forall nenv dbenv fenv, 
    exists n1 n2, 
      a_Imp_Lang a1 dbenv fenv nenv n1 /\
      a_Imp_Lang a2 dbenv fenv nenv n2) ->
  aimpImp_Lang Source.imp_lang_log_true
               (AbsEnvAnd
                  (Source.true_bool (geq_Imp_Lang (APP_Imp_Lang "max" (a1::a2::nil)) (a1)))
                  (Source.true_bool (geq_Imp_Lang (APP_Imp_Lang "max" (a1::a2::nil)) a2)))
               fenvMaxIn.
Proof. 
  unfold aimpImp_Lang. intros. specialize (H nenv dbenv fenvMaxIn) as RESULTS. destruct RESULTS as (n1&rest).
  destruct rest as  (n2&rest).  
  destruct rest as (sem1 & sem2).
  
  pose proof comparator_terminates (n1 :: n2 :: nil) fenvMaxIn init_nenv. simpl in H1. assert (2 >= 2) by lia. specialize (H1 H2). destruct H1; repeat constructor. 
- pose proof maxSmallProofMaxFenv. pose proof Hoare_Imp_Lang_sound Source.imp_lang_log_true maxSmallCompProg Source.max_conclusion Source.imp_list fenvMaxIn X. unfold triple_Imp_Lang in H3. econstructor. econstructor. apply sem1. econstructor. exists. simpl; reflexivity. econstructor. apply sem1. repeat econstructor. apply sem2. simpl in *. econstructor. apply H1. repeat econstructor. 
(* constructor.
  + assumption.
  + constructor. constructor. simpl; lia. simpl. exists.
  + simpl. exists. *)
  + pose proof @update_same nat "z" n1 init_nenv. simpl. 
    apply H4.  
  + apply (Nat.leb_le n1 n1). lia.  
- pose proof maxSmallProofMaxFenv. pose proof Hoare_Imp_Lang_sound Source.imp_lang_log_true maxSmallCompProg Source.max_conclusion Source.imp_list fenvMaxIn X. unfold triple_Imp_Lang in H0. econstructor. econstructor. apply sem2. econstructor. exists. simpl; reflexivity. econstructor. apply sem1. repeat econstructor. apply sem2. simpl in *. econstructor. apply H1. repeat econstructor. 
  (* + assumption.
  + constructor. constructor. simpl; lia. simpl. exists. *)
  + simpl. exists.
  + pose proof @update_same nat "z" n1 init_nenv. rewrite H4.
    apply Nat.leb_le. invs H1. invs H11. invs H8. invs H15. 
    simpl in *. 
    assert (forall (x : nat) y, ((Some x) = (Some y)) -> x = y) by (intros; invs H5; lia). 
    pose proof (H5 n1 n3) H13. rewrite H14 in *.
    pose proof (H5 n2 n0 H9). rewrite H16 in *. pose proof (Bool.andb_true_iff (Nat.leb n0 n3) b2). destruct H17. specialize (H17 H7). destruct H17. pose proof (Nat.leb_le n0 n3). destruct H20. apply H20. assumption.
- pose proof maxSmallProofMaxFenv. pose proof Hoare_Imp_Lang_sound Source.imp_lang_log_true maxSmallCompProg Source.max_conclusion Source.imp_list fenvMaxIn X. unfold triple_Imp_Lang in H0. econstructor. econstructor. apply sem1. econstructor. exists. simpl; reflexivity. econstructor. apply sem1. repeat econstructor. apply sem2. simpl. apply Imp_Lang_if_false. assumption.
econstructor. constructor. simpl. lia. exists. simpl in *. exists. 
  + pose proof @update_same nat "z" (n2) init_nenv. rewrite H4.
    apply Nat.leb_le. invs H1. invs H11. invs H8. invs H15. 
    simpl in *. 
    assert (forall (x : nat) y, ((Some x) = (Some y)) -> x = y) by (intros; invs H5; lia). 
    pose proof (H5 n2 n0) H9. rewrite H14 in *.
    pose proof H5 n1 n3 H13. rewrite H16 in *. pose proof Nat.leb_gt n0 n3. pose proof Bool.andb_false_iff (n0 <=? n3)%nat b2.
    destruct H18. specialize (H18 H7). destruct H18.
    * destruct H17. specialize (H17 H18). lia.
    * invs H12. pose proof Bool.negb_false_iff b. destruct H14. specialize (H14 H25). rewrite H14 in H21. invs H21. 
    pose proof Bool.andb_true_iff b1 b2.
    destruct H14. specialize (H14 H22). destruct H14. subst. invs H28. invs H31. simpl in H24. 
    pose proof (H5 n0 n2 H24). rewrite H14 in *.  invs H30. simpl in H32.      
    pose proof (H5 n3 n1 H32). rewrite H14 in *. 
    pose proof Nat.leb_le n1 n2. destruct H26. apply H26; assumption.
- pose proof maxSmallProofMaxFenv. pose proof Hoare_Imp_Lang_sound Source.imp_lang_log_true maxSmallCompProg Source.max_conclusion Source.imp_list fenvMaxIn X. unfold triple_Imp_Lang in H0. econstructor. econstructor. apply sem2. econstructor. exists. simpl; reflexivity. econstructor. apply sem1. repeat econstructor. apply sem2. simpl. apply Imp_Lang_if_false. assumption.
  econstructor. constructor. simpl. lia. exists. simpl in *. exists. 

  + pose proof @update_same nat "z" n2 init_nenv.
    rewrite H4. apply Nat.leb_le. lia. 
Qed.

  Lemma stk_funcs_okay_too_incorrect :
    funcs_okay_too funcs fenvsMaxIncorrectIn.
  Proof.
    unfold funcs_okay_too. split; [ | split; intros; try destruct H ]. constructor. split.
    - repeat econstructor.
    - constructor; try simpl; lia.
    - constructor; try split.
      + simpl. unfold maxSmallStkIncorrect. unfold fenvsMaxIncorrectIn.   
        econstructor. constructor. repeat constructor.
      + simpl. repeat constructor.
      + constructor.
    - rewrite <- H. simpl. apply eq_refl.
    - destruct H; destruct H. simpl. apply eq_refl.
    - unfold fenvsMaxIncorrectIn. unfold update. destruct (string_dec "max" names). 
      + left. rewrite <- e. unfold fenvMaxIn. unfold update. simpl. right. left. apply eq_refl.
      + right. unfold init_fenv_stk. reflexivity.  
  Qed.

Lemma Imp_LangImp : 
  aimpImp_Lang Source.imp_lang_log_true (AbsEnvAnd (Source.true_bool (geq_Imp_Lang (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil)) (VAR_Imp_Lang "x")))
  (Source.true_bool (geq_Imp_Lang (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil)) (VAR_Imp_Lang "y")))) fenvMaxIn.
Proof.
  pose proof args_terminate_max_proof (VAR_Imp_Lang "x") (VAR_Imp_Lang "y"). 
  assert (forall (nenv : nat_env) (dbenv : list nat) (fenv : fun_env),
  exists n1 n2 : nat,
    a_Imp_Lang (VAR_Imp_Lang "x") dbenv fenv nenv n1 /\
    a_Imp_Lang (VAR_Imp_Lang "y") dbenv fenv nenv n2).
  - intros. exists (nenv "x"). exists (nenv "y"). split;  
  constructor; reflexivity.
  - apply H. assumption.  
Qed.      


Local Definition maxFactEnv := ((Source.imp_lang_log_true), ((AbsEnvAnd (Source.true_bool (geq_Imp_Lang (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil)) (VAR_Imp_Lang "x")))
(Source.true_bool (geq_Imp_Lang (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil)) (VAR_Imp_Lang "y"))))))::nil. 

Local Definition targetFactEnv := List.map (fun x => ((BuggyProofCompilable.SC.comp_logic 0 comp_map (fst x)), (BuggyProofCompilable.SC.comp_logic 0 comp_map (snd x)))) maxFactEnv. 


Local Definition straightlineAssignMax := 
  (ASSIGN_Imp_Lang ("z") (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil))). 

Local Definition xyz := (AbsEnvAnd (Source.true_bool (geq_Imp_Lang (VAR_Imp_Lang "z") (VAR_Imp_Lang "x")))
(Source.true_bool (geq_Imp_Lang (VAR_Imp_Lang "z") (VAR_Imp_Lang "y")))). 

Lemma zeroth_implication_index :  
  nth_error maxFactEnv 0 =
    Some (Source.imp_lang_log_true,
           Imp_LangLogSubst.subst_AbsEnv "z"
                                         ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil) xyz).
Proof. 
  unfold maxFactEnv. simpl. apply eq_refl.
Qed.     

Local Definition maxAssign :=
  hl_Imp_Lang_consequence_pre (Imp_LangLogSubst.subst_AbsEnv "z" (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil)) xyz)
                              xyz
                              (Source.imp_lang_log_true)
                              straightlineAssignMax
                              0
                              maxFactEnv
                              fenvMaxIn
                              (hl_Imp_Lang_assign 
                                 xyz maxFactEnv fenvMaxIn "z" (APP_Imp_Lang "max" ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil)))
                              zeroth_implication_index
                              Imp_LangImp.

Lemma imp_list_valid : 
  fact_env_valid maxFactEnv fenvMaxIn. 
Proof.
  unfold fact_env_valid.  intros. unfold maxFactEnv in *. destruct H; try invs H. apply Imp_LangImp.
Qed.

Lemma max_funcs_params_ok :
  Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs.
Proof.
  repeat constructor.
Qed.

Lemma max_fun_app_imp :
  fun_app_imp_well_formed fenvMaxIn funcs straightlineAssignMax.
Proof.
  unfold straightlineAssignMax. econstructor. econstructor. econstructor. econstructor. econstructor. econstructor. econstructor. exists. unfold funcs. finite_in. simpl. lia. simpl. unfold maxSmallCompProg. apply ImpHasVarIf__then. repeat constructor. left. simpl. apply eq_refl. 
Qed.

  Lemma var_map_wf_imp_z_gets_max :
    imp_rec_rel (var_map_wf_wrt_imp comp_map) (ASSIGN_Imp_Lang
                                                 "z" (APP_Imp_Lang "max" (VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil))).
  Proof.
    eapply CompilerCorrectMoreHelpers.var_map_wf_imp_self_imp_rec_rel.
    reflexivity.
  Qed.

  Ltac wf_bexp_finite :=
    unfold var_map_wf_wrt_bexp; split; [ var_map_wf_finite | ]; repeat split; intros;
    match goal with
    | [ H: ?bvarmap = free_vars_bexp_src _, H': In _ ?bvarmap |- In _ _ ] =>
        simpl in H;
        rewrite H in H'; finite_in_implication
    | [ H: ?bvarmap = free_vars_bexp_src _, H': In _ ?bvarmap |- bexp_has_variable _ _ ] =>
        eapply free_vars_in_bexp_has_variable; eassumption
    | [ H: ?bvarmap = free_vars_bexp_src _, H': In _ ?bvarmap |- _ ] =>
        simpl in H; subst bvarmap; eapply in_implies_find_index_rel; [ finite_in_implication | finite_nodup ]
    | [ |- _ ] =>
        idtac
    end;
    idtac.

Lemma max_app_well_formed_helper_lemma :
  forall (n : "max" <> "id")
    (Hmaxid : string_dec "max" "id" = right n)
    (e : "max" = "max")
  (Hmaxmax : string_dec "max" "max" = left e),
    fun_app_well_formed
    (fun y : ident =>
     if string_dec "max" y
     then maxFunctionImp_Lang
     else
      {|
        Name := "id";
        Args := 1;
        Ret := "x";
        Body := "x" <- PARAM_Imp_Lang 0
      |})
    ({|
       Name := "id";
       Args := 1;
       Ret := "x";
       Body := "x" <- PARAM_Imp_Lang 0
     |} :: maxFunctionImp_Lang :: nil)
    ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil).
Proof.
  intros. econstructor.
  - repeat econstructor.
  - reflexivity.
  - simpl. right. left. reflexivity.
  - simpl. reflexivity.
  - simpl. unfold maxSmallCompProg. eapply ImpHasVarIf__else. econstructor. reflexivity.
  - simpl. left. reflexivity.
Qed.

  Lemma maxSmallCompProg_if_false
        (dbenv : list nat)
        (nenv : nat_env)
        (H : AbsEnv_rel Source.imp_lang_log_true
                        (update "max" maxFunctionImp_Lang init_fenv) dbenv nenv)
        (p0 : nat)
        (Heqp0 : p0 = nenv "x")
        (p1 : nat)
        (Heqp1 : p1 = nenv "y")
        (Heqb : false =
                  ((p1 <=? p0)%nat && negb ((p1 <=? p0)%nat && (p0 <=? p1)%nat))%bool):
    i_Imp_Lang maxSmallCompProg (nenv "x" :: nenv "y" :: nil)
               (update "max" maxFunctionImp_Lang init_fenv) init_nenv 
               (update "z" (nenv "y") init_nenv).
  Proof.
    unfold maxSmallCompProg. eapply Imp_Lang_if_false.
    * remember (nenv "x" :: nenv "y" :: nil) as temp1.
      remember (update "max" maxFunctionImp_Lang init_fenv) as temp2.
      rewrite Heqb. subst temp1 temp2. meta_smash; congruence.
    * meta_smash.
  Qed.
  Lemma aimp_true :
    aimpImp_Lang Source.imp_lang_log_true
    (Imp_LangLogSubst.subst_AbsEnv "z"
       ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil) xyz)
    (update "max" maxFunctionImp_Lang init_fenv).
  Proof.
    unfold Source.true_bool. unfold fenvMaxIn.
    unfold aimpImp_Lang. intros.
    unfold maxSmallCompProg.
    remember (nenv "x") as p0.
    remember (nenv "y") as p1.
    remember (andb (Nat.leb p1 p0) (negb (andb (Nat.leb p1 p0) (Nat.leb p0 p1)))) as b. destruct b.
    econstructor; econstructor; econstructor; meta_smash.
    - unfold maxSmallCompProg. unfold gt_Imp_Lang. unfold lt_Imp_Lang.
      eapply Imp_Lang_if_true.
      + remember (nenv "x" :: nenv "y" :: nil) as temp.
        remember (update "max" maxFunctionImp_Lang init_fenv) as temp1.
        rewrite Heqb.
        subst temp temp1.
        meta_smash; congruence.
      + meta_smash.
    - simpl. unfold update. simpl. eapply Nat.leb_refl.
    - unfold maxSmallCompProg. unfold gt_Imp_Lang. unfold lt_Imp_Lang.
      eapply Imp_Lang_if_true.
      + remember (nenv "x" :: nenv "y" :: nil) as temp.
        remember (update "max" maxFunctionImp_Lang init_fenv) as temp1.
        rewrite Heqb. subst temp temp1.
        meta_smash; congruence.
      + meta_smash.
    - unfold update. simpl.
      symmetry in Heqb. eapply Bool.andb_true_iff in Heqb.
      destruct Heqb. subst p0 p1. eassumption.
    - simpl. pose proof (maxSmallCompProg_if_false dbenv nenv H p0 Heqp0 p1 Heqp1 Heqb).
      econstructor; econstructor; econstructor; (meta_smash; [ eapply H0 | ]); unfold update; simpl; subst p0 p1; symmetry in Heqb; eapply Bool.andb_false_iff in Heqb; destruct Heqb.
      + eapply Nat.leb_le. eapply Nat.leb_gt in H1.
        lia.
      + eapply Bool.negb_false_iff in H1.
        eapply Bool.andb_true_iff in H1.
        destruct H1. assumption.
      + eapply Nat.leb_refl.
      + eapply Nat.leb_refl.
  Qed.
      
                           

Lemma maxSmallAimpAlwaysWf :
  aimp_always_wf funcs comp_map 0 Source.imp_lang_log_true straightlineAssignMax xyz fenvMaxIn maxFactEnv maxAssign.
  Proof.
    unfold aimp_always_wf, comp_map, Source.imp_lang_log_true, funcs, straightlineAssignMax, xyz, fenvMaxIn, maxAssign.
    pose proof (UIP_option_refl := UIPList.UIP_option_pair_refl _ Imp_LangLogPropDec.UIP_AbsEnv).
    specialize (UIP_option_refl _ zeroth_implication_index).
    eapply HLImp_LangWFConsequencePre with (n := 0) (nth := zeroth_implication_index); simplify_var_map_wf_cases; try finite_not_in.
    - shelve. (* shelve aimpImp_Lang *)
    - reflexivity.
    - hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; try finite_not_in; try reflexivity.
      + log_Imp_Lang_wf_helper_no_app.
      + repeat econstructor.
      + handle_fun_app_well_formed_app.
    - unfold xyz.  simpl. log_Imp_Lang_wf_helper_no_app.
    - simpl. log_Imp_Lang_wf_helper_no_app.
    - repeat econstructor.
    - repeat econstructor.
      Unshelve.
      eapply aimp_true.
Qed.

Lemma precondition_translated :
  BuggyProofCompilable.SC.comp_logic 0 comp_map Source.imp_lang_log_true = BuggyProofCompilable.SC.comp_logic 0 comp_map Source.imp_lang_log_true.
Proof.
  reflexivity.
Qed. 

Lemma postcondition_translated : 
  BuggyProofCompilable.SC.comp_logic 0 comp_map xyz = BuggyProofCompilable.SC.comp_logic 0 comp_map xyz.
Proof.
  reflexivity.
Qed.

Lemma maxSmallImp_LangLogPropRelPre :
  AbsEnv_prop_wf comp_map Source.imp_lang_log_true.
Proof.
  unfold AbsEnv_prop_wf, comp_map, Source.imp_lang_log_true.
  econstructor. econstructor. econstructor.
Qed.

Lemma maxSmallImp_LangLogPropRelPost :
  AbsEnv_prop_wf comp_map xyz.
Proof.
  unfold AbsEnv_prop_wf, comp_map, xyz.
  unfold Source.true_bool.
  econstructor; econstructor; econstructor; econstructor.
  - wf_bexp_finite.
  - wf_bexp_finite.
Qed.

Lemma maxSmallVarMapWfWrtImp :
  imp_rec_rel (var_map_wf_wrt_imp comp_map) straightlineAssignMax.
Proof.
  (* econstructor. *)
  eapply var_map_wf_imp_z_gets_max.
Qed.

Ltac enough_room n stk :=
  match n with
  | 0 =>
      fail
  | 1 =>
      match stk with
      | _ :: _ =>
          idtac
      | _ =>
          fail
      end
  | S ?n' =>
      match stk with
      | _ :: ?stk' =>
          enough_room n' stk'
      | _ =>
          fail
      end
  end.


Ltac eval_prop_rel_helper :=
  simpl;
  match goal with
  | [ |- eval_prop_rel _ _ ] =>
      econstructor;
      eval_prop_rel_helper
  | [ |- bexp_stack_sem _ _ (_ :: _) (_ :: _, _) ] =>
      simpl; econstructor; eval_prop_rel_helper
  | [ |- aexp_stack_sem
          (?compiler _
            (fun x : ident => one_index_opt x ?map)
            (Datatypes.length ?map))
          _ _ _] =>
      unfold compiler; simpl; eval_prop_rel_helper
  | [ |- aexp_stack_sem (Var_Stk ?n) _ ?stk (?stk', ?n1) ] =>
      enough_room n stk;
      econstructor; simpl; try lia; try reflexivity
  | [ |- aexp_stack_sem (App_Stk _ _) _ _ _ ] =>
      progress econstructor; try reflexivity; eval_prop_rel_helper
  | [ |- args_stack_sem (_ :: _)
                       _ _ _] =>
      econstructor; eval_prop_rel_helper
  | [ |- args_stack_sem nil _ _ _ ] =>
      econstructor
  | [ |- imp_stack_sem Push_Stk _ ?stk ?stk' ] =>
      econstructor; try reflexivity
  | [ |- imp_stack_sem (Assign_Stk (stack_mapping _ _) _)
                      _ _ _ ] =>
      unfold stack_mapping; simpl; eval_prop_rel_helper
  | [ |- imp_stack_sem (Assign_Stk _ _) _ _ _ ] =>
      econstructor; simpl; try lia; eval_prop_rel_helper
  | [ |- stack_mutated_at_index _ ?k _ ?original_stack ] =>
      enough_room k original_stack;
      econstructor; try reflexivity
  | [ |- aexp_stack_sem (Const_Stk _) _ _ _ ] =>
      econstructor
  | [ |- _ ] =>
      idtac "done"
  end.
Ltac same_after_popping_helper :=
  match goal with
  | [ |- same_after_popping _ _ _ ] =>
      progress econstructor;
      same_after_popping_helper
  | [ |- _ = _ ] =>
      try reflexivity
  end.

Lemma imp_trans_valid : 
  BuggyProofCompilable.valid_imp_trans_def maxFactEnv targetFactEnv fenvMaxIn fenvsMaxIncorrectIn comp_map 0.
Proof.
  unfold BuggyProofCompilable.valid_imp_trans_def; repeat split; intros.
  - simpl. lia.
  - destruct n.
    + simpl in *. invs H3. simpl. reflexivity.
    + unfold targetFactEnv. simpl. simpl in H3. destruct n. simpl in *. invs H3. simpl in H3. invs H3.
  (* - destruct n; simpl in *.
    + invs H1. invc H3. unfold Source.imp_lang_log_true. simpl. unfold comp_map in H4.
      destruct_stks stk. econstructor.
      * econstructor. simpl. lia.
      * econstructor. econstructor. econstructor.
    + rewrite nth_error_nil_none in H3. invs H3.
  - destruct n; simpl in H3.
    + invc H3. destruct_stks stk. unfold Source.imp_lang_log_true in *. meta_smash. econstructor. econstructor.
    + rewrite nth_error_nil_none in H3. invs H3.
  - destruct_stks stk. destruct n; simpl in *. invc H3.
    (* logic_transrelation_inversion. *)
    simpl in *. destruct ((Nat.leb (nenv "x")(nenv "y"))) eqn:?;  econstructor; constructor.
    + constructor. simpl; lia.
    + meta_smash.
      * eapply Stack_if_false.
        -- meta_smash. rewrite Heqb. reflexivity.
        -- meta_smash. smash_stack_mutated_at_index.
      * simpl. lia.
      * simpl. reflexivity.
      * repeat econstructor.
      * eapply Nat.leb_le. eapply Nat.leb_le in Heqb. lia.
      * repeat econstructor.
    + econstructor. simpl. lia.
    + meta_smash.
      * eapply Stack_if_false.
        -- meta_smash. rewrite Heqb. reflexivity.
        -- meta_smash.  smash_stack_mutated_at_index.
      * simpl. lia.
      * simpl. reflexivity.
      * repeat econstructor.
      * eapply Nat.leb_le. lia.
      * repeat econstructor.
    + econstructor. simpl. lia.
    + meta_smash.
      * eapply Stack_if_true.
        -- meta_smash. rewrite Heqb. reflexivity.
        -- meta_smash. smash_stack_mutated_at_index.
      * simpl. lia.
      * simpl. reflexivity.
      * repeat econstructor.
      * eapply Nat.leb_le. lia.
      * repeat econstructor.
    + econstructor. simpl. lia.
    + meta_smash.
      * eapply Stack_if_true.
        -- meta_smash. rewrite Heqb. reflexivity.
        -- meta_smash. smash_stack_mutated_at_index.
      * simpl. lia.
      * simpl. reflexivity.
      * repeat econstructor.
      * eapply Nat.leb_gt in Heqb. eapply Nat.leb_le. lia.
      * repeat econstructor.
    + rewrite nth_error_nil_none in H3. invs H3.
  - pose proof Imp_LangImp. 
  destruct n. simpl in *. invs H3.  unfold aimpImp_Lang in H6. apply (H6 dbenv nenv). repeat econstructor.  
    destruct n; invs H3. *)
  - unfold StackLogic.fact_env_valid; intros. destruct H; simpl in H. invs H. unfold StackLogic.aimpstk; intros. absstate_match_inversion.   
    pose proof @nth_error_nth' nat stk 1 100. 
    pose proof @nth_error_nth' nat stk 2 100.
    assert (1 < Datatypes.length stk) by lia. 
    assert (2 < Datatypes.length stk) by lia. 
    specialize (H0 H4).
    specialize (H2 H5).
    destruct (Nat.leb (nth 2 stk 100) (nth 1 stk 100)) eqn:?; meta_smash; try eassumption.
    + eapply Stack_if_false; meta_smash.
      * rewrite Heqb. reflexivity.
      * smash_stack_mutated_at_index.
    + simpl. lia.
    + simpl. reflexivity.
    + repeat econstructor.
    + eapply Nat.leb_le. eapply Nat.leb_le in Heqb. lia.
    + repeat econstructor.
    + eapply Stack_if_false; meta_smash.
      * rewrite Heqb. reflexivity.
      * smash_stack_mutated_at_index.
    + simpl. lia.
    + simpl. reflexivity.
    + repeat econstructor.
    + eapply Nat.leb_le. eapply Nat.leb_le in Heqb. lia.
    + repeat econstructor.
    + eapply Stack_if_true; meta_smash.
      * rewrite Heqb. reflexivity.
      * smash_stack_mutated_at_index.
    + simpl. lia.
    + simpl. reflexivity.
    + repeat econstructor.
    + eapply Nat.leb_le. lia.
    + repeat econstructor.
    + eapply Stack_if_true; meta_smash.
      * rewrite Heqb. reflexivity.
      * smash_stack_mutated_at_index.
    + simpl. lia.
    + simpl. reflexivity.
    + repeat econstructor.
    + eapply Nat.leb_le. eapply Nat.leb_gt in Heqb. lia.
    + repeat econstructor.
    + contradiction.
Qed. 


Module SourceAssignMax <: SourceProgramType.
  Definition program := straightlineAssignMax.
  Definition precond := Source.imp_lang_log_true.
  Definition postcond := xyz.
  Definition fenv := fenvMaxIn.
  Definition facts := maxFactEnv. 
  Definition hoare_triple := maxAssign.
  Definition idents := comp_map.
  Definition num_args := 0.
  Definition funcs := funcs.
End SourceAssignMax.

(* 
Module TargetProgram (SP: SourceProgramType) <: TargetProgramType.
  Module SP := SP.

  Definition compile_imp_lang_log (d: AbsEnv): AbsState :=
    comp_logic SP.num_args SP.idents d.
  
  Definition program: imp_stack := comp_code SP.program SP.idents SP.num_args.
  Definition precond: AbsState := compile_imp_lang_log SP.precond.
  Definition postcond: AbsState := compile_imp_lang_log SP.postcond.
  Definition fenv: fun_env_stk := compile_fenv SP.fenv.
  Definition facts: implication_env_stk := map (translate_AbsEnv_pair SP.idents SP.num_args) SP.facts.
End TargetProgram. *)

  Lemma fenvMaxIn_well_formed :
  fenv_well_formed' ((fenvMaxIn "id"):: (fenvMaxIn "max") :: nil) fenvMaxIn.
Proof.
  unfold fenv_well_formed'.
  repeat split.
  - constructor.
    + unfold not; intros. invs H. unfold fenvMaxIn in H0. unfold init_fenv in H0. unfold update in H0. simpl in H0. unfold maxFunctionImp_Lang in H0. discriminate. invs H0.        
    + constructor. unfold In. unfold not. intros; assumption. constructor.    
  - intros. 
  (* pose proof string_dec f "max"; destruct H0;  *)
  unfold fenvMaxIn in *. unfold update in *. 
  destruct (string_dec "max" f).
    + left. simpl. right. left. symmetry. assumption.
    + simpl. unfold init_fenv in *. simpl. right. assumption.          
   (* left. unfold update in H. simpl in H.   finite_in.   split; [ | split; [ | split ] ].  *)
  - unfold fenvMaxIn in *. unfold update in *. 
    destruct (string_dec "max" f).
    + unfold maxFunctionImp_Lang in *. assert (Body func = maxSmallCompProg) by (rewrite H; simpl; reflexivity). rewrite H0. unfold maxSmallCompProg. repeat econstructor.
    + unfold init_fenv in *. rewrite H. simpl. repeat econstructor.
  - unfold fenvMaxIn in *. unfold update in *. 
    destruct (string_dec "max" f).
    + unfold maxFunctionImp_Lang in *. assert (Body func = maxSmallCompProg) by (rewrite H; simpl; reflexivity). rewrite H0. rewrite H. unfold maxSmallCompProg. simpl. 
    apply ImpHasVarIf__then. repeat constructor.  
    + unfold init_fenv in *. rewrite H. simpl. repeat econstructor.
  - unfold fenvMaxIn. unfold update. simpl. repeat constructor; unfold not; intros; destruct H; try discriminate; try constructor. invs H.
  - intros. unfold fenvMaxIn in *. unfold update in *. unfold init_fenv in *. simpl in H.  destruct H; destruct (string_dec "max" f). 
    + rewrite H0 in H. unfold maxFunctionImp_Lang. discriminate.
    + simpl in IN_FUNC_NAMES; destruct IN_FUNC_NAMES; try (rewrite <- H1). 
      * rewrite H0. simpl. reflexivity.
      * destruct H1; try contradiction. 
    + destruct H; try contradiction. unfold maxFunctionImp_Lang in H. rewrite <- H. simpl. symmetry. apply e.
    + destruct H; try contradiction. simpl in IN_FUNC_NAMES; destruct IN_FUNC_NAMES.
      * rewrite H0. simpl. symmetry. apply H1.
      * destruct H1; try contradiction.
  - unfold init_fenv; unfold fenvMaxIn; unfold update. simpl. unfold init_fenv. left. apply eq_refl.
  - intros. unfold fenvMaxIn in *; unfold update in *; simpl in H. destruct (string_dec "max" f). unfold not in H. assert ("id" = f \/ "max" = f \/ False) by (right;left;assumption).
  specialize (H H0). contradiction. unfold init_fenv. apply eq_refl.
  - intros. unfold fenvMaxIn in *. unfold update in *. unfold init_fenv in *. simpl in H0. destruct H0. 
    + exists "id". repeat split.
      * simpl. left; apply eq_refl.
      * destruct (string_dec "max" f). unfold maxFunctionImp_Lang in H. rewrite H in H0. discriminate. simpl. apply eq_refl.     
      * rewrite <- H0. simpl. apply eq_refl.
    + destruct H0; try contradiction. exists "max". repeat split.
      * simpl. right; left; apply eq_refl.
      * destruct (string_dec "max" f). simpl. apply eq_refl.  unfold maxFunctionImp_Lang in H0. rewrite H in H0. discriminate. 
      * rewrite <- H0. simpl. apply eq_refl.
Qed.

Definition translate_AbsEnv_pair_buggy lst args p :=
  match p with
  |(P, Q) => ((BuggyProofCompilable.SC.comp_logic args lst P)
  , (BuggyProofCompilable.SC.comp_logic args lst Q))
  end. 

Module TargetAssignMax <: TargetProgramType. 
  Module SP := SourceAssignMax. 
  Definition compile_imp_lang_log (d: AbsEnv):=
    BuggyProofCompilable.SC.comp_logic SP.num_args SP.idents d.
  Definition program: imp_stack := comp_code SP.program SP.idents SP.num_args.
  Definition precond := compile_imp_lang_log SP.precond.
  Definition postcond := compile_imp_lang_log SP.postcond.
  Definition fenv: fun_env_stk := fenvsMaxIncorrectIn.
  Definition facts := map (translate_AbsEnv_pair_buggy SP.idents SP.num_args) SP.facts.
End TargetAssignMax.

Lemma pre_sound_proof : 
BuggyProofCompilable.SC.transrelation_sound
SourceAssignMax.precond
SourceAssignMax.fenv
TargetAssignMax.fenv
SourceAssignMax.idents
SourceAssignMax.num_args.
Proof. 
  constructor. intros. split.
  - intros. simpl. econstructor.
    + invs H0. simpl. econstructor. simpl. lia.
    + repeat econstructor.
  - repeat econstructor.
Qed.             

Lemma post_sound_proof : 
  BuggyProofCompilable.SC.transrelation_sound
  SourceAssignMax.postcond
  SourceAssignMax.fenv
  TargetAssignMax.fenv
  SourceAssignMax.idents
  SourceAssignMax.num_args.
Proof. 
  constructor; intros; split; intros; simpl in *.
  - unfold BuggyProofCompilable.SC.comp_bool. unfold BuggyProofCompilable.SC.CC.compile_bexp. simpl. invs H0. simpl in *. 
    econstructor; econstructor.
    + econstructor. simpl. lia.
    + econstructor; econstructor; econstructor; try econstructor; try lia. 
      simpl. lia. exists. simpl. lia. exists. AbsEnv_rel_inversion. rewrite H3 in *. invs H9. invs H10. symmetry. apply H3.
    + econstructor. simpl. lia.
    + econstructor; econstructor; econstructor; try econstructor; try lia. 
    simpl. lia. exists. simpl. lia. exists. AbsEnv_rel_inversion. rewrite H3 in *. rewrite H4 in *.  invs H11. invs H12. symmetry. apply H4.
  - unfold BuggyProofCompilable.SC.CC.compile_bexp in H1. simpl in H1. invs H0. simpl in *. 
  econstructor; econstructor; econstructor; econstructor.
    + econstructor; econstructor; exists.
    + absstate_match_inversion. simpl in *. invs H23. invs H22. symmetry. apply H15.
    + econstructor; econstructor; exists.
    + absstate_match_inversion. simpl in *. invs H22. invs H18. invs H19. symmetry. assumption.
Qed.

  Lemma max_check_proof_proof :
    BuggyProofCompiler.PC.check_proof SourceAssignMax.fenv SourceAssignMax.funcs SourceAssignMax.precond SourceAssignMax.postcond SourceAssignMax.program SourceAssignMax.facts SourceAssignMax.idents SourceAssignMax.num_args SourceAssignMax.hoare_triple.
  Proof.
    unfold SourceAssignMax.fenv, SourceAssignMax.funcs, SourceAssignMax.precond, SourceAssignMax.postcond, SourceAssignMax.program, SourceAssignMax.facts, SourceAssignMax.idents, SourceAssignMax.num_args, SourceAssignMax.hoare_triple.
    unfold maxAssign. unfold straightlineAssignMax. eapply BuggyProofCompiler.PC.CheckHLPre.
    - simpl. reflexivity.
    - unfold BuggyProofCompiler.PC.CC.check_imp. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - assert (ASSIGN_Imp_Lang "z" ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil) = ASSIGN_Imp_Lang "z" ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil)) by reflexivity.
      pose proof (eq_refl (AbsEnvAnd
      (Source.true_bool
         ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil >=d
          VAR_Imp_Lang "x"))
      (Source.true_bool
         ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil >=d
          VAR_Imp_Lang "y")))).
      
      eapply BuggyProofCompiler.PC.CheckHLAssign with (Hi := H) (Heq := H0).
      + rewrite (UIP_imp_refl _ H). rewrite (Imp_LangLogPropDec.UIP_AbsEnv_refl _ H0). simpl. reflexivity.
      + reflexivity.
      + unfold BuggyProofCompiler.PC.CC.compile_aexp. simpl.
        StackExprWellFormed.prove_absstate_well_formed.
      + simpl. unfold BuggyProofCompilable.SC.comp_bool. unfold BuggyProofCompilable.SC.CC.compile_bexp. simpl.
        StackExprWellFormed.prove_absstate_well_formed.
      + simpl. econstructor. econstructor. econstructor. lia. econstructor. econstructor. lia.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + unfold BuggyProofCompiler.PC.CC.compile_aexp. unfold funcs. simpl. intros.
        unfold funcs_okay_too in H5. destruct H5 as (FORALL & OTHER). simpl in FORALL. invc FORALL. invc H8. destruct H9.
        econstructor.
        * reflexivity.
        * econstructor. econstructor. lia. econstructor. econstructor. lia. econstructor.
        * eassumption.
        * eassumption.
        * eapply StackPurestBase.aexp_frame_implies_aexp_pure. eassumption.
      + simpl. unfold BuggyProofCompiler.PC.CC.compile_aexp. unfold BuggyProofCompilable.SC.comp_bool. unfold BuggyProofCompilable.SC.CC.compile_bexp. simpl. intros.
        rewrite <- H1. rewrite H4.  simpl. reflexivity.
  Qed.

  Lemma max_check_logic_precond_proof :
    BuggyProofCompiler.SC.check_logic SourceAssignMax.precond = true.
  Proof.
    reflexivity.
  Qed.
    

    Lemma max_check_logic_postcond_proof :
      BuggyProofCompiler.SC.check_logic SourceAssignMax.postcond = true.
  Proof.
    reflexivity.
  Qed.

  Lemma max_check_imp_proof :
    BuggyProofCompiler.CC.check_imp SourceAssignMax.program = true.
  Proof.
    reflexivity.
  Qed.

  Module CompileMaxProofs <: ProgramProofCompilationType.
    Module CAPC := BuggyProofCompiler.
    Module SOURCE := SourceAssignMax.
    Module TARGET := TargetAssignMax.
    Definition fact_cert := imp_list_valid. 
    Definition facts' := targetFactEnv. 
    Definition fenv_well_formed_proof := fenvMaxIn_well_formed.
    Definition funcs_okay_too_proof := stk_funcs_okay_too_incorrect.
    Definition all_params_ok_for_funcs_proof := max_funcs_params_ok.
    Definition fun_app_well_formed_proof  := max_fun_app_imp.
    Definition aimp_always_wf_proof := maxSmallAimpAlwaysWf.
    Definition check_proof_proof := max_check_proof_proof.
    Definition translate_precond_proof := precondition_translated.
    Definition translate_postcond_proof := postcondition_translated.
    Definition check_logic_precond_proof := max_check_logic_precond_proof.
    Definition check_logic_postcond_proof := max_check_logic_postcond_proof.
    (* Definition terminator_proof := maxTerminates. *)
    Definition program_compiled_proof := eq_refl (comp_code straightlineAssignMax comp_map 0).
    Definition check_imp_proof := max_check_imp_proof.
    (* Definition fun_env_compiled_proof := eq_refl (compile_fenv init_fenv). *)
    Definition precond_wf_proof := maxSmallImp_LangLogPropRelPre.
    Definition postcond_wf_proof := maxSmallImp_LangLogPropRelPost.
    Definition imp_code_wf_proof := maxSmallVarMapWfWrtImp.
    Definition implication_transformer := imp_trans_valid.
    Definition pre_sound := pre_sound_proof. 
    Definition post_sound := post_sound_proof. 
  End CompileMaxProofs.
End IncorrectlyCompiledFenvExample_ModuleVersion.
