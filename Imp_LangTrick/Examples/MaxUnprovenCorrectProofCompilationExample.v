From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick Require Import TranslationPure Imp_LangTrickLanguage.
From Imp_LangTrick Require Import ProofCompiler FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy.
From Imp_LangTrick Require Import TerminatesForSure UnprovenCorrectProofCompiler ProofCompCodeCompAgnosticMod.

Import Tests.

Local Open Scope string_scope.
Local Open Scope list_scope.
Module CorrectlyCompiledFenvExample_ModuleVersion.
  Local Definition maxSmallCompMap := "z" :: nil.
  Local Definition maxSmallCompProg := (IF_Imp_Lang (gt_Imp_Lang (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1)) (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 0)) (ASSIGN_Imp_Lang "z" (PARAM_Imp_Lang 1))).

  Local Definition comp_map := "z" :: "y" :: "x" :: nil.

  Local Definition maxSmallStkCorrect := UnprovenCorrectProofCompiler.CC.compile_imp maxSmallCompProg comp_map (List.length comp_map).

  Eval compute in maxSmallStkCorrect.

  Local Definition maxFunctionImp_Lang := 
    {| Imp_LangTrickLanguage.Name := "max"
    ; Imp_LangTrickLanguage.Args := 2
    ; Ret := "z"
    ; Imp_LangTrickLanguage.Body := maxSmallCompProg|}.

  Local Definition maxFunctionStkCorrect :=
    compile_function maxFunctionImp_Lang.

  Eval compute in maxFunctionStkCorrect.

  Local Definition fenvMaxIn :=
    update "max" maxFunctionImp_Lang init_fenv.

  Local Definition funcs := ((fenvMaxIn "id") :: (fenvMaxIn "max") :: nil).

  Local Definition fenvsMaxCorrectIn := update "max" maxFunctionStkCorrect init_fenv_stk.

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
    funcs_okay_too funcs fenvsMaxCorrectIn.
  Proof.
    unfold funcs_okay_too. constructor. constructor. split.
    - repeat econstructor.
    - constructor; try simpl; lia.
    - constructor; try split.
      + simpl. unfold maxSmallStkCorrect. unfold fenvsMaxCorrectIn.   
        econstructor. constructor. repeat constructor.
      + simpl. repeat constructor.
      + constructor.
    - split; intros; try destruct H. 
      + rewrite <- H. simpl. apply eq_refl.
      + destruct H; destruct H. simpl. apply eq_refl.
      + unfold fenvsMaxCorrectIn. unfold update. destruct (string_dec "max" names). 
        * left. rewrite <- e. unfold fenvMaxIn. unfold update. simpl. right. left. apply eq_refl.
        * right. unfold init_fenv_stk. reflexivity.  
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

Local Definition targetFactEnv := List.map (fun x => ((UnprovenCorrectProofCompiler.PC.SC.comp_logic 0 comp_map (fst x)), (UnprovenCorrectProofCompiler.PC.SC.comp_logic 0 comp_map (snd x)))) maxFactEnv. 


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
  econstructor. unfold var_map_wf_wrt_imp. split; [ | repeat split ]; unfold comp_map.
    + var_map_wf_finite.  
    + econstructor. econstructor.
      * var_map_wf_finite.
      * repeat split; intros.
        -- simpl in H. subst. finite_in_implication.
        -- eapply free_vars_in_aexp_has_variable; eassumption.
        -- eapply find_index_rel_in. eassumption. eassumption. intros. simpl in H. subst. finite_in_implication.
           finite_nodup_reflective.
        -- invc H. eapply free_vars_in_args_has_variable; try eassumption. reflexivity.
    + intros. invs H.
      * eapply String.eqb_eq in H2. subst x. finite_in.
      * invs H2. invs H3.
        -- invs H4. eapply String.eqb_eq in H5. subst x. finite_in.
        -- invs H4.
           ++ invs H5. eapply String.eqb_eq in H6. subst x. finite_in.
           ++ invs H5.
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
      
                           

Lemma maxSmallAimpAlwaysWf :
  aimp_always_wf funcs comp_map 0 Source.imp_lang_log_true straightlineAssignMax xyz fenvMaxIn maxFactEnv maxAssign.
Proof.
  unfold aimp_always_wf. unfold Source.imp_lang_log_true. unfold xyz. unfold straightlineAssignMax. unfold maxFactEnv. unfold maxAssign. unfold Source.imp_lang_log_true. unfold straightlineAssignMax. unfold maxFactEnv. simpl. unfold Source.imp_lang_log_true. unfold Source.true_bool.
  eapply HLImp_LangWFConsequencePre.
  - shelve.
  - reflexivity.
  - eapply var_map_wf_imp_z_gets_max.
  - unfold AbsEnv_prop_wf. unfold comp_map. unfold Source.true_bool.
    econstructor; econstructor; econstructor; econstructor.
    + wf_bexp_finite.
      
    + wf_bexp_finite.
  - unfold comp_map. unfold AbsEnv_prop_wf. econstructor. econstructor. econstructor.
  - unfold comp_map. unfold AbsEnv_prop_wf. econstructor; econstructor; econstructor; econstructor; wf_bexp_finite.
  -
    (* Check HLImp_LangWFAssign. *)
    unfold xyz.
    assert (Hsubst :
             (Imp_LangLogSubst.subst_AbsEnv "z" ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil) (AbsEnvAnd (Source.true_bool (VAR_Imp_Lang "z" >=d VAR_Imp_Lang "x"))
                                                                                                         (Source.true_bool (VAR_Imp_Lang "z" >=d VAR_Imp_Lang "y"))))
           = (AbsEnvAnd (Source.true_bool (("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil) >=d VAR_Imp_Lang "x"))
                        (Source.true_bool (("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil) >=d VAR_Imp_Lang "y")))) by reflexivity.
    assert (Heq' : ("z" <- ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil)) = ("z" <- ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil))) by reflexivity.

    eapply HLImp_LangWFAssign with (x := "z") (a := ("max" @d VAR_Imp_Lang "x" :: VAR_Imp_Lang "y" :: nil)) (Heq := Heq') (Hsubst := Hsubst); [ | clear Hsubst Heq' .. ]. progress simpl. subst. simpl.
    specialize (Imp_LangLogPropDec.UIP_AbsEnv_refl _ Hsubst). intros.
    subst. simpl.
    specialize (UIP_imp_refl _ Heq'). intros. subst. simpl. reflexivity.
    + 
      unfold AbsEnv_prop_wf, comp_map. constructor; constructor; constructor; constructor; (unfold var_map_wf_wrt_bexp; split; [ var_map_wf_finite | ]; repeat split; intros); solve [simpl in H; rewrite H in H0; finite_in_implication | eapply free_vars_in_bexp_has_variable; eassumption | simpl in H; subst bexp_var_map; eapply in_implies_find_index_rel; [ finite_in_implication | finite_nodup ]].
    + eapply var_map_wf_imp_z_gets_max.
    + repeat econstructor.
    + econstructor; econstructor; econstructor; econstructor; unfold comp_map; wf_bexp_finite.
    + econstructor; econstructor; econstructor; econstructor; econstructor; econstructor.
    + repeat econstructor.
    + unfold funcs.  unfold fenvMaxIn. unfold init_fenv. unfold update.
      destruct (string_dec "max" "id") eqn:Hmaxid. invs e.
      destruct (string_dec "max" "max") eqn:Hmaxmax; [ | Imp_LangLogicHelpers.discrim_neq ].
      eapply max_app_well_formed_helper_lemma; eassumption.
  - unfold funcs.  unfold fenvMaxIn. unfold init_fenv. unfold update.
      destruct (string_dec "max" "id") eqn:Hmaxid. invs e.
    destruct (string_dec "max" "max") eqn:Hmaxmax; [ | Imp_LangLogicHelpers.discrim_neq ]. econstructor; econstructor; econstructor; econstructor; econstructor.
    all: try eapply max_app_well_formed_helper_lemma; try eassumption.
    + repeat econstructor.
    + repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
  - econstructor; econstructor; econstructor; econstructor; unfold comp_map; wf_bexp_finite.
  - repeat econstructor.
  - econstructor; econstructor; econstructor; econstructor; unfold comp_map; wf_bexp_finite. 
  - repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
    Unshelve.
    unfold Source.true_bool. unfold fenvMaxIn.
    unfold aimpImp_Lang. intros.
    unfold maxSmallCompProg.
    remember (nenv "x") as p0.
    remember (nenv "y") as p1.
    remember (andb (Nat.leb p1 p0) (negb (andb (Nat.leb p1 p0) (Nat.leb p0 p1)))) as b. destruct b.
    econstructor; econstructor; econstructor; econstructor.
    
    + econstructor.
      * econstructor. reflexivity.
      * econstructor. reflexivity. simpl. reflexivity.
        econstructor. econstructor. reflexivity. econstructor. econstructor. reflexivity. econstructor.
        simpl.
       
        
        -- eapply Imp_Lang_if_true.
           ++ rewrite <- Heqp0. rewrite <- Heqp1. rewrite Heqb. repeat econstructor.
           ++ econstructor. econstructor. simpl. lia. simpl. reflexivity.
        -- simpl. reflexivity.
    + unfold update. destruct (string_dec "z" "z"). eapply Nat.leb_refl.
      Imp_LangLogicHelpers.discrim_neq.
    + econstructor.
      * econstructor. reflexivity.
      * econstructor.
        -- reflexivity.
        -- simpl. reflexivity.
        -- econstructor.
           ++ econstructor. reflexivity.
           ++ econstructor.
              ** econstructor. reflexivity.
              ** econstructor.
        -- simpl. unfold maxSmallCompProg. eapply Imp_Lang_if_true.
           ++ rewrite Heqb. repeat econstructor.
              ** simpl. rewrite <- Heqb. rewrite Heqp1. reflexivity.
              ** rewrite <- Heqb. simpl. rewrite Heqp0. reflexivity.
              ** rewrite <- Heqb. simpl. f_equal. rewrite Heqp1. reflexivity.
              ** rewrite <- Heqb. simpl. rewrite Heqp0. reflexivity.
              ** rewrite <- Heqb. simpl. rewrite Heqp0. reflexivity.
              ** rewrite <- Heqb. simpl. rewrite Heqp1. reflexivity.
           ++ econstructor. econstructor.
              ** simpl. lia.
              ** simpl. reflexivity.
        -- simpl.
           unfold update. destruct (string_dec "z" "z"); [ | Imp_LangLogicHelpers.discrim_neq]. reflexivity.
    + eapply Bool.andb_true_eq in Heqb. destruct Heqb. subst. rewrite H0 at 10. reflexivity.
    + econstructor; econstructor; econstructor; econstructor. econstructor.
      * econstructor. reflexivity.
      * econstructor.
        -- reflexivity.
        -- reflexivity.
        -- econstructor. econstructor. reflexivity. econstructor. econstructor. reflexivity. econstructor.
        -- eapply Imp_Lang_if_false.
           ++ rewrite Heqb. repeat econstructor.
              all: try (rewrite <- Heqb; simpl; try rewrite Heqp0; try rewrite Heqp1; reflexivity).
           ++ econstructor. econstructor. simpl. lia. simpl. reflexivity.
        -- simpl. unfold update. destruct (string_dec "z" "z"). reflexivity. Imp_LangLogicHelpers.discrim_neq.
      * symmetry in Heqb. eapply Bool.andb_false_elim in Heqb. destruct Heqb.
        -- eapply leb_complete_conv in e. assert (p0 <= p1) by lia.
           eapply Nat.leb_le in H0. rewrite Heqp0, Heqp1 in H0. eassumption.
        -- eapply Bool.negb_false_iff in e.
           eapply Bool.andb_true_iff in e. destruct e. rewrite Heqp0, Heqp1 in H1. eassumption.
      * econstructor.
        -- econstructor. reflexivity.
        -- econstructor.
           ++ reflexivity.
           ++ reflexivity.
           ++ econstructor. econstructor. reflexivity. econstructor. econstructor. reflexivity. econstructor.
           ++ simpl. eapply Imp_Lang_if_false.
              ** rewrite Heqb. repeat econstructor.
                 all: try (rewrite <- Heqb; simpl; try rewrite Heqp0; try rewrite Heqp1; reflexivity).
              ** econstructor. econstructor. simpl. lia. simpl. reflexivity.
           ++ simpl. reflexivity.
      * unfold update. destruct (string_dec "z" "z"); [ | Imp_LangLogicHelpers.discrim_neq ] .
        eapply Nat.leb_refl.
Qed.

Lemma precondition_translated :
  UnprovenCorrectProofCompilable.SC.comp_logic 0 comp_map Source.imp_lang_log_true = UnprovenCorrectProofCompilable.SC.comp_logic 0 comp_map Source.imp_lang_log_true.
Proof.
  reflexivity.
Qed. 

Lemma postcondition_translated : 
  UnprovenCorrectProofCompilable.SC.comp_logic 0 comp_map xyz = UnprovenCorrectProofCompilable.SC.comp_logic 0 comp_map xyz.
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
  UnprovenCorrectProofCompilable.valid_imp_trans_def maxFactEnv targetFactEnv fenvMaxIn fenvsMaxCorrectIn comp_map 0.
Proof.
  unfold UnprovenCorrectProofCompilable.valid_imp_trans_def; repeat split; intros.
  - simpl. lia.
  - destruct n. simpl in *. invs H3. simpl. reflexivity.
    unfold targetFactEnv. simpl. simpl in H3. destruct n. simpl in *. invs H3. simpl in H3. invs H3.
  - unfold StackLogic.fact_env_valid; intros. destruct H; simpl in H. invs H. unfold StackLogic.aimpstk; intros. absstate_match_inversion.   
    pose proof @nth_error_nth' nat stk 1 100. 
    pose proof @nth_error_nth' nat stk 2 100.
    assert (1 < Datatypes.length stk) by lia. 
    assert (2 < Datatypes.length stk) by lia. 
    specialize (H0 H4).
    specialize (H2 H5). 
    destruct (Nat.leb (nth 2 stk 100) (nth 1 stk 100)) eqn:?; econstructor. econstructor. repeat econstructor; assumption. 
    unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp, comp_map; simpl; econstructor; econstructor; 
  econstructor.
    + econstructor; try lia. apply H2.
    + econstructor; try exists.
      * repeat econstructor; try lia. apply H2. apply H0.
      * simpl. econstructor. econstructor. exists. eapply Stack_if_false.
        --econstructor. econstructor. econstructor; try simpl; try lia. exists. econstructor; try simpl; try lia. exists. symmetry. apply Heqb. simpl. reflexivity.
        --econstructor; unfold stack_mapping.
          ++simpl. lia.
          ++simpl. lia.
          ++econstructor; simpl; try lia. exists.
          ++econstructor. exists. 
      * simpl. unfold stack_mapping; simpl. econstructor; econstructor; try simpl; try lia. exists.
      * simpl. constructor. constructor. constructor. constructor. apply eq_refl.
    + pose proof (Nat.leb_le (nth 2 stk 100) (nth 1 stk 100 + 1)). symmetry. 
      destruct H6; apply H7. 
      pose proof (Nat.leb_le (nth 2 stk 100) (nth 1 stk 100)). destruct H8. specialize (H8 Heqb). lia.
    + repeat econstructor.
    + repeat econstructor.
    (* + repeat econstructor.  *)
    + econstructor. repeat econstructor; assumption. 
      unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp, comp_map; simpl; econstructor; econstructor; 
      econstructor.
      * repeat econstructor; try lia. apply H0. 
      * simpl. econstructor; try exists. repeat econstructor; try lia. apply H2. apply H0. simpl. econstructor. repeat econstructor.   eapply Stack_if_false.
        --econstructor. econstructor. econstructor; try simpl; try lia. exists. econstructor; try simpl; try lia. exists. symmetry. apply Heqb. simpl. reflexivity.
        --econstructor; unfold stack_mapping.
          ++simpl. lia.
          ++simpl. lia.
          ++econstructor; simpl; try lia. exists.
          ++econstructor. exists. 
        -- econstructor; econstructor.
          ++simpl. unfold stack_mapping. simpl. lia.
          ++unfold stack_mapping; simpl. lia.
          ++simpl. exists. 
        -- repeat econstructor.    
      * pose proof (Nat.leb_le (nth 1 stk 100) (nth 1 stk 100 + 1)). symmetry. 
        destruct H6; apply H7. lia.  
      * repeat econstructor.
      * repeat econstructor.
    + econstructor. repeat econstructor; assumption. 
      unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp, comp_map; simpl; econstructor; econstructor; 
      econstructor.
      * repeat econstructor; try lia. apply H2. 
      * econstructor; try exists. econstructor. econstructor; try lia. apply H2. econstructor. econstructor; try lia. apply H0. econstructor. 
      (* symmetry. apply Heqb. simpl. reflexivity. *)
      simpl. econstructor; try exists. repeat econstructor; try lia.
       (* apply H2. apply H0. simpl. econstructor. repeat econstructor.  *)
       eapply Stack_if_true.
        --eapply Bool.negb_true_iff in Heqb. rewrite <- Heqb.  
          econstructor; econstructor; unfold stack_mapping.
          ++econstructor; simpl. lia. lia. exists. 
          ++econstructor; simpl. lia. lia. exists. 
          ++apply eq_refl. 
          (* econstructor; econstructor; simpl; try lia. exists. *)
          (* ++econstructor. exists.  *)
        -- econstructor.
          ++simpl. unfold stack_mapping. simpl. lia.
          ++unfold stack_mapping; simpl. lia.
          ++econstructor; simpl. lia. lia. exists. 
          ++econstructor; simpl. exists. 
          (* simpl. exists.  *)
        -- simpl. unfold stack_mapping. simpl. econstructor. econstructor. lia. simpl. lia. exists. econstructor.
        -- repeat econstructor. 
      * pose proof (Nat.leb_le (nth 2 stk 100) (nth 2 stk 100 + 1)). symmetry. 
        destruct H6; apply H7. lia.  
      * repeat econstructor.
      * repeat econstructor. 
    + econstructor. repeat econstructor; assumption. 
    unfold UnprovenCorrectProofCompilable.SC.CC.compile_bexp, comp_map; simpl; econstructor; econstructor; 
    econstructor.
    econstructor; try lia. apply H0.
    econstructor; try exists.
      * repeat econstructor; try lia. apply H2. apply H0.
      * simpl. econstructor. econstructor. exists. eapply Stack_if_true.
        --econstructor. econstructor. econstructor; try simpl; try lia. exists. econstructor; try simpl; try lia. exists. symmetry. apply Heqb. simpl. reflexivity.
        --econstructor; unfold stack_mapping.
          ++simpl. lia.
          ++simpl. lia.
          ++econstructor; econstructor; simpl; try lia.
           (* exists. *)
          ++econstructor. exists. 
      * simpl. unfold stack_mapping; simpl. econstructor; econstructor; try simpl; try lia. exists.
      * simpl. constructor. constructor. constructor. constructor. apply eq_refl.
      * pose proof (Nat.leb_le (nth 1 stk 100) (nth 2 stk 100 + 1)). symmetry. 
      destruct H6; apply H7. 
      pose proof (leb_iff_conv (nth 1 stk 100) (nth 2 stk 100)). destruct H8. specialize (H8 Heqb). lia.
      * repeat econstructor.
      * repeat econstructor.
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

  Lemma fenvMaxIn_well_formed :
  fenv_well_formed' ((fenvMaxIn "id"):: (fenvMaxIn "max") :: nil) fenvMaxIn.
Proof.
  unfold fenv_well_formed'.
  repeat split.
  - finite_nodup.
  - unfold fenvMaxIn in *. unfold update in *. 
    destruct (string_dec "max" f).
    + left. simpl. right. left. symmetry. assumption.
    + simpl. unfold init_fenv in *. simpl. right. assumption.          
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

Module TargetAssignMax <: TargetProgramType. 
  Module SP := SourceAssignMax. 
  Definition compile_imp_lang_log (d: AbsEnv):=
    UnprovenCorrectProofCompiler.PC.SC.comp_logic SP.num_args SP.idents d.
  Definition program: imp_stack := comp_code SP.program SP.idents SP.num_args.
  Definition precond := compile_imp_lang_log SP.precond.
  Definition postcond := compile_imp_lang_log SP.postcond.
  Definition fenv: fun_env_stk := fenvsMaxCorrectIn.
  Definition facts := map (fun x => translate_AbsEnv_pair SP.idents SP.num_args x UnprovenCorrectProofCompiler.PC.SC.comp_logic) SP.facts.
End TargetAssignMax.

Lemma pre_sound_proof : 
UnprovenCorrectProofCompiler.SC.transrelation_sound
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
  UnprovenCorrectProofCompiler.SC.transrelation_sound
  SourceAssignMax.postcond
  SourceAssignMax.fenv
  TargetAssignMax.fenv
  SourceAssignMax.idents
  SourceAssignMax.num_args.
Proof. 
  constructor; intros; split; intros; simpl in *.
  - unfold UnprovenCorrectProofCompiler.CC.compile_bexp. simpl. invs H0. simpl in *. 
    econstructor; econstructor.
    + econstructor. simpl. lia.
    + econstructor; econstructor; econstructor; try econstructor; try lia. 
      simpl. lia. exists. simpl. lia. exists. AbsEnv_rel_inversion. rewrite H3 in *. invs H9. invs H10. symmetry. apply H3.
    + econstructor. simpl. lia.
    + econstructor; econstructor; econstructor; try econstructor; try lia. 
    simpl. lia. exists. simpl. lia. exists. AbsEnv_rel_inversion. rewrite H3 in *. rewrite H4 in *.  invs H11. invs H12. symmetry. apply H4.
  - unfold UnprovenCorrectProofCompiler.CC.compile_bexp in H1. simpl in H1. invs H0. simpl in *. 
  econstructor; econstructor; econstructor; econstructor.
    + econstructor; econstructor; exists.
    + absstate_match_inversion. simpl in *. invs H23. invs H22. symmetry. apply H15.
    + econstructor; econstructor; exists.
    + absstate_match_inversion. simpl in *. invs H22. invs H18. invs H19. symmetry. assumption.
Qed.

  Lemma max_check_proof_proof :
    UnprovenCorrectProofCompiler.PC.check_proof SourceAssignMax.fenv SourceAssignMax.funcs SourceAssignMax.precond SourceAssignMax.postcond SourceAssignMax.program SourceAssignMax.facts SourceAssignMax.idents SourceAssignMax.num_args SourceAssignMax.hoare_triple.
  Proof.
    unfold SourceAssignMax.fenv, SourceAssignMax.funcs, SourceAssignMax.precond, SourceAssignMax.postcond, SourceAssignMax.program, SourceAssignMax.facts, SourceAssignMax.idents, SourceAssignMax.num_args, SourceAssignMax.hoare_triple.
    unfold maxAssign. unfold straightlineAssignMax. eapply UnprovenCorrectProofCompiler.PC.CheckHLPre.
    - simpl. reflexivity.
    - unfold UnprovenCorrectProofCompiler.PC.CC.check_imp. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - UnprovenCorrectProofCompiler.PC.check_proof_assign_setup.
      + UnprovenCorrectProofCompilable.unfold_cc_sc. simpl.
        StackExprWellFormed.prove_absstate_well_formed.
      + simpl. UnprovenCorrectProofCompiler.PC.unfold_cc_sc. simpl.
        StackExprWellFormed.prove_absstate_well_formed.
      + simpl. econstructor. econstructor. econstructor. lia. econstructor. econstructor. lia.
      + unfold UnprovenCorrectProofCompiler.PC.CC.compile_aexp. unfold funcs. simpl. intros.
        match goal with
        | [ H3: funcs_okay_too _ _ |- _ ] =>
            unfold funcs_okay_too in H3; destruct H3 as (FORALL & OTHER);
            simpl in FORALL; invc FORALL
        end.
        invc H6. destruct H7.
        
        econstructor.
        *  reflexivity.
        * econstructor. econstructor. lia. econstructor. econstructor. lia. econstructor.
        * eassumption.
        * eassumption.
        * eapply StackPurestBase.aexp_frame_implies_aexp_pure. eassumption.
      + simpl. UnprovenCorrectProofCompilable.unfold_cc_sc. simpl. intros.
        rewrite <- H. rewrite H2.  simpl. reflexivity.
  Qed.

  Lemma max_check_logic_precond_proof :
    UnprovenCorrectProofCompiler.SC.check_logic SourceAssignMax.precond = true.
  Proof.
    reflexivity.
  Qed.
    

    Lemma max_check_logic_postcond_proof :
      UnprovenCorrectProofCompiler.SC.check_logic SourceAssignMax.postcond = true.
  Proof.
    reflexivity.
  Qed.

  Lemma max_check_imp_proof :
    UnprovenCorrectProofCompiler.CC.check_imp SourceAssignMax.program = true.
  Proof.
    reflexivity.
  Qed.

  Module CompileMaxProofs <: ProgramProofCompilationType.
    Module CAPC := UnprovenCorrectProofCompiler.
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
End CorrectlyCompiledFenvExample_ModuleVersion.
