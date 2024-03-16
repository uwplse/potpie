From Coq Require Import String List Psatz Peano Program.Equality.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage EnvToStack StackLangTheorems.
From Imp_LangTrick Require Import Imp_LangTrickSemanticsMutInd ImpVarMap ImpVarMapTheorems.
From Imp_LangTrick Require Import LogicTranslationBase Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import FunctionWellFormed CompilerCorrectHelpers CompilerCorrectMoreHelpers.
From Imp_LangTrick Require Import StackFrame.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Definition P_compiler_sound (funcs: list fun_Imp_Lang) (i: imp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv nenv': nat_env): Prop :=
  forall (i_stk: imp_stack) (stk stk' rho: stack) (num_args: nat) (idents: list ident),
  forall (fenv_s: fun_env_stk),
  forall (FUN_WF: fun_app_imp_well_formed fenv funcs i),
  forall (FENV_WF: fenv_well_formed' funcs fenv),
    fenv_s = compile_fenv fenv ->
    List.length dbenv = num_args ->
    state_to_stack idents nenv dbenv stk ->
    state_to_stack idents nenv' dbenv stk' ->
    imp_rec_rel (var_map_wf_wrt_imp idents) i ->
    i_stk = compile_imp i (fun x => one_index_opt x idents) (List.length idents) ->
    imp_stack_sem i_stk fenv_s (stk ++ rho) (stk' ++ rho).

Local Definition P0_compiler_sound (funcs: list fun_Imp_Lang) (a: aexp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) (n: nat): Prop :=
  forall (a_stk: aexp_stack) (stk rho: stack) (num_args: nat) (idents: list ident),
  forall (fenv_s: fun_env_stk),
  forall (FUN_WF: fun_app_well_formed fenv funcs a),
  forall (FENV_WF: fenv_well_formed' funcs fenv),
    fenv_s = compile_fenv fenv ->
    List.length dbenv = num_args ->
    state_to_stack idents nenv dbenv stk ->
    var_map_wf_wrt_aexp idents a ->
    a_stk = compile_aexp a (fun x => one_index_opt x idents) (List.length idents) ->
    aexp_stack_sem a_stk fenv_s (stk ++ rho) (stk ++ rho, n).

Local Definition P1_compiler_sound (funcs: list fun_Imp_Lang) (b: bexp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) (v: bool): Prop :=
  forall (b_stk: bexp_stack) (stk rho: stack) (num_args: nat) (idents: list ident),
  forall (fenv_s: fun_env_stk),
  forall (FUN_WF: fun_app_bexp_well_formed fenv funcs b),
  forall (FENV_WF: fenv_well_formed' funcs fenv),
    fenv_s = compile_fenv fenv ->
    List.length dbenv = num_args ->
    state_to_stack idents nenv dbenv stk ->
    var_map_wf_wrt_bexp idents b ->
    b_stk = compile_bexp b (fun x => one_index_opt x idents) (List.length idents) ->
    bexp_stack_sem b_stk fenv_s (stk ++ rho) (stk ++ rho, v).

Local Definition P2_compiler_sound (funcs: list fun_Imp_Lang) (args: list aexp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) (vals: list nat): Prop :=
  forall (args_stk: list aexp_stack) (stk rho: stack) (num_args: nat) (idents: list ident),
  forall (fenv_s: fun_env_stk),
  forall (FUN_WF: fun_app_args_well_formed fenv funcs args),
  forall (FENV_WF: fenv_well_formed' funcs fenv),
    fenv_s = compile_fenv fenv ->
    List.length dbenv = num_args ->
    state_to_stack idents nenv dbenv stk ->
    Forall (var_map_wf_wrt_aexp idents) args ->
    args_stk = map (fun a => compile_aexp a (fun x => one_index_opt x idents) (List.length idents)) args ->
    args_stack_sem args_stk fenv_s (stk ++ rho) (stk ++ rho, vals).




Lemma big_step_away_pushes (funcs: list fun_Imp_Lang)
      (dbenv : list nat)
      (fenv : ident -> fun_Imp_Lang)
      (nenv nenv'' : nat_env)
      (func : fun_Imp_Lang)
      (aexps : list aexp_Imp_Lang)
      (ns : list nat)
      (ret : nat)
      (f : ident)
      (FUN_WF: fun_app_well_formed fenv funcs (APP_Imp_Lang f aexps))
      (FENV_WF: fenv_well_formed' funcs fenv)
      (e : fenv f = func)
      (e0 : Imp_LangTrickLanguage.Args func = Datatypes.length aexps)
      (i : i_Imp_Lang (Imp_LangTrickLanguage.Body func) ns fenv init_nenv nenv'')
      (H0 : forall (i_stk : imp_stack) (stk stk' rho : stack) 
         (num_args : nat) (idents : list ident) (fenv_s : fun_env_stk),
          fun_app_imp_well_formed fenv funcs (Imp_LangTrickLanguage.Body func) ->
          fenv_well_formed' funcs fenv ->
          fenv_s = compile_fenv fenv ->
          Datatypes.length ns = num_args ->
          state_to_stack idents init_nenv ns stk ->
          state_to_stack idents nenv'' ns stk' ->
          imp_rec_rel (var_map_wf_wrt_imp idents)
                      (Imp_LangTrickLanguage.Body func) ->
          i_stk =
            compile_imp (Imp_LangTrickLanguage.Body func)
                        (fun x : ident => one_index_opt x idents)
                        (Datatypes.length idents) ->
          imp_stack_sem i_stk fenv_s (stk ++ rho) (stk' ++ rho))
      (stk rho : stack)
      (num_args : nat)
      (idents : list ident)
      (fenv_s : fun_env_stk)
      (H1 : fenv_s = compile_fenv fenv)
      (H2 : Datatypes.length dbenv = num_args)
      (H3 : state_to_stack idents nenv dbenv stk)
      (H4 : var_map_wf_wrt_aexp idents (APP_Imp_Lang f aexps))
      (func' COMPD : fun_stk)
      (fidents : list ident)
      (Heqfidents : fidents = construct_trans (Imp_LangTrickLanguage.Body func))
      (HeqCOMPD : COMPD =
                    {|
                      Name := Imp_LangTrickLanguage.Name func;
                      Args := Datatypes.length aexps;
                      Body := fst (compile_code (Imp_LangTrickLanguage.Body func));
                      Return_expr :=
                      Var_Stk (stack_mapping (Imp_LangTrickLanguage.Body func) (Ret func));
                      Return_pop := Datatypes.length fidents
                    |})
      (Heqfunc' : func' =
                    {|
                      Name := Imp_LangTrickLanguage.Name func;
                      Args := Datatypes.length aexps;
                      Body :=
                      prepend_push
                        (compile_imp (Imp_LangTrickLanguage.Body func)
                                     (stack_mapping (Imp_LangTrickLanguage.Body func))
                                     (Datatypes.length fidents))
                        (Datatypes.length fidents);
                      Return_expr :=
                       Var_Stk (stack_mapping (Imp_LangTrickLanguage.Body func) (Ret func));
                      Return_pop := Datatypes.length fidents
                    |})
      (Hfunc' : func' = fenv_s f):
  imp_stack_sem
    (prepend_push
       (compile_imp (Imp_LangTrickLanguage.Body func)
                    (stack_mapping (Imp_LangTrickLanguage.Body func))
                    (Datatypes.length fidents)) (Datatypes.length fidents)) fenv_s
    (ns ++ stk ++ rho) ((map nenv'' fidents ++ ns) ++ stk ++ rho).
Proof.
  remember (Datatypes.length fidents) as fidents_len.
  revert Heqfidents_len. revert Heqfidents.
  remember (compile_imp (Imp_LangTrickLanguage.Body func) (stack_mapping (Imp_LangTrickLanguage.Body func)) fidents_len) as body_s.
  revert i.
  revert H0. revert ns.
  inversion FUN_WF.
  subst fenv0 wf_funcs f0 args.
  unfold fenv_well_formed' in FENV_WF. destruct FENV_WF as (FENV_WF & FENV_WF' & REST).
  
  induction fidents_len; intros.
  - simpl.
    eapply H0.
    + symmetry in e.
      apply FENV_WF' in e. destruct e as (_ & FUN_APP_BODY & _).
      assumption.
    + unfold fenv_well_formed'; split.
      eassumption.
      split; eassumption.
    + assumption.
    + ereflexivity.
    + assert (state_to_stack nil init_nenv ns ns).
      constructor. eassumption.
    + destruct fidents. simpl. econstructor.
      simpl in Heqfidents_len. invs Heqfidents_len.
    + unfold_wf_aexp_in H4.
      destruct fidents.
      symmetry in Heqfidents.
      eapply var_map_wf_imp_nil_trivial. assumption.
      simpl in Heqfidents_len. invs Heqfidents_len.
    + simpl.
      rewrite Heqbody_s.
      unfold stack_mapping.
      rewrite <- Heqfidents.
      destruct fidents.
      simpl. reflexivity.
      simpl in Heqfidents_len. invs Heqfidents_len.
  - simpl. destruct fidents.
    simpl in Heqfidents_len. invs Heqfidents_len. simpl in *.
    rewrite app_comm_cons. simpl. rewrite prepend_push_commutes. econstructor.
    + econstructor. ereflexivity.
    + rewrite app_comm_cons. rewrite app_comm_cons. eapply remove_prepend_push. rewrite app_assoc.
      eapply H0.
      * symmetry in e. apply FENV_WF' in e. destruct e as (_ & FUN_APP_BODY & _). assumption.
      * unfold fenv_well_formed'; (split; [ | split ]); assumption.
      * assumption.
      * ereflexivity.
      * assert (0 :: ns = 0 :: nil ++ ns) by (reflexivity).
        rewrite H. rewrite app_comm_cons. rewrite app_assoc. rewrite repeat_add_last. rewrite Heqfidents_len. change (S (Datatypes.length fidents)) with (Datatypes.length (i0 :: fidents)). rewrite <- init_fenv_map_is_repeat_0 with (idents := i0 :: fidents). econstructor.
      * rewrite app_comm_cons. rewrite <- map_cons. econstructor.
      * eapply var_map_wf_imp_self_imp_rec_rel. symmetry. assumption.
      * rewrite Heqbody_s. simpl. rewrite <- Heqfidents_len. unfold stack_mapping. rewrite <- Heqfidents. simpl. reflexivity.
Qed.

Lemma nth_error_map_commute_kinda :
  forall (A B: Type) (alist: list A) (a: A) (f: A -> B) (n: nat),
    nth_error alist n = Some a ->
    nth_error (map f alist) n = Some (f a).
Proof.
  induction alist; intros.
  - destruct n; simpl in H; invs H.
  - destruct n; simpl in H.
    + invs H. simpl. reflexivity.
    + simpl. apply IHalist. assumption.
Qed.
                                     
Theorem compiler_sound_mut_ind :
  forall (funcs: list fun_Imp_Lang),
    imp_langtrick_sem_mut_ind_theorem (P_compiler_sound funcs) (P0_compiler_sound funcs) (P1_compiler_sound funcs) (P2_compiler_sound funcs).
Proof.
  unfold imp_langtrick_sem_mut_ind_theorem, P_compiler_sound, P0_compiler_sound, P1_compiler_sound, P2_compiler_sound.
  intros funcs.
  imp_langtrick_sem_mutual_induction' P P0 P1 P2 (P_compiler_sound funcs) (P0_compiler_sound funcs) (P1_compiler_sound funcs) (P2_compiler_sound funcs) P_compiler_sound P0_compiler_sound P1_compiler_sound P2_compiler_sound; intros.
  - simpl in H4. subst. invs H1. invs H2.
    constructor.
  - simpl in H6. subst. invs FUN_WF. eapply Stack_if_true.
    + eapply H.
      assumption. assumption.
      reflexivity. ereflexivity. eassumption.
      apply imp_rec_rel_self in H5.
      unfold_wf_imp_in H5.
      invs WF'. assumption. reflexivity.
    + eapply H0; eauto. invs H5. assumption.
  - simpl in H6. rewrite H6. clear H6. clear i_stk. inversion FUN_WF. subst fenv0 wf_funcs b0 i0 i3. eapply Stack_if_false.
    + eapply H; eauto. eapply imp_rec_rel_self in H5. unfold_wf_imp_in H5. invs WF'. assumption.
    + eapply H0; eauto. invs H5. assumption.
  - simpl in H5. rewrite H5. clear H5. clear i_stk.
    eapply imp_rec_rel_self in H4. unfold_wf_imp_in H4.
    inversion FUN_WF. subst fenv0 wf_funcs x0 a1.
    assert (In x idents).
    {
      eapply WF''. constructor. eapply String.eqb_eq. reflexivity.
    }
    econstructor.
    + apply one_index_opt_always_geq_1.
    + remember (one_index_opt x idents) as index.
      assert (imp_has_variable x (ASSIGN_Imp_Lang x a)).
      constructor. eapply String.eqb_eq. reflexivity.
      apply WF'' in H5.
      eapply inside_implies_within_range' with (index := index) in H5.
      invs H2. rewrite app_length. rewrite app_length. rewrite map_length.
      eapply Plus.le_plus_trans.
      eapply Plus.le_plus_trans. assumption.
      symmetry. assumption.
    + eapply H. assumption. assumption.
      assumption. eassumption. eassumption.
      invs WF'. assumption.
      reflexivity.
    + invs H3. invs H2. eapply stack_mutated_prefix_OK.
      pose proof (inside_implies_within_range').
      specialize (H0 idents x (one_index_opt x idents) H4 eq_refl).
      rewrite app_length. rewrite map_length. eapply Plus.le_plus_trans. assumption.
      eapply stack_mutated_prefix_OK.
      rewrite map_length. apply inside_implies_within_range' with (x := x).
      assumption. reflexivity.
      eapply stack_mutated_at_index_of_update. assumption. destruct WF as (WF & _). assumption.
  - simpl in H5. rewrite H5. clear H5. clear i_stk.
    pose proof (H5 := H4).
    eapply imp_rec_rel_self in H5. unfold_wf_imp_in H5.
    constructor.
    invs FUN_WF.
    invs H2. invs H3. eapply H; eauto.
    invs WF'. assumption.
  - simpl in H7. rewrite H7. clear H7. clear i_stk.
    revert H2. revert H3.
    invc H6.
    unfold_wf_imp_in H9. invs FUN_WF. intros.
    eapply Stack_while_step.
    + eapply H; eauto. invs WF'. assumption.
    + eapply H0; eauto. econstructor.
    + eapply H1; eauto.
      * econstructor.
      * econstructor. assumption.
        unfold_wf_imp; assumption.
  - simpl in H6. rewrite H6. clear H6. clear i_stk.
    revert H2. revert H3.
    invc H5.
    invs FUN_WF.
    unfold_wf_imp_in H9. intros.
    econstructor; [ eapply H | eapply H0 ]; eauto.
    + econstructor.
    + econstructor.
  - simpl in H3. rewrite H3. constructor.
  - simpl in H3. rewrite H3.
    unfold_wf_aexp_in H2.
    constructor.
    eapply one_index_opt_always_geq_1. invs H1.
    repeat rewrite app_length. rewrite map_length. repeat eapply Plus.le_plus_trans.
    
    eapply inside_implies_within_range'.
    eapply A. ereflexivity. simpl. left. reflexivity. reflexivity.
    invs H1.
    destruct WF as (NODUP & FIND_OPT & IN & _).
    assert (In x idents).
    {
      eapply A. reflexivity. simpl. left. reflexivity.
    }
    specialize (find_index_rel_in_stronger idents x H NODUP). intros.
    destruct H0.
    specialize (find_index_rel_within_range idents x x0 H0). intros.
    specialize (FIND_OPT x x0 H2). destruct FIND_OPT as (FIND_OPT & _).
    specialize (FIND_OPT H0). rewrite FIND_OPT.
    rewrite <- app_assoc.
    rewrite successor_minus_one_same.
    specialize (in_map nenv idents x H). intros.
    apply In_nth_error in H. destruct H.
    apply nth_error_vs_find_index_rel in H0. destruct H0.
    pose proof (map_length).
    specialize (H5 string nat nenv idents).
    erewrite <- map_length in H2.
    erewrite nth_error_app1.
    eapply map_nth_error with (f := nenv) in H0. assumption.
    destruct H2. eassumption.
  - simpl in H3. rewrite H3.
    clear H3. clear a_stk. constructor.
    lia.
    rewrite app_length. invs H1. rewrite app_length. rewrite map_length.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    eapply Plus.plus_le_compat_l.
    lia.
    invs H1. rewrite <- app_assoc.
    erewrite nth_error_app2.
    rewrite map_length.
    remember ((Nat.sub
             (Nat.add (Nat.add (@Datatypes.length ident idents) n) (S O))
             (S O))) as SUB.
    remember (Nat.add (@Datatypes.length ident idents) n) as ADD.
    rewrite PeanoNat.Nat.add_comm in HeqSUB.
    erewrite Minus.minus_plus in HeqSUB.
    rewrite HeqADD in HeqSUB. rewrite HeqSUB.
    erewrite Minus.minus_plus.
    rewrite nth_error_app1. assumption.
    destruct a. assumption.
    rewrite PeanoNat.Nat.add_sub. rewrite map_length. apply PeanoNat.Nat.le_add_r.
  - simpl in H5. rewrite H5. clear H5. clear a_stk.
    eapply var_map_wf_plus_imp_lang_forwards in H4. destruct H4.
    inversion FUN_WF.
    subst fenv0 wf_funcs a3 a4.
    econstructor.
    + eapply H; eauto.
    + eapply H0; eauto.
  - simpl in H5. rewrite H5. clear H5. clear a_stk.
    eapply var_map_wf_minus_imp_lang_forwards in H4. destruct H4.
    inversion FUN_WF. subst fenv0 wf_funcs a3 a4.
    econstructor.
    + eapply H; eauto.
    + eapply H0; eauto.
  - simpl in H5. rewrite H5. clear H5. clear a_stk.
    remember (fenv_s f) as func'.
    pose proof (Hfunc' := Heqfunc').
    rewrite H1 in Heqfunc'. unfold compile_fenv in Heqfunc'. unfold compile_function in Heqfunc'. rewrite e in Heqfunc'.
    remember (pre_compile_function func) as COMPD.
    unfold pre_compile_function in HeqCOMPD.
    rewrite e0 in HeqCOMPD.
    rewrite HeqCOMPD in Heqfunc'. simpl in Heqfunc'.
    remember (construct_trans (Imp_LangTrickLanguage.Body func)) as fidents.
    assert (imp_stack_sem
    (prepend_push
       (compile_imp (Imp_LangTrickLanguage.Body func)
          (stack_mapping (Imp_LangTrickLanguage.Body func))
          (Datatypes.length fidents)) (Datatypes.length fidents)) fenv_s
    (ns ++ stk ++ rho) (((map nenv'' fidents) ++ ns) ++ stk ++ rho)) by (eapply big_step_away_pushes; eassumption).
    inversion FUN_WF. subst fenv0 wf_funcs f0 args.
    econstructor.
    + symmetry in Hfunc'. eassumption.
    + rewrite Heqfunc'. simpl. ereflexivity.
    + rewrite Heqfunc'. simpl. ereflexivity.
    + rewrite Heqfunc'. simpl. ereflexivity.
    + rewrite map_length. apply args_Imp_Lang_preserves_length in a.
      rewrite a. reflexivity. 
    + eapply H; eauto.
      induction aexps.
      * constructor.
      * eapply var_map_wf_app_imp_lang_args_all; eauto.
    + rewrite Heqfunc'. simpl. eapply H5.
    + assert (func0 = func) by (rewrite H9, e; reflexivity).
      subst func0. rewrite H6 in H10, H15, H14, H11.
      eapply free_vars_in_imp_has_variable in H14; [ | eauto ].
      assert (In (Ret func) (construct_trans (Imp_LangTrickLanguage.Body func))).
      {
        unfold construct_trans. eapply fold_left_containment_helper.
        assumption.
      } 
      econstructor.
      * unfold stack_mapping. eapply one_index_opt_always_geq_1.
      * unfold stack_mapping. repeat rewrite app_length. rewrite map_length. rewrite Heqfidents.

        pose proof (inside_implies_within_range).
        specialize (H9 (construct_trans (Imp_LangTrickLanguage.Body func)) (Ret func) (Nat.pred (one_index_opt (Ret func) (construct_trans (Imp_LangTrickLanguage.Body func)))) H7).
        assert (one_index_opt (Ret func) (construct_trans (Imp_LangTrickLanguage.Body func)) =
                  S (Nat.pred (one_index_opt (Ret func) (construct_trans (Imp_LangTrickLanguage.Body func))))).
        rewrite <- Lt.S_pred_pos. reflexivity.
        specialize (one_index_opt_always_geq_1 (Ret func) (construct_trans (Imp_LangTrickLanguage.Body func))).
        intros.
        lia.
        apply H9 in H12. destruct H12. apply PeanoNat.Nat.lt_pred_le in H13.
        rewrite <- PeanoNat.Nat.add_assoc.
        apply Plus.le_plus_trans. assumption.
      * unfold stack_mapping.
        pose proof (IN := H7).
        eapply in_idents_one_index_opt in H7; [ | eapply nodup_construct_trans ].
        destruct H7.
        specialize (one_index_opt_always_geq_1 (Ret func) fidents).
        intros.
        rewrite Heqfidents in H9. assert (1 <= x) by (rewrite <- H7; assumption).
        destruct x; [ invs H12 | ].
        rewrite H7. rewrite successor_minus_one_same.
        pose proof (INSIDE := inside_implies_within_range).
        specialize (INSIDE (construct_trans (Imp_LangTrickLanguage.Body func)) (Ret func) x IN H7).
        rewrite <- Heqfidents in INSIDE.
        erewrite <- map_length with (f := nenv'') in INSIDE.
        erewrite nth_error_app1.
        rewrite nth_error_app1.
        2: destruct INSIDE; assumption.
        2: destruct INSIDE; rewrite app_length; apply Plus.lt_plus_trans; assumption.
        rewrite nth_error_map.
        rewrite map_length in INSIDE. rewrite Heqfidents in INSIDE.
        destruct INSIDE.
        eapply one_index_opt_vs_nth_error in H7; [ | try lia; try assumption .. ].
        rewrite Heqfidents.
        rewrite <- nth_error_map.
        apply nth_error_map_commute_kinda with (B := nat) (f := nenv'') in H7.
        rewrite e1 in H7. assumption.
    + enough ((Datatypes.length aexps + Datatypes.length fidents) = Datatypes.length (map nenv'' fidents ++ ns)).
      -- apply (same_after_popping_length1 (stk ++ rho) ((map nenv'' fidents ++ ns)) (stk ++ rho) (Datatypes.length aexps + Datatypes.length fidents)).
        symmetry; assumption. reflexivity.  
      -- rewrite app_length. rewrite map_length. rewrite PeanoNat.Nat.add_comm. 
        eapply args_Imp_Lang_preserves_length in a. rewrite a. reflexivity. 
  - rewrite H3. simpl. econstructor.
  - rewrite H3. simpl. econstructor.
  - rewrite H4. simpl. econstructor.
    inversion FUN_WF. subst fenv0 wf_funcs b1.
    + eapply H; eauto.
      eapply var_map_wf_neg_imp_lang; eauto.
    + reflexivity.
  - rewrite H5. simpl. eapply var_map_wf_and_or_imp_lang_forwards in H4. destruct H4. inversion FUN_WF. subst fenv0 wf_funcs b3 b4.  econstructor.
    + eapply H. assumption. assumption. assumption. eassumption. eassumption. eapply H4. reflexivity.
    + eapply H0. assumption. assumption. assumption. eassumption. eassumption. eassumption. reflexivity.
    + reflexivity.
    + left. reflexivity.
  - rewrite H5. simpl. eapply var_map_wf_and_or_imp_lang_forwards in H4. destruct H4. inversion FUN_WF. subst fenv0 wf_funcs b3 b4. econstructor.
    + eapply H. assumption. assumption. assumption. eassumption. eassumption. eapply H4. reflexivity.
    + eapply H0. assumption. assumption. assumption. eassumption. eassumption. eassumption. reflexivity.
    + reflexivity.
    + right. reflexivity.
  - rewrite H5. simpl. eapply var_map_wf_leq_imp_lang_forwards in H4. destruct H4. inversion FUN_WF. subst fenv0 wf_funcs a3 a4. econstructor.
    + eapply H. assumption. assumption. assumption. eassumption. eassumption. eapply H4. reflexivity.
    + eapply H0. assumption. assumption. assumption. eassumption. eassumption. eassumption. reflexivity.
    + reflexivity.
    + reflexivity.
  - rewrite H3. simpl. econstructor.
  - rewrite H5. simpl. inversion FUN_WF. subst fenv0 wf_funcs arg args. econstructor.
    + eapply H; eauto. invs H4. assumption.
    + eapply H0; eauto. invs H4. assumption.
Qed.

    
Theorem compiler_sound :
  forall n_args idents fenv_d fenv_s func_list,
    fenv_well_formed' func_list fenv_d ->
    fenv_s = compile_fenv fenv_d -> 
    (forall aD aS,
        aS = compile_aexp
               aD
               (fun x => one_index_opt x idents)
               (List.length idents) ->
        fun_app_well_formed fenv_d func_list aD ->
        var_map_wf_wrt_aexp idents aD ->
        forall nenv dbenv stk n rho, 
          List.length dbenv = n_args -> 
          state_to_stack idents nenv dbenv stk ->
          a_Imp_Lang aD dbenv fenv_d nenv n -> 
          aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n)) /\
      (forall bD bS,
          bS = compile_bexp
                 bD
                 (fun x => one_index_opt x idents)
                 (List.length idents) ->
          fun_app_bexp_well_formed fenv_d func_list bD ->
          var_map_wf_wrt_bexp idents bD ->
          forall nenv dbenv stk bl rho, 
            List.length dbenv = n_args -> 
            state_to_stack idents nenv dbenv stk -> 
            b_Imp_Lang bD dbenv fenv_d nenv bl -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl)).
Proof.
  pose proof (SOUND := compiler_sound_mut_ind).
  intros.
  unfold imp_langtrick_sem_mut_ind_theorem, P_compiler_sound, P0_compiler_sound, P1_compiler_sound, P2_compiler_sound in SOUND. specialize (SOUND func_list).
  destruct SOUND as (_ & AEXP & BEXP & _).
  split; intros.
  - eapply AEXP; try eassumption.
  - eapply BEXP; try eassumption.
Qed.

Lemma aexp_compiler_sound :
  forall n_args idents fenv_d fenv_s func_list,
    fenv_well_formed' func_list fenv_d ->
    fenv_s = compile_fenv fenv_d -> 
    forall aD aS,
        aS = compile_aexp
               aD
               (fun x => one_index_opt x idents)
               (List.length idents) ->
        fun_app_well_formed fenv_d func_list aD ->
        var_map_wf_wrt_aexp idents aD ->
        forall nenv dbenv stk n rho, 
          List.length dbenv = n_args -> 
          state_to_stack idents nenv dbenv stk ->
          a_Imp_Lang aD dbenv fenv_d nenv n -> 
          aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n).
Proof.
  pose proof (SOUND := compiler_sound).
  intros.
  specialize (SOUND n_args idents fenv_d fenv_s func_list H H0).
  destruct SOUND as (AEXP & _).
  eapply AEXP; eassumption.
Qed.

Lemma bexp_compiler_sound :
  forall n_args idents fenv_d fenv_s func_list,
    fenv_well_formed' func_list fenv_d ->
    fenv_s = compile_fenv fenv_d -> 
    forall bD bS,
      bS = compile_bexp
             bD
             (fun x => one_index_opt x idents)
             (List.length idents) ->
      fun_app_bexp_well_formed fenv_d func_list bD ->
      var_map_wf_wrt_bexp idents bD ->
      forall nenv dbenv stk bl rho, 
        List.length dbenv = n_args -> 
        state_to_stack idents nenv dbenv stk -> 
        b_Imp_Lang bD dbenv fenv_d nenv bl -> 
        bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl).
Proof.
  pose proof (SOUND := compiler_sound).
  intros. specialize (SOUND n_args idents fenv_d fenv_s func_list H H0).
  destruct SOUND as (_ & BEXP).
  eapply BEXP; eassumption.
Qed.
     
