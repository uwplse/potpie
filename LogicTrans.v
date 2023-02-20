From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From DanTrick Require Import DanTrickLanguage DanLogProp DanLogicHelpers 
  StackLanguage StackLangEval EnvToStack StackLogicGrammar LogicProp TranslationPure FunctionWellFormed ImpVarMap ImpVarMapTheorems StackLangTheorems.

From DanTrick Require Export LogicTranslationBase ParamsWellFormed FunctionWellFormed.

Lemma compile_bool_args_sound_pos :  
  forall (vals: list bool) (sargs: list bexp_stack) (dargs: list bexp_Dan) (num_args: nat) (idents: list ident),
    compile_bool_args num_args idents dargs sargs -> 
    forall fenv_d fenv_s func_list,
    forall (FENV_WF: fenv_well_formed' func_list fenv_d),
      fenv_s = compile_fenv fenv_d -> 
      (forall aD aS,
          aS = compile_aexp aD (fun x => one_index_opt x idents) (List.length idents) ->
          forall (FUN_APP_AEXP: fun_app_well_formed fenv_d func_list aD),
          forall (MAP_WF_AEXP: var_map_wf_wrt_aexp idents aD),
          forall nenv dbenv stk n rho, 
            List.length dbenv = num_args -> 
            state_to_stack idents nenv dbenv stk -> 
            a_Dan aD dbenv fenv_d nenv n -> 
            aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n)) ->
      (forall bD bS,
          bS = compile_bexp bD (fun x => one_index_opt x idents) (List.length idents) ->
          forall (FUN_APP_BEXP: fun_app_bexp_well_formed fenv_d func_list bD),
          forall (MAP_WF_BEXP: var_map_wf_wrt_bexp idents bD),
          forall nenv dbenv stk bl rho, 
            List.length dbenv = num_args -> 
            state_to_stack idents nenv dbenv stk -> 
            b_Dan bD dbenv fenv_d nenv bl -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl)) -> 
      forall nenv dbenv,
        List.length dbenv = num_args -> 
        (eval_prop_args_rel
           (fun (b : bexp_Dan) (v : bool) =>
              b_Dan b dbenv fenv_d nenv v) dargs vals) ->
        forall (ARGS_FUN_APP: prop_args_rel (V := bool) (fun_app_bexp_well_formed fenv_d func_list) dargs),
        forall (ARGS_MAP_WF: prop_args_rel (V := bool) (var_map_wf_wrt_bexp idents) dargs),
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
            eval_prop_args_rel
              (fun (boolexpr : bexp_stack) (boolval : bool) =>
                 bexp_stack_sem boolexpr (compile_fenv fenv_d) 
                                (stk ++ rho) (stk ++ rho, boolval)) sargs vals. 
Proof.
  induction vals. 
  - intros. inversion H4. subst. inversion H. subst.
    inversion H0. subst. apply RelArgsNil.
  - intros. inversion H4. subst. inversion H. subst. inversion H0. subst.
    inversion ARGS_FUN_APP. inversion ARGS_MAP_WF. subst.
    apply RelArgsCons.
    + pose proof (BEXP := H2 arg (comp_bool idents arg)). 
      eapply BEXP.
      -- unfold comp_bool. auto.
      -- eauto.
      -- eauto.
      -- eapply eq_refl.
      -- apply H5.
      -- auto. 
    + pose proof (IHvals args' args (Datatypes.length dbenv) idents) as int.
      pose proof (CompiledBoolArgs idents (Datatypes.length dbenv) args args' H9).
      pose proof (int H3 fenv_d (compile_fenv fenv_d)) as int2.
      pose proof (eq_refl (compile_fenv fenv_d)) as eq.
      pose proof (int2 func_list FENV_WF eq H1 H2 nenv dbenv) as int3.
      pose proof (eq_refl (Datatypes.length dbenv)) as eq2.
      pose proof (int3 eq2 H11 H12 H17 stk H5 rho) as conc.
      apply conc.
Qed.  

Lemma compile_arith_args_sound_pos :  
forall vals sargs dargs num_args idents,
  compile_arith_args num_args idents dargs sargs -> 
  forall fenv_d fenv_s func_list,
    forall (FENV_WF: fenv_well_formed' func_list fenv_d),
    fenv_s = compile_fenv fenv_d -> 
    (forall aD aS,
          aS = compile_aexp aD (fun x => one_index_opt x idents) (List.length idents) ->
          forall (FUN_APP_AEXP: fun_app_well_formed fenv_d func_list aD),
          forall (MAP_WF_AEXP: var_map_wf_wrt_aexp idents aD),
          forall nenv dbenv stk n rho, 
            List.length dbenv = num_args -> 
            state_to_stack idents nenv dbenv stk -> 
            a_Dan aD dbenv fenv_d nenv n -> 
            aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n)) ->
      (forall bD bS,
          bS = compile_bexp bD (fun x => one_index_opt x idents) (List.length idents) ->
          forall (FUN_APP_BEXP: fun_app_bexp_well_formed fenv_d func_list bD),
          forall (MAP_WF_BEXP: var_map_wf_wrt_bexp idents bD),
          forall nenv dbenv stk bl rho, 
            List.length dbenv = num_args -> 
            state_to_stack idents nenv dbenv stk -> 
            b_Dan bD dbenv fenv_d nenv bl -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl)) -> 
    forall nenv dbenv,
      List.length dbenv = num_args -> 
      (eval_prop_args_rel
      (fun (b : aexp_Dan) (v : nat) =>
         a_Dan b dbenv fenv_d nenv v) dargs vals) ->
      forall (ARGS_FUN_APP: prop_args_rel (V := nat) (fun_app_well_formed fenv_d func_list) dargs),
      forall (ARGS_MAP_WF: prop_args_rel (V := nat) (var_map_wf_wrt_aexp idents) dargs),
      forall stk,
        state_to_stack idents nenv dbenv stk -> 
        forall rho, 
          eval_prop_args_rel
          (fun (boolexpr : aexp_stack) (boolval : nat) =>
          aexp_stack_sem boolexpr (compile_fenv fenv_d) 
            (stk ++ rho) (stk ++ rho, boolval)) sargs vals. 
Proof.
  induction vals. 
  - intros. inversion H4. subst. inversion H. subst.
    inversion H0. subst. apply RelArgsNil.
  - intros. inversion H4. subst. inversion H. subst. inversion H0. subst.
    inversion ARGS_FUN_APP. inversion ARGS_MAP_WF. subst.
    apply RelArgsCons.
    + pose proof (AEXP := H1 arg (comp_arith idents arg)). 
      eapply AEXP.
      -- auto.
      -- auto.
      -- auto.
      -- reflexivity.
      -- eauto.
      -- eauto.
    + pose proof (IHvals args' args (Datatypes.length dbenv) idents) as int.
      pose proof (CompiledArithArgs idents (Datatypes.length dbenv) args args' H9).
      pose proof (int H3 fenv_d (compile_fenv fenv_d)) as int2.
      pose proof (eq_refl (compile_fenv fenv_d)) as eq.
      pose proof (int2 func_list FENV_WF eq H1 H2 nenv dbenv) as int3.
      pose proof (eq_refl (Datatypes.length dbenv)) as eq2.
      pose proof (int3 eq2 H11 H12 H17 stk H5 rho) as conc.
      apply conc.
Qed.

Lemma trans_sound_pos_assume_comp_basestate_lp_aexp (idents : list DanTrickLanguage.ident)
      (dbenv : list nat)
      (fenv_d : fun_env)
      (func_list : list fun_Dan)
      (FENV_WF : fenv_well_formed' func_list fenv_d)
      (H1 : forall (aD : aexp_Dan) (aS : aexp_stack),
          aS =
            compile_aexp aD (fun x : ident => one_index_opt x idents)
                         (Datatypes.length idents) ->
          fun_app_well_formed fenv_d func_list aD ->
          var_map_wf_wrt_aexp idents aD ->
          forall (nenv : nat_env) (dbenv0 stk : list nat)
            (n : nat) (rho : list nat),
            Datatypes.length dbenv0 = Datatypes.length dbenv ->
            state_to_stack idents nenv dbenv0 stk ->
            a_Dan aD dbenv0 fenv_d nenv n ->
            aexp_stack_sem aS (compile_fenv fenv_d) (stk ++ rho)
                           (stk ++ rho, n))
      (H2 : forall (bD : bexp_Dan) (bS : bexp_stack),
          bS =
            compile_bexp bD (fun x : ident => one_index_opt x idents)
                         (Datatypes.length idents) ->
          fun_app_bexp_well_formed fenv_d func_list bD ->
          var_map_wf_wrt_bexp idents bD ->
          forall (nenv : nat_env) (dbenv0 stk : list nat)
            (bl : bool) (rho : list nat),
            Datatypes.length dbenv0 = Datatypes.length dbenv ->
            state_to_stack idents nenv dbenv0 stk ->
            b_Dan bD dbenv0 fenv_d nenv bl ->
            bexp_stack_sem bS (compile_fenv fenv_d) (stk ++ rho)
                           (stk ++ rho, bl))
      (OKfuncs: funcs_okay_too func_list (compile_fenv fenv_d))
      (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
      (nenv : nat_env)
      (l : LogicProp nat aexp_Dan)
      (stk : list nat)
      (H5 : state_to_stack idents nenv dbenv stk)
      (rho : list nat)
      (FUN_APP : Dan_lp_prop_rel (fun_app_well_formed fenv_d func_list)
                                 (fun_app_bexp_well_formed fenv_d func_list)
                                 (Dan_lp_arith l))
      (MAP_WF : Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                                (var_map_wf_wrt_bexp idents) (Dan_lp_arith l))
      (H0 : Dan_lp_rel (Dan_lp_arith l) fenv_d dbenv nenv)
      (s : LogicProp nat aexp_stack)
      (TRANSLATE : lp_transrelation (Datatypes.length dbenv) idents
                              (Dan_lp_arith l) (MetaNat s)):
  meta_match_rel (MetaNat s) (compile_fenv fenv_d) (stk ++ rho).
Proof.
  invc FUN_APP. invc MAP_WF. invc TRANSLATE. invc H9. invc H0.
  constructor.
  - Tactics.revert_until s.
    revert l.
    induction s; intros; invc H.
    + constructor.
    + invs H4.
    + invs H4. econstructor.
      * eapply H1; try eauto.
        reflexivity. invs H6. assumption. invs H7. assumption.
      * assumption.
    + invs H4. invs H7. invs H6. econstructor.
      * eapply H1; [reflexivity | | | reflexivity | .. ]; eassumption.
      * eapply H1; [reflexivity | | | reflexivity | .. ]; eassumption.
      * assumption.
    + invs H4. invs H6. invs H7. econstructor.
      * eapply IHs1. eapply H12. eassumption. assumption. assumption.
      * eapply IHs2; [ eapply H13 | eassumption .. ].
    + invs H6. invs H7. invs H4; [eapply RelOrPropLeft | eapply RelOrPropRight].
      * eapply IHs1; [ eapply H8 | eassumption .. ].
      * eapply IHs2; [ eapply H9 | eassumption .. ].
    + invs H4. invs H6. invs H7. econstructor; [ eapply H1; try reflexivity .. |]; eassumption.
    + invs H4. invs H6. invs H7. econstructor; [ | eassumption ].
      eapply compile_arith_args_sound_pos; try eassumption.
      econstructor. assumption. reflexivity. reflexivity.
  - Tactics.revert_until s. revert l.
    induction s; intros; invs H.
    + constructor.
    + invs H4.
    + invs H4. eapply arith_compile_prop_rel_implies_pure'; eauto.
    + invs H4. invs H6. invs H7.
      eapply arith_compile_prop_rel_implies_pure'; eauto.
    + invs H4. invs H6. invs H7.
      econstructor; [ eapply IHs1; [ eapply H13 | ..] | eapply IHs2; [ eapply H14 | .. ]]; eauto.
    + invs H6.
      eapply arith_compile_prop_rel_implies_pure'; eauto.
    + invs H6. eapply arith_compile_prop_rel_implies_pure'; eauto.
    + invs H6. invs H7. constructor. eapply arith_compile_prop_args_rel_implies_pure'; eauto.
Qed.
    
Lemma trans_sound_pos_assume_comp_basestate_lp_bexp (idents : list DanTrickLanguage.ident)
      (dbenv : list nat)
      (fenv_d : fun_env)
      (func_list : list fun_Dan)
      (FENV_WF : fenv_well_formed' func_list fenv_d)
      (H1 : forall (aD : aexp_Dan) (aS : aexp_stack),
          aS =
            compile_aexp aD (fun x : ident => one_index_opt x idents)
                         (Datatypes.length idents) ->
          fun_app_well_formed fenv_d func_list aD ->
          var_map_wf_wrt_aexp idents aD ->
          forall (nenv : nat_env) (dbenv0 stk : list nat)
            (n : nat) (rho : list nat),
            Datatypes.length dbenv0 = Datatypes.length dbenv ->
            state_to_stack idents nenv dbenv0 stk ->
            a_Dan aD dbenv0 fenv_d nenv n ->
            aexp_stack_sem aS (compile_fenv fenv_d) (stk ++ rho)
                           (stk ++ rho, n))
      (H2 : forall (bD : bexp_Dan) (bS : bexp_stack),
          bS =
            compile_bexp bD (fun x : ident => one_index_opt x idents)
                         (Datatypes.length idents) ->
          fun_app_bexp_well_formed fenv_d func_list bD ->
          var_map_wf_wrt_bexp idents bD ->
          forall (nenv : nat_env) (dbenv0 stk : list nat)
            (bl : bool) (rho : list nat),
            Datatypes.length dbenv0 = Datatypes.length dbenv ->
            state_to_stack idents nenv dbenv0 stk ->
            b_Dan bD dbenv0 fenv_d nenv bl ->
            bexp_stack_sem bS (compile_fenv fenv_d) (stk ++ rho)
                           (stk ++ rho, bl))
      (OKfuncs: funcs_okay_too func_list (compile_fenv fenv_d))
      (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
      (nenv : nat_env)
      (s : LogicProp bool bexp_stack)
      (l : LogicProp bool bexp_Dan)
      (H4 : AbsEnv_rel (AbsEnvLP (Dan_lp_bool l)) fenv_d dbenv nenv)
      (stk : list nat)
      (H5 : state_to_stack idents nenv dbenv stk)
      (rho : list nat)
      (FUN_APP : Dan_lp_prop_rel (fun_app_well_formed fenv_d func_list)
                                 (fun_app_bexp_well_formed fenv_d func_list)
                                 (Dan_lp_bool l))
      (MAP_WF : Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                                (var_map_wf_wrt_bexp idents) (Dan_lp_bool l))
      (H : prop_rel (var_map_wf_wrt_bexp idents) l)
      (TRANSLATE : compile_prop_rel (comp_bool idents) l s):
  meta_match_rel (MetaBool s) (compile_fenv fenv_d) (stk ++ rho).
Proof.
  invc FUN_APP. invc MAP_WF. invc H4. invc H3.
  constructor.
  - Tactics.revert_until s.
    induction s; intros; invs TRANSLATE.
    + constructor.
    + invs H4.
    + invs H4. invs H7. invs H8. econstructor; [ | eassumption ].
      eapply H2; try reflexivity; try eassumption.
    + invs H4. invs H7. invs H8. econstructor; [ .. | eassumption ].
      all: eapply H2; try reflexivity; try eassumption.
    + invs H4. invs H7. invs H8. econstructor; [ eapply IHs1; [ | eapply H15 | .. ] | eapply IHs2; [ | eapply H16 | .. ]]; eassumption.
    + invs H7. invs H8. invs H4.
      * eapply RelOrPropLeft. eapply IHs1; [ | eapply H13 | .. ]; eassumption.
      * eapply RelOrPropRight. eapply IHs2; [ | eapply H14 | .. ]; eassumption.
    + invs H4. invs H7. invs H8.
      econstructor; [ .. | eassumption ].
      all: eapply H2; try reflexivity; try eassumption.
    + invs H4. invs H7. invs H8. econstructor; [ | eassumption ].
      eapply compile_bool_args_sound_pos; try reflexivity;
        try eassumption.
      constructor. assumption.
  - Tactics.revert_until s.
    induction s; intros; invs TRANSLATE.
    + constructor.
    + constructor.
    + invs H7. invs H8. eapply bool_compile_prop_rel_implies_pure'; try eassumption.
      reflexivity. reflexivity.
    + invs H7. invs H8. eapply bool_compile_prop_rel_implies_pure'; eauto.
    + invs H7. invs H8. eapply bool_compile_prop_rel_implies_pure'; eauto.
    + invs H7. invs H8. eapply bool_compile_prop_rel_implies_pure'; eauto.
    + invs H7. invs H8. eapply bool_compile_prop_rel_implies_pure'; eauto.
    + invs H7. invs H8. constructor.  eapply bool_compile_prop_args_rel_implies_pure'; eauto.
Qed.

          

Lemma trans_sound_pos_assume_comp_basestate (m : MetavarPred)
      (idents : list DanTrickLanguage.ident)
      (dbenv : list nat)
      (d : Dan_lp)
      (fenv_d : fun_env)
      (func_list : list fun_Dan)
      (FENV_WF : fenv_well_formed' func_list fenv_d)
      (H1 : forall (aD : aexp_Dan) (aS : aexp_stack),
          aS =
            compile_aexp aD (fun x : ident => one_index_opt x idents)
                         (Datatypes.length idents) ->
          fun_app_well_formed fenv_d func_list aD ->
          var_map_wf_wrt_aexp idents aD ->
          forall (nenv : nat_env) (dbenv0 stk : list nat)
            (n : nat) (rho : list nat),
            Datatypes.length dbenv0 = Datatypes.length dbenv ->
            state_to_stack idents nenv dbenv0 stk ->
            a_Dan aD dbenv0 fenv_d nenv n ->
            aexp_stack_sem aS (compile_fenv fenv_d) (stk ++ rho)
                           (stk ++ rho, n))
      (H2 : forall (bD : bexp_Dan) (bS : bexp_stack),
          bS =
            compile_bexp bD (fun x : ident => one_index_opt x idents)
                         (Datatypes.length idents) ->
          fun_app_bexp_well_formed fenv_d func_list bD ->
          var_map_wf_wrt_bexp idents bD ->
          forall (nenv : nat_env) (dbenv0 stk : list nat)
            (bl : bool) (rho : list nat),
            Datatypes.length dbenv0 = Datatypes.length dbenv ->
            state_to_stack idents nenv dbenv0 stk ->
            b_Dan bD dbenv0 fenv_d nenv bl ->
            bexp_stack_sem bS (compile_fenv fenv_d) (stk ++ rho)
                           (stk ++ rho, bl))
      (OKfuncs: funcs_okay_too func_list (compile_fenv fenv_d))
      (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
      (nenv : nat_env)
      (H4 : AbsEnv_rel (AbsEnvLP d) fenv_d dbenv nenv)
      (stk : list nat)
      (H5 : state_to_stack idents nenv dbenv stk)
      (rho : list nat)
      (H10 : lp_transrelation (Datatypes.length dbenv) idents d m)
      (H0 : Dan_lp_rel d fenv_d dbenv nenv)
      (MAP_WF : Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                             (var_map_wf_wrt_bexp idents) d)
      (FUN_APP : Dan_lp_prop_rel (fun_app_well_formed fenv_d func_list)
                             (fun_app_bexp_well_formed fenv_d func_list) d):
  absstate_match_rel
    (BaseState
       (AbsStkSize (Datatypes.length idents + Datatypes.length dbenv)) m)
    (compile_fenv fenv_d) (stk ++ rho).
Proof.
  constructor.
  - constructor.
    inversion H5. simpl. rewrite app_length. rewrite app_length. rewrite map_length. lia.
  - inversion MAP_WF. subst. invs FUN_APP. invs H10. invs H9.
    clear H9. eapply trans_sound_pos_assume_comp_basestate_lp_aexp; eauto.
    subst. invc H10. invc H8; eauto.
    eapply trans_sound_pos_assume_comp_basestate_lp_bexp; eauto.
Qed.





Lemma trans_sound_pos_assume_comp : 
  forall state dan_log num_args idents, 
    logic_transrelation num_args idents dan_log state -> 
    forall fenv_d fenv_s func_list,
    forall (FENV_WF: fenv_well_formed' func_list fenv_d)
      (OKfuncs: funcs_okay_too func_list (compile_fenv fenv_d))
      (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list),
      fenv_s = compile_fenv fenv_d -> 
      (forall aD aS,
          aS = compile_aexp aD (fun x => one_index_opt x idents) (List.length idents) ->
          forall (FUN_APP_AEXP: fun_app_well_formed fenv_d func_list aD),
          forall (MAP_WF_AEXP: var_map_wf_wrt_aexp idents aD),
          forall nenv dbenv stk n rho, 
            List.length dbenv = num_args -> 
            state_to_stack idents nenv dbenv stk -> 
            a_Dan aD dbenv fenv_d nenv n -> 
            aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n)) ->
      (forall bD bS,
          bS = compile_bexp bD (fun x => one_index_opt x idents) (List.length idents) ->
          forall (FUN_APP_BEXP: fun_app_bexp_well_formed fenv_d func_list bD),
          forall (MAP_WF_BEXP: var_map_wf_wrt_bexp idents bD),
          forall nenv dbenv stk bl rho, 
            List.length dbenv = num_args -> 
            state_to_stack idents nenv dbenv stk -> 
            b_Dan bD dbenv fenv_d nenv bl -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl)) -> 
      forall nenv dbenv,
        List.length dbenv = num_args ->
        forall (FUN_APP: AbsEnv_prop_rel (fun_app_well_formed fenv_d func_list)
                                     (fun_app_bexp_well_formed fenv_d func_list)
                                     dan_log)
          (MAP_WF: AbsEnv_prop_rel (var_map_wf_wrt_aexp idents)
                                    (var_map_wf_wrt_bexp idents)
                                    dan_log),
        AbsEnv_rel dan_log fenv_d dbenv nenv -> 
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
            absstate_match_rel state fenv_s (stk ++ rho). 
Proof.
  induction state; intros.
  - inversion H. subst. clear H. inversion H4. inversion MAP_WF. inversion FUN_APP. subst.
    eapply trans_sound_pos_assume_comp_basestate; eauto.
    
  - invs H. invs H4. invs MAP_WF. invs FUN_APP.
    constructor.
    + eapply IHstate1; try eassumption; try reflexivity.
    + eapply IHstate2; try eassumption; try reflexivity.
  - invs H. invs MAP_WF. invs FUN_APP. invs H4.
    + eapply RelAbsOrLeft. eapply IHstate1; try eassumption; try reflexivity.
    + eapply RelAbsOrRight. eapply IHstate2; try eassumption; try reflexivity.
Qed.
