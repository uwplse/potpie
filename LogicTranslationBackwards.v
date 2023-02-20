From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From DanTrick Require Import DanTrickLanguage DanLogProp DanLogicHelpers 
  StackLanguage StackLangEval EnvToStack StackLogicGrammar LogicProp TranslationPure StackLangTheorems StackLogic.

From DanTrick Require Export LogicTranslationBase.

Lemma compile_bool_args_sound_pos_backwards :  
forall vals sargs dargs args map,
  compile_bool_args args map dargs sargs -> 
  forall fenv_d fenv_s,
    fenv_s = compile_fenv fenv_d -> 
    (forall aD aS,
        aS = compile_aexp aD (fun x => one_index_opt x map) (List.length map) -> 
        forall nenv dbenv stk n rho, 
          List.length dbenv = args -> 
          state_to_stack map nenv dbenv stk -> 
          aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
          a_Dan aD dbenv fenv_d nenv n) -> 
    (forall bD bS,
        bS = compile_bexp bD (fun x => one_index_opt x map) (List.length map) -> 
        forall nenv dbenv stk bl rho, 
          List.length dbenv = args -> 
          state_to_stack map nenv dbenv stk -> 
          bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl) -> 
          b_Dan bD dbenv fenv_d nenv bl) -> 
    forall nenv dbenv,
      List.length dbenv = args -> 
      forall stk,
        state_to_stack map nenv dbenv stk -> 
        forall rho, 
          eval_prop_args_rel
            (fun (boolexpr : bexp_stack) (boolval : bool) =>
               bexp_stack_sem boolexpr (compile_fenv fenv_d) 
                              (stk ++ rho) (stk ++ rho, boolval)) sargs vals ->
          (eval_prop_args_rel
             (fun (b : bexp_Dan) (v : bool) =>
                b_Dan b dbenv fenv_d nenv v) dargs vals).
Proof.
  induction vals; intros.
  - invs H5. invs H. invs H0. econstructor.
  - invs H5. invs H. invs H0.
    assert (compile_bool_args (Datatypes.length dbenv) map args args0) by (econstructor; assumption).
    
    econstructor.
    eapply H2.
    + eapply eq_refl.
    + reflexivity.
    + eassumption.
    + unfold comp_bool in H10. eassumption.
    + eapply IHvals.
      * eapply H3.
      * eapply eq_refl.
      * eassumption.
      * eassumption.
      * reflexivity.
      * eassumption.
      * eassumption.
Qed.


Lemma compile_arith_args_sound_pos_backwards :  
forall vals sargs dargs args map,
  compile_arith_args args map dargs sargs -> 
  forall fenv_d fenv_s,
    fenv_s = compile_fenv fenv_d -> 
    (forall aD aS,
      aS = compile_aexp aD (fun x => one_index_opt x map) (List.length map) -> 
      forall nenv dbenv stk n rho, 
        List.length dbenv = args -> 
        state_to_stack map nenv dbenv stk -> 
        aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
        a_Dan aD dbenv fenv_d nenv n) ->
    (forall bD bS,
      bS = compile_bexp bD (fun x => one_index_opt x map) (List.length map) -> 
      forall nenv dbenv stk bl rho, 
        List.length dbenv = args -> 
        state_to_stack map nenv dbenv stk -> 
        bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl) ->
        b_Dan bD dbenv fenv_d nenv bl) ->
    forall nenv dbenv,
      List.length dbenv = args -> 
      forall stk,
        state_to_stack map nenv dbenv stk -> 
        forall rho, 
          eval_prop_args_rel
          (fun (boolexpr : aexp_stack) (boolval : nat) =>
             aexp_stack_sem boolexpr (compile_fenv fenv_d) 
                            (stk ++ rho) (stk ++ rho, boolval)) sargs vals ->
          (eval_prop_args_rel
             (fun (b : aexp_Dan) (v : nat) =>
                a_Dan b dbenv fenv_d nenv v) dargs vals).
Proof.
  induction vals; intros; invs H5.
  - invs H. invs H0. econstructor.
  - invs H. invs H0.
    assert (compile_arith_args (Datatypes.length dbenv) map args args0) by (econstructor; assumption).
    
    econstructor.
    eapply H1.
    + eapply eq_refl.
    + reflexivity.
    + eassumption.
    + unfold comp_arith in H10. eassumption.
    + eapply IHvals.
      * eapply H3.
      * eapply eq_refl.
      * eassumption.
      * eassumption.
      * reflexivity.
      * eassumption.
      * eassumption.
Qed.

Lemma compile_bool_sound_backwards :
  forall dl sl args map,
    compile_prop_rel (comp_bool map) dl sl ->
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      (forall aD aS,
          aS = compile_aexp aD
                            (fun x => one_index_opt x map)
                            (List.length map) -> 
          forall nenv dbenv stk n rho, 
            List.length dbenv = args -> 
            state_to_stack map nenv dbenv stk -> 
            aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
            a_Dan aD dbenv fenv_d nenv n) ->
      (forall bD bS,
          bS = compile_bexp bD
                            (fun x => one_index_opt x map)
                            (List.length map) -> 
          forall nenv dbenv stk bl rho, 
            List.length dbenv = args -> 
            state_to_stack map nenv dbenv stk -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl) ->
            b_Dan bD dbenv fenv_d nenv bl) ->
      forall nenv dbenv,
        List.length dbenv = args ->
        forall stk,
          state_to_stack map nenv dbenv stk -> 
          forall rho, 
            eval_prop_rel (fun b v => bexp_stack_sem b fenv_s (stk ++ rho) (stk ++ rho, v)) sl ->
            eval_prop_rel (fun b v => b_Dan b dbenv fenv_d nenv v) dl.
Proof.
  induction dl; intros; invs H.
  - econstructor.
  - invs H5.
  - invs H5. econstructor. eapply H2; try eapply eq_refl; try eassumption. assumption.
  - invs H5. econstructor; [ | | eassumption ]; eapply H2; try eapply eq_refl; try eassumption.
  - invs H5. econstructor; [eapply IHdl1 | eapply IHdl2]; try eassumption; try reflexivity.
  - invs H5.
    + econstructor; eapply IHdl1; try eassumption; try reflexivity.
    + eapply RelOrPropRight; eapply IHdl2; try eassumption; try reflexivity.
  - invs H5; econstructor; [ | | | eassumption ]; eapply H2; try eapply eq_refl; try eassumption.
  - invs H5. assert (compile_bool_args (Datatypes.length dbenv) map a_list blist) by (econstructor; eassumption). econstructor. eapply compile_bool_args_sound_pos_backwards; try eassumption. reflexivity. reflexivity. assumption.
Qed.

Lemma compile_arith_sound_backwards :
  forall dl sl args map,
    compile_prop_rel (comp_arith map) dl sl ->
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      (forall aD aS,
          aS = compile_aexp aD
                            (fun x => one_index_opt x map)
                            (List.length map) -> 
          forall nenv dbenv stk n rho, 
            List.length dbenv = args -> 
            state_to_stack map nenv dbenv stk -> 
            aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
            a_Dan aD dbenv fenv_d nenv n) ->
      (forall bD bS,
          bS = compile_bexp bD
                            (fun x => one_index_opt x map)
                            (List.length map) -> 
          forall nenv dbenv stk bl rho, 
            List.length dbenv = args -> 
            state_to_stack map nenv dbenv stk -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl) ->
            b_Dan bD dbenv fenv_d nenv bl) ->
      forall nenv dbenv,
        List.length dbenv = args ->
        forall stk,
          state_to_stack map nenv dbenv stk -> 
          forall rho, 
            eval_prop_rel (fun b v => aexp_stack_sem b fenv_s (stk ++ rho) (stk ++ rho, v)) sl ->
            eval_prop_rel (fun b v => a_Dan b dbenv fenv_d nenv v) dl.
Proof.
  induction dl; intros; invs H; invs H5.
  - econstructor.
  - econstructor; [ | eassumption ].
    eapply H1; try eassumption; try reflexivity.
  - econstructor; [ .. | eassumption]; eapply H1; try eassumption; try reflexivity.
  - econstructor; [eapply IHdl1 | eapply IHdl2]; try eassumption; try reflexivity.
  - econstructor; eapply IHdl1; try eassumption; try reflexivity.
  - eapply RelOrPropRight; eapply IHdl2; try eassumption; try reflexivity.
  - econstructor; [ .. | eassumption ]; eapply H1; try eassumption; try reflexivity.
  - assert (compile_arith_args (Datatypes.length dbenv) map a_list blist) by (econstructor; eassumption).
    econstructor; [ | eassumption ].
    eapply (compile_arith_args_sound_pos_backwards); try eassumption; try reflexivity.
Qed.



  

Ltac translation_inversion :=
  match goal with
  | [ H: logic_transrelation ?args ?map ?dan_log (BaseState ?s ?m) |- _ ] =>
      invs H;
      match goal with
      | [ H': lp_transrelation ?args' map ?d m |- _ ] =>
          invs H';
          match goal with
          | [ H'': lp_arith_transrelation args' map ?d0 ?s |- _ ] =>
              invs H''
          | [ H'': lp_bool_transrelation args' map ?d0 ?s |- _ ] =>
              invs H''
          end
      end
  | [ H: logic_transrelation ?args ?map ?dan_log (AbsAnd ?state1 ?state2) |- _ ] =>
      invs H;
      match goal with
      | [ H1: logic_transrelation ?args' map ?d1 state1,
            H2: logic_transrelation ?args' map ?d2 state2 |- _ ] =>
          idtac
      end
  end.

Lemma trans_sound_pos_assume_comp_backwards : 
  forall state dan_log args map, 
    logic_transrelation args map dan_log state -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      (forall aD aS,
          aS = compile_aexp aD
                            (fun x => one_index_opt x map)
                            (List.length map) -> 
          forall nenv dbenv stk n rho, 
            List.length dbenv = args -> 
            state_to_stack map nenv dbenv stk -> 
            aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
            a_Dan aD dbenv fenv_d nenv n) ->
      (forall bD bS,
          bS = compile_bexp bD
                            (fun x => one_index_opt x map)
                            (List.length map) -> 
          forall nenv dbenv stk bl rho, 
            List.length dbenv = args -> 
            state_to_stack map nenv dbenv stk -> 
            bexp_stack_sem bS fenv_s (stk ++ rho) (stk ++ rho, bl) ->
            b_Dan bD dbenv fenv_d nenv bl) ->
      forall nenv dbenv,
        List.length dbenv = args ->
        forall stk,
          state_to_stack map nenv dbenv stk -> 
          forall rho, 
            absstate_match_rel state fenv_s (stk ++ rho) ->
            AbsEnv_rel dan_log fenv_d dbenv nenv.
Proof.
  induction state; intros; invs H0.
  - translation_inversion; match_inversion; econstructor; econstructor; try (eapply compile_arith_sound_backwards || eapply compile_bool_sound_backwards; try eassumption; try reflexivity).
  - translation_inversion; invs H5. econstructor; [eapply IHstate1 | eapply IHstate2]; try eassumption; try reflexivity.
  - invs H; invs H5.
    + econstructor. eapply IHstate1; try eassumption; try reflexivity.
    + eapply AbsEnv_or_right. eapply IHstate2; try eassumption; try reflexivity.
Qed.
