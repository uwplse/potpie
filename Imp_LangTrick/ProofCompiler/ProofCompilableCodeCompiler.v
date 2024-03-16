From Coq Require Import String List Program.Equality.

From Imp_LangTrick Require Import Base Imp_LangTrickLanguage Imp_LangLogProp StackLanguage StackLogicGrammar LogicProp EnvToStack Imp_LangLogSubst StackLogicBase LogicTranslationCompilerAgnostic ImpVarMap FunctionWellFormed ParamsWellFormed StackLogic Imp_LangLogHoare StackUpdateAdequacy Imp_LangDec Imp_LangLogPropDec UIPList.

From Imp_LangTrick Require Import TranslationPure.

Require Import Coq.Init.Logic.

Import EqNotations.





Module Type CodeCompilerType.
  Parameter compile_aexp : aexp_Imp_Lang -> list ident -> nat -> aexp_stack.
  Parameter compile_bexp : bexp_Imp_Lang -> list ident -> nat -> bexp_stack.
  Parameter compile_imp : imp_Imp_Lang -> list ident -> nat -> imp_stack.
  Definition idents_to_map : list ident -> ident -> nat :=
    ident_list_to_map.
End CodeCompilerType.

Module Type CodeCheckerType.
  Parameter check_aexp : aexp_Imp_Lang -> bool.
  Parameter check_bexp : bexp_Imp_Lang -> bool.
  Parameter check_imp : imp_Imp_Lang -> bool.
End CodeCheckerType.

Module Type CheckableCodeCompilerType <: CodeCompilerType.
  Include CodeCompilerType.
  Include CodeCheckerType.
End CheckableCodeCompilerType.

Module BasicCodeChecker <: CodeCheckerType.
  Definition check_aexp (_: aexp_Imp_Lang) := true.
  Definition check_bexp (_: bexp_Imp_Lang) := true.
  Definition check_imp (_: imp_Imp_Lang) := true.
End BasicCodeChecker.

Module CreateBasicCheckableCodeCompiler(CCType: CodeCompilerType) <: CheckableCodeCompilerType.
  Include CCType.
  Include BasicCodeChecker.
End CreateBasicCheckableCodeCompiler.

Print CheckableCodeCompilerType.

Module Type SpecificationCompilerType.
  Declare Module CC: CodeCompilerType.
  Parameter comp_logic : nat -> (list ident) -> AbsEnv -> AbsState.
  Parameter comp_lp : nat -> (list ident) -> Imp_Lang_lp -> MetavarPred.

  Inductive transrelation_sound : AbsEnv -> fun_env -> fun_env_stk -> list ident -> nat -> Type := 
  |iff_transrelation_sound :
    forall P fenv fenv' idents n, 
      (forall dbenv nenv stk,
          List.length dbenv >= n ->
          LogicTranslationBase.state_to_stack idents nenv dbenv stk ->
          (AbsEnv_rel P fenv dbenv nenv <-> absstate_match_rel (comp_logic n idents P) fenv' stk)) ->
      transrelation_sound P fenv fenv' idents n. 

  
  (* Inductive logic_transrelation : nat -> list ident -> AbsEnv -> AbsState -> Prop := *)
  (* | logic_transrelation_specs_equal : *)
  (*   forall n idents absenv absstate, *)
  (*     comp_logic n idents absenv = absstate -> *)
  (*     logic_transrelation n idents absenv absstate. *)
End SpecificationCompilerType.

Module Type SpecificationCheckerType.
  Parameter check_logic : AbsEnv -> bool.
  Parameter check_lp : Imp_Lang_lp -> bool.
End SpecificationCheckerType.

Module Type CheckableSpecificationCompilerType.
  Include CheckableCodeCompilerType.
  Include SpecificationCompilerType.
  (* Parameter comp_logic : nat -> (list ident) -> AbsEnv -> AbsState. *)
  (* Parameter comp_lp : nat -> (list ident) -> Imp_Lang_lp -> MetavarPred. *)
  Include SpecificationCheckerType.
  (* Parameter check_logic: AbsEnv -> bool. *)
  (* Parameter check_lp : Imp_Lang_lp -> bool. *)
End CheckableSpecificationCompilerType.

Print CheckableSpecificationCompilerType.

Module BasicSpecificationChecker <: SpecificationCheckerType.
  Definition check_lp (_: Imp_Lang_lp) := true.

  Definition check_logic (_: AbsEnv) := true.
End BasicSpecificationChecker.


Module ImpToStackLogicCompilerListIdentOnly(CCType: CodeCompilerType) <: SpecificationCompilerType.
  Module CC := CCType.

  Definition comp_lp (args: nat) (idents: list ident) (lp: Imp_Lang_lp) :=
    match lp with
    | Imp_Lang_lp_arith l => MetaNat (compile_prop l (fun aexp => CC.compile_aexp aexp idents args))
    | Imp_Lang_lp_bool l => MetaBool (compile_prop l (fun bexp => CC.compile_bexp bexp idents args))
    end.

  Fixpoint comp_logic (args: nat) (idents: list ident) (ae: AbsEnv) :=
    match ae with
    | AbsEnvLP lp => BaseState (AbsStkSize (args + Datatypes.length idents))
                              (comp_lp args idents lp)
    | AbsEnvAnd a1 a2 => AbsAnd (comp_logic args idents a1)
                               (comp_logic args idents a2)
    | AbsEnvOr a1 a2 => AbsOr (comp_logic args idents a1)
                             (comp_logic args idents a2)
    end.

  Inductive transrelation_sound : AbsEnv -> fun_env -> fun_env_stk -> list ident -> nat -> Type := 
  |iff_transrelation_sound :
    forall P fenv fenv' idents n, 
      (forall dbenv nenv stk,
          List.length dbenv >= n ->
          LogicTranslationBase.state_to_stack idents nenv dbenv stk ->
          (AbsEnv_rel P fenv dbenv nenv <-> absstate_match_rel (comp_logic n idents P) fenv' stk)) ->
      transrelation_sound P fenv fenv' idents n. 
End ImpToStackLogicCompilerListIdentOnly.


Module CreateStandardCheckableLogicCompiler(CCType: CheckableCodeCompilerType) (SCType: SpecificationCheckerType) <: CheckableSpecificationCompilerType.
  Include CCType.
  Include SCType.
  Include ImpToStackLogicCompilerListIdentOnly(CCType).
  (* Include BasicSpecificationChecker. *)
End CreateStandardCheckableLogicCompiler.


(* Oh, I just had an idea -- maybe instead of having it return options, i'll just preface everything with a "compiles okay" relation, and then the proof compiler will just assume "compiles okay," and if i try to compile anything that isn't okay, then it just goes kaput. (is that how you spell that?) *)

(* Definition compiled_aexps_are_pure := *)
(*     forall a args idents fenv fenv' funcs, *)
(*       CC.check_aexp a = true -> *)
(*       fenv_well_formed' funcs fenv -> *)
(*       fun_app_well_formed fenv funcs a -> *)
(*       all_params_ok_aexp args a -> (* ...might not need this one *) *)
(*       var_map_wf_wrt_aexp idents a -> *)
(*       funcs_okay_too funcs fenv' -> *)
(*       StackPurestBase.aexp_stack_pure_rel (CC.compile_aexp a idents args) fenv'. *)

Module ProofChecker(CC: CheckableCodeCompilerType) (SC: CheckableSpecificationCompilerType).
  Inductive check_proof (fenv: fun_env) (func_list: list fun_Imp_Lang) (d d': AbsEnv) (i: imp_Imp_Lang) (facts: implication_env) (idents: list ident) (args: nat): (hl_Imp_Lang d i d' facts fenv) -> Prop :=
  | CheckHLSkip :
    forall (hl: hl_Imp_Lang d i d' facts fenv),
    forall (Hi : SKIP_Imp_Lang = i),
    forall (Heq: d = d'),
      hl =
        rew [fun H : AbsEnv => hl_Imp_Lang d i H facts fenv] Heq in
      rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H d facts fenv] Hi in
        hl_Imp_Lang_skip d facts fenv ->
      SC.check_logic d = true ->
      CC.check_imp i = true ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLAssign :
     forall x a,
     forall (hl: hl_Imp_Lang d i d' facts fenv)
       (Hi : ASSIGN_Imp_Lang x a = i)
       (Heq : Imp_LangLogSubst.subst_AbsEnv x a d' = d),
       hl =
         rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Hi in
       rew [fun H: AbsEnv => hl_Imp_Lang H (ASSIGN_Imp_Lang x a) d' facts fenv] Heq in
         hl_Imp_Lang_assign d' facts fenv x a ->
         CC.check_aexp a = true ->
         StackExprWellFormed.aexp_well_formed (CC.compile_aexp a idents args) ->
         StackExprWellFormed.absstate_well_formed (SC.comp_logic args idents d') ->
         stack_large_enough_for_state (CC.idents_to_map idents x) (SC.comp_logic args idents d') ->
         CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
         SC.check_logic d = true ->
         SC.check_logic d' = true ->
         (forall fenv',
             fenv_well_formed' func_list fenv ->
             fun_app_well_formed fenv func_list a ->
             all_params_ok_aexp args a -> (* ...might not need this one *)
             var_map_wf_wrt_aexp idents a ->
             funcs_okay_too func_list fenv' ->
             StackPurestBase.aexp_stack_pure_rel (CC.compile_aexp a idents args) fenv') ->
         (forall s' k,
             SC.comp_logic args idents d' = s' ->
             var_map_wf_wrt_aexp idents a ->
             In x idents ->
             k = CC.idents_to_map idents x ->
             (* state_update k a_stk s' = s -> *)
             SC.comp_logic args idents (Imp_LangLogSubst.subst_AbsEnv x a d') = state_update k (CC.compile_aexp a idents args) s') ->
         check_proof fenv func_list d d' i facts idents args hl
  | CheckHLSeq :
    forall d0 i1 i2,
    forall (hl: hl_Imp_Lang d i d' facts fenv)
      (hl1: hl_Imp_Lang d i1 d0 facts fenv)
      (hl2: hl_Imp_Lang d0 i2 d' facts fenv),
    forall (Hi: SEQ_Imp_Lang i1 i2 = i),
      hl = rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Hi in
        hl_Imp_Lang_seq d d' d0 facts fenv i1 i2 hl1 hl2 ->
      CC.check_imp i = true ->
      CC.check_imp i1 = true ->
      CC.check_imp i2 = true ->
      SC.check_logic d0 = true ->
      check_proof fenv func_list d d0 i1 facts idents args hl1 ->
      check_proof fenv func_list d0 d' i2 facts idents args hl2 ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLIf :
    forall b i1 i2,
    forall (hl1: hl_Imp_Lang (atrueImp_Lang b d) i1 d' facts fenv)
      (hl2: hl_Imp_Lang (afalseImp_Lang b d) i2 d' facts fenv)
      (Hi: IF_Imp_Lang b i1 i2 = i)
      (hl: hl_Imp_Lang d i d' facts fenv),
      hl =
         rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Hi in
        hl_Imp_Lang_if d d' b i1 i2 facts fenv hl1 hl2 ->
      CC.check_bexp b = true ->
      CC.check_imp i1 = true ->
      CC.check_imp i = true ->
      CC.check_imp i2 = true ->
      (forall fenv',
          fenv_well_formed' func_list fenv ->
          fun_app_bexp_well_formed fenv func_list b ->
          var_map_wf_wrt_bexp idents b ->
          funcs_okay_too func_list fenv' ->
          StackPurestBase.bexp_stack_pure_rel (CC.compile_bexp b idents args) fenv') ->
      SC.check_logic (atrueImp_Lang b d) = true ->
      SC.check_logic (afalseImp_Lang b d) = true ->
      check_proof fenv func_list (atrueImp_Lang b d) d' i1 facts idents args hl1 ->
      check_proof fenv func_list (afalseImp_Lang b d) d' i2 facts idents args hl2 ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLWhile :
    forall b i__body,
    forall (hl__body: hl_Imp_Lang (atrueImp_Lang b d) i__body d facts fenv)
      (hl: hl_Imp_Lang d i d' facts fenv)
      (HeqP: afalseImp_Lang b d = d')
      (Hi: WHILE_Imp_Lang b i__body = i),
      hl =
        rew [fun H: AbsEnv => hl_Imp_Lang d i H facts fenv]
            HeqP in
      rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H (afalseImp_Lang b d) facts fenv]
          Hi in
        hl_Imp_Lang_while d b i__body facts fenv hl__body ->
      CC.check_bexp b = true ->
      CC.check_imp i = true ->
      CC.check_imp i__body = true ->
      (forall fenv',
          fenv_well_formed' func_list fenv ->
          fun_app_bexp_well_formed fenv func_list b ->
          var_map_wf_wrt_bexp idents b ->
          funcs_okay_too func_list fenv' ->
          StackPurestBase.bexp_stack_pure_rel (CC.compile_bexp b idents args) fenv') ->
      SC.check_logic (atrueImp_Lang b d) = true ->
      SC.check_logic (afalseImp_Lang b d) = true ->
      check_proof fenv func_list (atrueImp_Lang b d) d i__body facts idents args hl__body ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLPre :
    forall P n,
    forall (hl: hl_Imp_Lang d i d' facts fenv)
      (hlP: hl_Imp_Lang P i d' facts fenv)
      (aimp: aimpImp_Lang d P fenv)
      (nth: nth_error facts n = Some (d, P)),
      hl = (hl_Imp_Lang_consequence_pre P d' d i n facts fenv hlP nth aimp) ->
      CC.check_imp i = true ->
      SC.check_logic P = true ->
      SC.check_logic d = true ->
      SC.check_logic d' = true ->
      check_proof fenv func_list P d' i facts idents args hlP ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLPost :
    forall Q n,
    forall (hl: hl_Imp_Lang d i d' facts fenv)
      (hlQ: hl_Imp_Lang d i Q facts fenv)
      (nth: nth_error facts n = Some (Q, d'))
      (aimp: aimpImp_Lang Q d' fenv),
      hl = (hl_Imp_Lang_consequence_post d Q d' i n facts fenv hlQ nth aimp) ->
      CC.check_imp i = true ->
      SC.check_logic Q = true ->
      SC.check_logic d = true ->
      SC.check_logic d' = true ->
      check_proof fenv func_list d Q i facts idents args hlQ ->
      check_proof fenv func_list d d' i facts idents args hl.

  Ltac check_proof_assign_setup :=
    match goal with
    | [ |- check_proof ?fenvMaxIn ?funcs ?ae ?xyz (ASSIGN_Imp_Lang ?x ?a) ?maxFactEnv ?comp_map ?nargs (hl_Imp_Lang_assign _ _ _ ?x ?a) ] =>
        let Hi := fresh "Hi" in
        let Heq := fresh "Heq" in
        assert (Hi: ASSIGN_Imp_Lang x a = ASSIGN_Imp_Lang x a) by reflexivity;
        assert (Heq: ae = ae) by reflexivity;
        let Himp_uip := fresh "Himp_uip" in
        let Habsenv_uip := fresh "Habsenv_uip" in
        pose proof (Himp_uip := UIP_imp_refl _ Hi);
        pose proof (Habsenv_uip := UIP_AbsEnv_refl _ Heq);
        eapply CheckHLAssign with (Hi := Hi) (Heq := Heq); try rewrite Himp_uip; try rewrite Habsenv_uip; try simpl; try reflexivity
    end.

  Ltac check_seq :=
      match goal with
      | [ |- check_proof _ _ _ _ (SEQ_Imp_Lang ?a ?b) _ _ _ _ ] =>
          let Hseq := fresh "Hseq" in
          assert (Hseq : SEQ_Imp_Lang a b = SEQ_Imp_Lang a b) by reflexivity;
          eapply CheckHLSeq with (Hi := Hseq);
          [ rewrite (UIP_imp_refl _ Hseq); simpl; reflexivity | try clear Hseq .. ]
      end.

  Ltac check_proof_while :=
    match goal with
    | [ |- check_proof _ _ ?d ?d' (WHILE_Imp_Lang ?b ?body) _ _ _ (hl_Imp_Lang_while ?d ?b ?body _ _ ?triple) ] =>
        let HeqP := fresh "HeqP" in
        assert (HeqP : afalseImp_Lang b d = d') by reflexivity || enough (HeqP : afalseImp_Lang b d = d');
        (* let Hi := fresh "Hi" in *)
        (* assert (Hi : WHILE_Imp_Lang b body = WHILE_Imp_Lang b body) by reflexivity; *)
        let Hi := fresh "Hi" in
        let Himp_uip := fresh "Himp_uip" in
        let Habsenv_uip := fresh "Habsenv_uip" in
        assert (Hi : WHILE_Imp_Lang b body = WHILE_Imp_Lang b body) by reflexivity;
        pose proof (Himp_uip := UIP_imp_refl _ Hi);
        pose proof (Habsenv_uip := UIP_AbsEnv_refl _ HeqP);
        eapply CheckHLWhile with (hl__body := triple) (HeqP := HeqP) (Hi := Hi); [ rewrite Himp_uip; rewrite Habsenv_uip; simpl; try reflexivity | clear Himp_uip Habsenv_uip; clear Hi HeqP .. ]
    end.
  Ltac check_hl_pre :=
    match goal with
    | [ |- check_proof ?fenv ?funcs ?P ?Q ?i ?facts ?idents ?args (hl_Imp_Lang_consequence_pre ?P' ?d ?d' ?i' ?n ?facts' ?fenv' ?HT ?nth' ?AIMP) ] =>
        let HFacts := fresh "HFacts" in
        let my_some := fresh "MySome" in
        let Hmy_some := fresh "Hmy_some" in
        remember (let true_prop := (AbsEnvLP (Imp_Lang_lp_arith (TrueProp _ _))) in
                  Some (fst (nth n facts (true_prop, true_prop)), snd (nth n facts (true_prop, true_prop)))) as my_some eqn:Hmy_some;
        simpl in Hmy_some; 
        assert (HFacts :
                 let true_prop := (AbsEnvLP (Imp_Lang_lp_arith (TrueProp _ _))) in
                 nth_error facts n = my_some) by (subst my_some; reflexivity);
        subst my_some;
        pose proof (UIP_option_refl := UIP_option_pair_refl);
        specialize (UIP_option_refl _ Imp_LangLogPropDec.UIP_AbsEnv);
        specialize (UIP_option_refl _ HFacts);
        eapply CheckHLPre with (aimp := AIMP) (hlP := HT) (nth := HFacts); [ rewrite UIP_option_refl; try reflexivity | clear UIP_option_refl; clear HFacts .. ]
    end.
  Ltac check_hl_post :=
    match goal with
    | [ |- check_proof ?fenv ?funcs ?P ?Q ?i ?facts ?idents ?args (hl_Imp_Lang_consequence_post ?d ?P' ?d' ?i' ?n ?facts' ?fenv' ?HT ?nth' ?AIMP) ] =>
        let HFacts := fresh "HFacts" in
        let my_some := fresh "MySome" in
        let Hmy_some := fresh "Hmy_some" in
        remember (let true_prop := (AbsEnvLP (Imp_Lang_lp_arith (TrueProp _ _))) in
                  Some (fst (nth n facts (true_prop, true_prop)), snd (nth n facts (true_prop, true_prop)))) as my_some eqn:Hmy_some;
        simpl in Hmy_some; 
        assert (HFacts :
                 let true_prop := (AbsEnvLP (Imp_Lang_lp_arith (TrueProp _ _))) in
                 nth_error facts n = my_some) by (subst my_some; reflexivity);
        subst my_some;
        pose proof (UIP_option_refl := UIP_option_pair_refl);
        specialize (UIP_option_refl _ Imp_LangLogPropDec.UIP_AbsEnv);
        specialize (UIP_option_refl _ HFacts);
        eapply CheckHLPost with (aimp := AIMP) (hlQ := HT) (nth := HFacts); [ rewrite UIP_option_refl; try reflexivity | clear UIP_option_refl; clear HFacts .. ]
    end.

  Ltac check_if :=
          match goal with
          | [ |- check_proof _ _ _ _ (IF_Imp_Lang ?b ?i1 ?i2) _ _ _ (hl_Imp_Lang_if ?P ?Q ?b' ?i1' ?i2' ?fact_env ?fenv ?HLtrue ?HLfalse) ] =>
              let Hi := fresh "Hi" in
              
              assert (Hi : IF_Imp_Lang b i1 i2 = IF_Imp_Lang b' i1' i2') by reflexivity;
              let Himp_uip := fresh "Himp_uip" in
              pose proof (Himp_uip := UIP_imp_refl _ Hi);
              eapply CheckHLIf with (Hi := Hi); try rewrite Himp_uip; try simpl; try reflexivity; try (clear Himp_uip; clear Hi)
          end.
  Ltac check_proof_helper :=
    match goal with
    | [ |- check_proof
            _ _ _ _ (SEQ_Imp_Lang _ _) _ _ _
            (hl_Imp_Lang_seq _ _ _ _ _ _ _ _ _ ) ] =>
        check_seq;
        try reflexivity;
        try check_proof_helper
    | [ |- check_proof
            _ _ _ _ (ASSIGN_Imp_Lang _ _) _ _ _
            (hl_Imp_Lang_assign _ _ _ _ _) ] =>
        check_proof_assign_setup;
        try reflexivity;
        try check_proof_helper
    | [ |- check_proof
            _ _ _ _ (IF_Imp_Lang _ _ _ ) _ _ _
            (hl_Imp_Lang_if _ _ _ _ _ _ _ _ _) ] =>
        check_if;
        try reflexivity;
        try check_proof_helper
    | [ |- check_proof
            _ _ _ _ (WHILE_Imp_Lang _ _) _ _ _
            (hl_Imp_Lang_while _ _ _ _ _ _) ] =>
        check_proof_while;
        try reflexivity;
        try check_proof_helper
    | [ |- check_proof
            _ _ _ _ ?i _ _ _
            (hl_Imp_Lang_consequence_pre _ _ _ _ _ _ _ _ _ _) ] =>
        check_hl_pre;
        try reflexivity;
        try check_proof_helper
    | [ |- check_proof
            _ _ _ _ ?i _ _ _
            (hl_Imp_Lang_consequence_post _ _ _ _ _ _ _ _ _ _) ] =>
        check_hl_post;
        try reflexivity;
        try check_proof_helper
    | [ |- StackUpdateAdequacy.stack_large_enough_for_state ?n _ ] =>
        repeat econstructor
    | [ |- forall fenv',
          fenv_well_formed'
            ?funcs ?fenv ->
          fun_app_well_formed ?fenv
                              ?funcs
                              ?aexp ->
          all_params_ok_aexp ?args ?aexp ->
          var_map_wf_wrt_aexp ?idents ?aexp ->
          funcs_okay_too
            ?funcs
            fenv' ->
          StackPurestBase.aexp_stack_pure_rel
            (CC.compile_aexp ?aexp ?idents ?args)
            fenv' ] =>
        intros fenv' FENV_WF FUN_APP ALL_PARAMS WF OK;
        match aexp with
        | APP_Imp_Lang ?f ?args =>
            econstructor; try reflexivity
        | _ =>
            repeat econstructor (* this isn't exactly right -- should stop if it finds function application *)
        end
    | [ |- forall fenv',
          fenv_well_formed'
            ?funcs ?fenv ->
          fun_app_bexp_well_formed ?fenv ?funcs ?bexp ->
          var_map_wf_wrt_bexp ?idents ?bexp ->
          funcs_okay_too
            ?funcs fenv' ->
          StackPurestBase.bexp_stack_pure_rel
            (CC.compile_bexp ?bexp ?idents ?args) fenv' ] =>
        intros fenv' FENV_WF FUN_APP WF OK;
        repeat econstructor
    | [ |- forall (s' : StackLogicGrammar.AbsState) (k : nat),
          _ = s' ->
          var_map_wf_wrt_aexp ?idents ?aexp ->
          _ ->
          k = ?num ->
          _ =
            StackLogicBase.state_update
              k
              (CC.compile_aexp ?aexp ?idents ?args)
              s' ] =>
        let fs' := fresh "s'" in
        let fk := fresh "k" in
        let Hs' := fresh "Hs'" in
        let WF := fresh "WF" in
        let Hk := fresh "Hk" in
        intros fs' fk Hs' WF _ Hk;
        rewrite <- Hs', Hk; try reflexivity
    | [ |- StackExprWellFormed.aexp_well_formed
            (CC.compile_aexp ?aexp ?idents ?args) ] =>
        match aexp with
        | APP_Imp_Lang ?f ?args =>
            econstructor; try reflexivity
        | _ => repeat econstructor
        end
    | [ |- StackExprWellFormed.absstate_well_formed _ ] =>
        repeat econstructor
    end.
End ProofChecker.

Module ValidImplicationTranslation(SC: CheckableSpecificationCompilerType).
  Definition valid_imp_trans_def facts facts' (fenv : fun_env) fenv0 map args :=
    Datatypes.length facts <= Datatypes.length facts' /\
      (forall (n : nat) (P Q : AbsEnv) (P' Q' : AbsState),
          SC.check_logic P = true ->
          SC.check_logic Q = true ->
          SC.comp_logic args map P = P' ->
          SC.comp_logic args map Q = Q' ->
          nth_error facts n = Some (P, Q) ->
          nth_error facts' n = Some (P', Q') 
          (* /\
            (forall (nenv : nat_env) (dbenv stk : list nat),
                LogicTranslationBase.state_to_stack map nenv dbenv stk ->
                AbsEnv_rel P fenv dbenv nenv <->
                  absstate_match_rel P' fenv0 stk) /\
            (forall (nenv : nat_env) (dbenv stk : list nat),
                LogicTranslationBase.state_to_stack map nenv dbenv stk ->
                AbsEnv_rel Q fenv dbenv nenv <->
                  absstate_match_rel Q' fenv0 stk)) 
        aimpstk P' Q' fenv0 *)
      )
                  /\
      StackLogic.fact_env_valid facts' fenv0.
End ValidImplicationTranslation.


Module Unfolder(CC: CheckableCodeCompilerType) (SC: CheckableSpecificationCompilerType).
  Ltac unfold_cc_sc :=
    unfold CC.compile_aexp, CC.compile_bexp, CC.compile_imp, CC.check_aexp, CC.check_bexp, CC.check_imp, SC.comp_lp, SC.comp_logic, SC.check_lp, SC.check_logic.
End Unfolder.

Module ProofCompilableSetDefinitions(CC: CheckableCodeCompilerType) (SC :CheckableSpecificationCompilerType).
  Include ProofChecker CC SC.
  Include ValidImplicationTranslation SC.
  Include Unfolder CC SC.
End ProofCompilableSetDefinitions.
  

Module Type ProofCompilableType.
  Declare Module CC: CheckableCodeCompilerType.
  Declare Module SC: CheckableSpecificationCompilerType.

  Include ProofCompilableSetDefinitions(CC) (SC).
        

  Parameter spec_conjunction_commutes: forall (args: nat) (idents: list ident) (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
      SC.check_logic (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ val_to_prop b)))) = true ->
      SC.check_logic P = true ->
      CC.check_bexp b = true ->
      SC.comp_logic
        args
        idents
        (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ val_to_prop b))))
      =
        AbsAnd (SC.comp_logic args idents P)
               (BaseState
                  (AbsStkSize (args + Datatypes.length idents))
                  (MetaBool (UnaryProp _ _ val_to_prop (CC.compile_bexp b idents args)))).

  Parameter spec_lp_conjunction_check:
    forall (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
      SC.check_logic P = true ->
      CC.check_bexp b = true ->
      SC.check_logic
        (AbsEnvAnd P
                   (AbsEnvLP
                      (Imp_Lang_lp_bool
                         (UnaryProp bool bexp_Imp_Lang
                                    val_to_prop b)))) = true.
  
  Parameter skip_compilation_okay: forall (args: nat) (idents: list ident),
      CC.check_imp SKIP_Imp_Lang = true ->
      CC.compile_imp SKIP_Imp_Lang idents args = Skip_Stk.
  Parameter assign_compilation_commutes: forall (args: nat) (idents: list ident) (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.compile_imp (ASSIGN_Imp_Lang x a) idents args = Assign_Stk (CC.idents_to_map idents x) (CC.compile_aexp a idents args).

  Parameter assign_check_implies_assignee_check :
    forall (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.check_aexp a = true.

  Parameter sequence_compilation_commutes: forall (args: nat) (idents: list ident) (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.compile_imp (SEQ_Imp_Lang i1 i2) idents args = Seq_Stk (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).

  Parameter sequence_check_implies_all_check :
    forall (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  
  
  Parameter if_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      (* CC.check_bexp b = true -> *)
      (* CC.check_imp i1 = true -> *)
      (* CC.check_imp i2 = true -> *)
      CC.compile_imp (IF_Imp_Lang b i1 i2) idents args
      =
        If_Stk (CC.compile_bexp b idents args) (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Parameter if_check_implies_condition_then_else_check:
    forall (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      CC.check_bexp b = true /\ CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  
  Parameter while_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      (* CC.check_bexp b = true -> *)
      (* CC.check_imp i = true -> *)
      CC.compile_imp (WHILE_Imp_Lang b i) idents args
      =
        While_Stk (CC.compile_bexp b idents args) (CC.compile_imp i idents args).
  Parameter while_check_implies_condition_loop_check :
    forall (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      CC.check_bexp b = true /\ CC.check_imp i = true.

  Parameter size_change_implication_okay : forall (s1 ARG : AbsState) (b : bexp_Imp_Lang)
         (idents : list ident) (n_args : nat) 
         (fenv : fun_env) (d : AbsEnv) (my_fun : bool -> Prop)
         (fenv' : fun_env_stk) (funcs : list fun_Imp_Lang),
       funcs_okay_too funcs fenv' ->
       fenv_well_formed' funcs fenv ->
       SC.comp_logic n_args idents d = s1 ->
       SC.check_logic d = true ->
       CC.check_bexp b = true ->
       ARG =
         AbsAnd s1
                (BaseState AbsStkTrue
                           (MetaBool
                              (UnaryProp bool bexp_stack my_fun
                                         (CC.compile_bexp b idents n_args)))) ->
       (aimpstk ARG
                (AbsAnd s1
                        (BaseState (AbsStkSize (Datatypes.length idents + n_args))
                                   (MetaBool
                                      (UnaryProp bool bexp_stack my_fun
                                                 (CC.compile_bexp b idents n_args)))))) fenv'.

  (* Include ValidImplicationTranslation(SC). *)

  (* Definition valid_imp_trans_def facts facts' fenv fenv0 map args := *)
  (*   Datatypes.length facts <= Datatypes.length facts' /\ *)
  (*     (forall (n : nat) (P Q : AbsEnv) (P' Q' : AbsState), *)
  (*         SC.check_logic P = true -> *)
  (*         SC.check_logic Q = true -> *)
  (*         SC.comp_logic args map P = P' -> *)
  (*         SC.comp_logic args map Q = Q' -> *)
  (*         nth_error facts n = Some (P, Q) -> *)
  (*         nth_error facts' n = Some (P', Q') /\ *)
  (*           (forall (nenv : nat_env) (dbenv stk : list nat), *)
  (*               LogicTranslationBase.state_to_stack map nenv dbenv stk -> *)
  (*               AbsEnv_rel P fenv dbenv nenv <-> *)
  (*                 absstate_match_rel P' fenv0 stk) /\ *)
  (*           (forall (nenv : nat_env) (dbenv stk : list nat), *)
  (*               LogicTranslationBase.state_to_stack map nenv dbenv stk -> *)
  (*               AbsEnv_rel Q fenv dbenv nenv <-> *)
  (*                 absstate_match_rel Q' fenv0 stk)) /\ *)
  (*     StackLogic.fact_env_valid facts' fenv0. *)
End ProofCompilableType.




(* This is in the case where we have a totally correct compiler *)
Module Type EasyProofCompilableType.
  Declare Module CC: CodeCompilerType.
  Declare Module SC: SpecificationCompilerType.

  (* Can you put inductive types in module types???? *)
  Parameter logic_transrelation_substitution :
    forall args ident_list d d0 s s' x a k a_stk mapping,
      SC.comp_logic args ident_list d = s ->
      Imp_LangLogSubst.subst_AbsEnv_rel x a d d0 ->
      In x ident_list ->
      var_map_wf_wrt_aexp ident_list a ->
      AbsEnv_prop_rel (var_map_wf_wrt_aexp ident_list)
                      (var_map_wf_wrt_bexp ident_list)
                      d0 ->
      mapping = ident_list_to_map ident_list ->
      a_stk = CC.compile_aexp a ident_list args ->
      SC.comp_logic args ident_list d0 = s' ->
      k = mapping x ->
      state_update_rel k a_stk s s'.

  Parameter compiled_aexps_are_pure :
    forall a args idents fenv fenv' funcs,
      fenv_well_formed' funcs fenv ->
      fun_app_well_formed fenv funcs a ->
      all_params_ok_aexp args a -> (* ...might not need this one *)
      var_map_wf_wrt_aexp idents a ->
      funcs_okay_too funcs fenv' ->
      StackPurestBase.aexp_stack_pure_rel (CC.compile_aexp a idents args) fenv'.

  Parameter compiled_bexps_are_pure :
    forall b args idents fenv fenv' funcs,
      fenv_well_formed' funcs fenv ->
      fun_app_bexp_well_formed fenv funcs b ->
      (* all_params_ok_bexp args b -> (* ...might not need this one *) *)
      var_map_wf_wrt_bexp idents b ->
      funcs_okay_too funcs fenv' ->
      StackPurestBase.bexp_stack_pure_rel (CC.compile_bexp b idents args) fenv'.

  Parameter spec_conjunction_commutes: forall (args: nat) (idents: list ident) (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
      
      SC.comp_logic
        args
        idents
        (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ val_to_prop b))))
      =
        AbsAnd (SC.comp_logic args idents P)
               (BaseState
                  (AbsStkSize (args + Datatypes.length idents))
                  (MetaBool (UnaryProp _ _ val_to_prop (CC.compile_bexp b idents args)))).

  Parameter skip_compilation_okay: forall (args: nat) (idents: list ident),
      CC.compile_imp SKIP_Imp_Lang idents args = Skip_Stk.
  Parameter assign_compilation_commutes: forall (args: nat) (idents: list ident) (x: ident) (a: aexp_Imp_Lang),
      CC.compile_imp (ASSIGN_Imp_Lang x a) idents args = Assign_Stk (CC.idents_to_map idents x) (CC.compile_aexp a idents args).
  Parameter sequence_compilation_commutes: forall (args: nat) (idents: list ident) (i1 i2: imp_Imp_Lang),
      CC.compile_imp (SEQ_Imp_Lang i1 i2) idents args = Seq_Stk (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Parameter if_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
    CC.compile_imp (IF_Imp_Lang b i1 i2) idents args
            =
              If_Stk (CC.compile_bexp b idents args) (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Parameter while_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
    CC.compile_imp (WHILE_Imp_Lang b i) idents args
            =
              While_Stk (CC.compile_bexp b idents args) (CC.compile_imp i idents args).

  Parameter size_change_implication_okay : forall (s1 ARG : AbsState) (b : bexp_Imp_Lang)
         (idents : list ident) (n_args : nat) 
         (fenv : fun_env) (d : AbsEnv) (my_fun : bool -> Prop)
         (fenv' : fun_env_stk) (funcs : list fun_Imp_Lang),
       funcs_okay_too funcs fenv' ->
       fenv_well_formed' funcs fenv ->
       SC.comp_logic n_args idents d = s1 ->
       ARG =
         AbsAnd s1
                (BaseState AbsStkTrue
                           (MetaBool
                              (UnaryProp bool bexp_stack my_fun
                                         (CC.compile_bexp b idents n_args)))) ->
       (aimpstk ARG
                (AbsAnd s1
                        (BaseState (AbsStkSize (Datatypes.length idents + n_args))
                                   (MetaBool
                                      (UnaryProp bool bexp_stack my_fun
                                                 (CC.compile_bexp b idents n_args)))))) fenv'.

  Definition valid_imp_trans_def facts facts' fenv fenv0 map args :=
      Datatypes.length facts <= Datatypes.length facts' /\
        (forall (n : nat) (P Q : AbsEnv) (P' Q' : AbsState),
            SC.comp_logic args map P = P' ->
            SC.comp_logic args map Q = Q' ->
            nth_error facts n = Some (P, Q) ->
            nth_error facts' n = Some (P', Q') /\
              (forall (nenv : nat_env) (dbenv stk : list nat),
                  LogicTranslationBase.state_to_stack map nenv dbenv stk ->
                  AbsEnv_rel P fenv dbenv nenv <->
                    absstate_match_rel P' fenv0 stk) /\
              (forall (nenv : nat_env) (dbenv stk : list nat),
                  LogicTranslationBase.state_to_stack map nenv dbenv stk ->
                  AbsEnv_rel Q fenv dbenv nenv <->
                    absstate_match_rel Q' fenv0 stk)) /\
        StackLogic.fact_env_valid facts' fenv0.
End EasyProofCompilableType.
  

  

  




(* Module CorrectCompilerProofCompilable <: ProofCompilableType. *)

  
