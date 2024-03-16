From Coq Require Import String Arith Psatz Bool List.

From Imp_LangTrick Require Import Base Imp_LangTrickLanguage Imp_LangLogProp StackLanguage StackLogicGrammar LogicProp EnvToStack Imp_LangLogSubst StackLogicBase LogicTranslationCompilerAgnostic ImpVarMap FunctionWellFormed ParamsWellFormed StackLogic Imp_LangLogHoare.
From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogProp StackLanguage StackLogicGrammar LogicProp EnvToStackBuggy ProofCompilableCodeCompiler Imp_LangLogHoare StackUpdateAdequacy TranslationPure ProofCompCodeCompAgnosticMod.

Module BuggyCodeCompiler <: CheckableCodeCompilerType.
  Definition compile_aexp (exp: aexp_Imp_Lang) (idents: list ident) (num_locals: nat): aexp_stack :=
    EnvToStackBuggy.compile_aexp exp (ident_list_to_map idents) num_locals.

  Definition compile_bexp (exp: bexp_Imp_Lang) (idents: list ident) (num_locals: nat): bexp_stack :=
    EnvToStackBuggy.compile_bexp exp (ident_list_to_map idents) num_locals.

  Definition compile_imp (imp: imp_Imp_Lang) (idents: list ident) (num_locals: nat) :=
    EnvToStackBuggy.compile_imp imp (ident_list_to_map idents) num_locals.

  Definition idents_to_map := ident_list_to_map.

  Definition check_aexp (_: aexp_Imp_Lang) := true.

  Definition check_bexp (_: bexp_Imp_Lang) := true.

  Definition check_imp (_: imp_Imp_Lang) := true.
End BuggyCodeCompiler.


Module BuggySpecCompiler <: CheckableSpecificationCompilerType.
  Include CreateStandardCheckableLogicCompiler(BuggyCodeCompiler) (BasicSpecificationChecker).
  

(* Module BuggySpecCompiler <: CheckableSpecificationCompilerType. *)
(*   Include BuggyCodeCompiler. *)
(*   Module CC := BuggyCodeCompiler. *)

  
  Definition comp_arith args idents :=
    fun (aexp: aexp_Imp_Lang) =>
      CC.compile_aexp aexp
                      idents
                      args.

  Definition comp_bool args idents :=
    fun (bexp: bexp_Imp_Lang) =>
      CC.compile_bexp bexp
                       idents
                       args.
End BuggySpecCompiler.

(*   Definition comp_lp (args: nat) (idents: list ident) (lp: Imp_Lang_lp) := *)
(*     match lp with *)
(*     | Imp_Lang_lp_arith l => MetaNat (compile_prop l (comp_arith args idents)) *)
(*     | Imp_Lang_lp_bool l => MetaBool (compile_prop l (comp_bool args idents)) *)
(*     end. *)

(*   Fixpoint comp_logic (args: nat) (idents: list ident) (ae: AbsEnv) := *)
(*     match ae with *)
(*     | AbsEnvLP lp => BaseState (AbsStkSize (args + List.length idents)) *)
(*                               (comp_lp args idents lp) *)
(*     | AbsEnvAnd l1 l2 => AbsAnd (comp_logic args idents l1) *)
(*                                (comp_logic args idents l2) *)
(*     | AbsEnvOr l1 l2 => AbsOr (comp_logic args idents l1) *)
(*                              (comp_logic args idents l2) *)
(*     end. *)

(*   Definition check_lp (_: Imp_Lang_lp) := true. *)

(*   Definition check_logic (_: AbsEnv) := true. *)
(* End BuggySpecCompiler. *)

Require Import Coq.Init.Logic.

Import EqNotations.

Module BuggyProofCompilable <: ProofCompilableType.
  Module CC := BuggyCodeCompiler.
  Module SC := BuggySpecCompiler.

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

  Lemma spec_conjunction_commutes:
    forall (args: nat) (idents: list ident) (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
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
  Proof.
    induction P; intros.
    - simpl. unfold SC.comp_bool. reflexivity.
    - simpl. unfold SC.comp_bool. reflexivity.
    - simpl. unfold SC.comp_bool. reflexivity.
  Qed.

  Lemma spec_lp_conjunction_check:
    forall (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
      SC.check_logic P = true ->
      CC.check_bexp b = true ->
      SC.check_logic
        (AbsEnvAnd P
                   (AbsEnvLP
                      (Imp_Lang_lp_bool
                         (UnaryProp bool bexp_Imp_Lang
                                    val_to_prop b)))) = true.
  Proof.
    intros.
    unfold SC.check_logic. reflexivity.
  Qed.

  Lemma skip_compilation_okay: forall (args: nat) (idents: list ident),
      CC.check_imp SKIP_Imp_Lang = true ->
      CC.compile_imp SKIP_Imp_Lang idents args = Skip_Stk.
  Proof.
    intros. unfold CC.compile_imp. unfold compile_imp. reflexivity.
  Qed.
    
  Lemma assign_compilation_commutes: forall (args: nat) (idents: list ident) (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.compile_imp (ASSIGN_Imp_Lang x a) idents args = Assign_Stk (CC.idents_to_map idents x) (CC.compile_aexp a idents args).
  Proof.
    intros. unfold CC.compile_imp. unfold compile_imp. unfold CC.compile_aexp. reflexivity.
  Qed.

  Lemma assign_check_implies_assignee_check :
    forall (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.check_aexp a = true.
  Proof.
    intros. unfold CC.check_aexp. reflexivity.
  Qed.

  Lemma sequence_compilation_commutes: forall (args: nat) (idents: list ident) (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.compile_imp (SEQ_Imp_Lang i1 i2) idents args = Seq_Stk (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Proof.
    intros. unfold CC.compile_imp. simpl. reflexivity.
  Qed.

  Lemma sequence_check_implies_all_check :
    forall (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  Proof.
    intros. unfold CC.check_imp. split; reflexivity.
  Qed.
  
  Lemma if_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      (* CC.check_bexp b = true -> *)
      (* CC.check_imp i1 = true -> *)
      (* CC.check_imp i2 = true -> *)
      CC.compile_imp (IF_Imp_Lang b i1 i2) idents args
      =
        If_Stk (CC.compile_bexp b idents args) (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Proof.
    intros. unfold CC.compile_bexp.  unfold CC.compile_imp.  simpl. reflexivity.
  Qed.
  
  Lemma if_check_implies_condition_then_else_check:
    forall (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      CC.check_bexp b = true /\ CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  Proof.
    intros. unfold CC.check_bexp, CC.check_imp. repeat split; reflexivity.
  Qed.
  
  Lemma while_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      (* CC.check_bexp b = true -> *)
      (* CC.check_imp i = true -> *)
      CC.compile_imp (WHILE_Imp_Lang b i) idents args
      =
        While_Stk (CC.compile_bexp b idents args) (CC.compile_imp i idents args).
  Proof.
    intros. unfold CC.compile_imp. unfold CC.compile_bexp. reflexivity.
  Qed.
  Lemma while_check_implies_condition_loop_check :
    forall (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      CC.check_bexp b = true /\ CC.check_imp i = true.
  Proof.
    intros. unfold CC.check_bexp, CC.check_imp. split; reflexivity.
  Qed.

  Lemma size_change_implication_okay : forall (s1 ARG : AbsState) (b : bexp_Imp_Lang)
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
  Proof.
    induction s1; unfold aimpstk; intros; subst.
    - destruct d eqn:Hd.
      + simpl in H1. invc H1. invc H5. econstructor.
        * eassumption.
        * invs H6. econstructor.
          -- rewrite Nat.add_comm. eassumption.
          -- invs H9. eassumption.
      + simpl in H1. invs H1.
      + simpl in H1. invs H1.
    - destruct d eqn:Hd; try solve [simpl in H1; invs H1].
      invc H5. invs H7.
      simpl in H1. invs H1.
      remember (SC.comp_logic n_args idents a1) as s1.
      remember (SC.comp_logic n_args idents a2) as s2.
      remember ((BaseState AbsStkTrue
             (MetaBool
                (UnaryProp bool bexp_stack my_fun
                   (CC.compile_bexp b idents n_args))))) as bm.
      assert (absstate_match_rel (AbsAnd s1 bm) fenv' stk) by (econstructor; eassumption).
      assert (absstate_match_rel (AbsAnd s2 bm) fenv' stk) by (econstructor; eassumption).
      eapply IHs1_1 in H4. eapply IHs1_2 in H5. inversion H5.
      econstructor.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + rewrite Heqs2. reflexivity.
      + eassumption.
      + eassumption.
      + rewrite Heqbm. reflexivity.
      + eassumption.
      + eassumption.
      + rewrite Heqs1. reflexivity.
      + eassumption.
      + eassumption.
      + rewrite Heqbm. reflexivity.
    - invc H5. 
      destruct d eqn:Hd; try solve [invs H1].
      simpl in H1.
      remember ((BaseState AbsStkTrue
             (MetaBool
                (UnaryProp bool bexp_stack my_fun
                   (CC.compile_bexp b idents n_args))))) as bm.
      inversion H1.
      inversion H7.
      subst s1. subst s2. subst fenv0. subst stk0.
      + assert (absstate_match_rel (AbsAnd s1_1 bm) fenv' stk) by (econstructor; eassumption).
        
        eapply IHs1_1 in H4. inversion H4.
        econstructor.
        * eapply RelAbsOrLeft. rewrite H5. eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * rewrite <- H5. reflexivity.
        * eassumption.
        * eassumption.
        * rewrite Heqbm. reflexivity.
      + assert (absstate_match_rel (AbsAnd s1_2 bm) fenv' stk) by (econstructor; eassumption).
        eapply IHs1_2 in H13. inversion H13. econstructor.
        * eapply RelAbsOrRight. rewrite H6. eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * rewrite <- H6. reflexivity.
        * eassumption.
        * eassumption.
        * rewrite Heqbm. reflexivity.
  Qed.

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
                  absstate_match_rel Q' fenv0 stk) *)
                  ) /\
      StackLogic.fact_env_valid facts' fenv0.
End BuggyProofCompilable.

Require Import ProofCompilerCodeCompAgnostic.

Module BuggyProofCompiler := CompilerAgnosticProofCompiler(BuggyProofCompilable).

