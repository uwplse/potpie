From Coq Require Import String Arith Psatz Bool List.

From Imp_LangTrick Require Import Base Imp_LangTrickLanguage Imp_LangLogProp StackLanguage StackLogicGrammar LogicProp EnvToStack Imp_LangLogSubst StackLogicBase LogicTranslationCompilerAgnostic ImpVarMap FunctionWellFormed ParamsWellFormed StackLogic Imp_LangLogHoare.
From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogProp StackLanguage StackLogicGrammar LogicProp ProofCompilableCodeCompiler Imp_LangLogHoare StackUpdateAdequacy TranslationPure ProofCompCodeCompAgnosticMod.

Module UnprovenCorrectCodeCompiler <: CodeCompilerType.
  Definition compile_aexp (exp: aexp_Imp_Lang) (idents: list ident) (num_locals: nat): aexp_stack :=
    compile_aexp exp (ident_list_to_map idents) num_locals.

  Definition compile_bexp (exp: bexp_Imp_Lang) (idents: list ident) (num_locals: nat): bexp_stack :=
    compile_bexp exp (ident_list_to_map idents) num_locals.

  Definition compile_imp (imp: imp_Imp_Lang) (idents: list ident) (num_locals: nat) :=
    compile_imp imp (ident_list_to_map idents) num_locals.

  Definition idents_to_map := ident_list_to_map.
End UnprovenCorrectCodeCompiler.

Module UnprovenCorrectCheckableCodeCompiler := CreateBasicCheckableCodeCompiler(UnprovenCorrectCodeCompiler).

Module UnprovenCorrectSpecCompiler := CreateStandardCheckableLogicCompiler(UnprovenCorrectCheckableCodeCompiler) (BasicSpecificationChecker).

Module Unfolder(CC: CheckableCodeCompilerType) (SC: CheckableSpecificationCompilerType).
  Ltac unfold_cc_sc :=
    unfold CC.compile_aexp, CC.compile_bexp, CC.compile_imp, CC.check_aexp, CC.check_bexp, CC.check_imp, SC.comp_lp, SC.comp_logic, SC.check_lp, SC.check_logic.
End Unfolder.

Module UnprovenCorrectProofCompilable <: ProofCompilableType.
  Module CC := UnprovenCorrectCheckableCodeCompiler.
  Module SC := UnprovenCorrectSpecCompiler.

  Include (ProofChecker CC SC).
  Include ValidImplicationTranslation(SC).
  Include Unfolder(CC) (SC).

  Lemma spec_conjunction_commutes: forall (args: nat) (idents: list ident) (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
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
    destruct P; intros; simpl; reflexivity.
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
    intros. reflexivity.
  Qed.
  
  Lemma skip_compilation_okay: forall (args: nat) (idents: list ident),
      CC.check_imp SKIP_Imp_Lang = true ->
      CC.compile_imp SKIP_Imp_Lang idents args = Skip_Stk.
  Proof.
    intros. reflexivity.
  Qed.
  
  Lemma assign_compilation_commutes: forall (args: nat) (idents: list ident) (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.compile_imp (ASSIGN_Imp_Lang x a) idents args = Assign_Stk (CC.idents_to_map idents x) (CC.compile_aexp a idents args).
  Proof.
    intros. reflexivity.
  Defined.

  Lemma assign_check_implies_assignee_check :
    forall (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.check_aexp a = true.
  Proof.
    reflexivity.
  Qed.

  Lemma sequence_compilation_commutes: forall (args: nat) (idents: list ident) (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.compile_imp (SEQ_Imp_Lang i1 i2) idents args = Seq_Stk (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Proof.
    reflexivity.
  Qed.

  Lemma sequence_check_implies_all_check :
    forall (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  Proof.
    split; reflexivity.
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
    reflexivity.
  Qed.
  Lemma if_check_implies_condition_then_else_check:
    forall (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      CC.check_bexp b = true /\ CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  Proof.
    split; [ | split ]; reflexivity.
  Qed.
  
  Lemma while_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      (* CC.check_bexp b = true -> *)
      (* CC.check_imp i = true -> *)
      CC.compile_imp (WHILE_Imp_Lang b i) idents args
      =
        While_Stk (CC.compile_bexp b idents args) (CC.compile_imp i idents args).
  Proof.
    reflexivity.
  Qed.
  Lemma while_check_implies_condition_loop_check :
    forall (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      CC.check_bexp b = true /\ CC.check_imp i = true.
  Proof.
    split; reflexivity.
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
    intros.
    unfold CC.compile_bexp.
    rewrite H4. clear H4. unfold aimpstk. intros.
    revert H1.
    invc H4. invc H9. revert H10 H5 H6. revert stk. revert s1.
    induction d; intros.
    - econstructor.
      + eassumption.
      + simpl in H1. rewrite <- H1 in *. invc H6. econstructor.
        * rewrite Nat.add_comm. eassumption.
        * eassumption.
    - simpl in H1. rewrite <- H1 in *. invc H6.
      remember (SC.comp_logic n_args idents d1) as s1.
      remember (SC.comp_logic n_args idents d2) as s2.
      specialize (IHd1 eq_refl). specialize (IHd2 eq_refl).
      remember ((BaseState (AbsStkSize (Datatypes.length idents + n_args))
          (MetaBool
             (UnaryProp bool bexp_stack my_fun
                (compile_bexp b (ident_list_to_map idents) n_args))))) as bm.
      assert (absstate_match_rel (AbsAnd s1 bm) fenv' stk).
      {
        eapply IHd1; try eassumption. reflexivity.
      }
      assert (absstate_match_rel (AbsAnd s2 bm) fenv' stk) by (eapply IHd2; try eassumption; reflexivity).
      invs H1. invs H4.
      econstructor; econstructor; try eassumption.
      invs H14. eassumption.
    - simpl in H1. subst. remember (SC.comp_logic n_args idents d1) as s1. remember (SC.comp_logic n_args idents d2) as s2. inversion H6.
      + subst. eapply IHd1 in H10; [ | try eassumption; try reflexivity .. ]. invs H10. econstructor.
        * eapply RelAbsOrLeft. eassumption.
        * eassumption.
      + subst. eapply IHd2 in H9; [ | try eassumption; try reflexivity .. ]. invs H9. econstructor.
        * eapply RelAbsOrRight. eassumption.
        * eassumption.
  Qed.
End UnprovenCorrectProofCompilable.
    
Require Import ProofCompilerCodeCompAgnostic.

Module UnprovenCorrectProofCompiler := CompilerAgnosticProofCompiler(UnprovenCorrectProofCompilable).
