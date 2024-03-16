From Coq Require Import List String Arith Psatz Peano Program.Equality.


From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogProp Imp_LangLogSubst 
LogicProp Imp_LangLogHoare StackLogic.
From Imp_LangTrick Require Import StackLanguage LogicProp StackSubstitution
StackPurest StackExprWellFormed LogicTranslationBase.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Inductive Imp_Lang_fact_env_valid_relation: implication_env -> fun_env -> Prop :=
| fact_env_valid_nil : 
  forall fenv,
    Imp_Lang_fact_env_valid_relation nil fenv
| fact_env_valid_cons :
  forall P Q fact_env fenv, 
    aimpImp_Lang P Q fenv ->
    Imp_Lang_fact_env_valid_relation fact_env fenv ->
    Imp_Lang_fact_env_valid_relation ((P, Q)::fact_env) fenv. 

Lemma Imp_Lang_valid_rel_implies_valid : 
  forall fact_env fenv,
    Imp_Lang_fact_env_valid_relation fact_env fenv ->
    Imp_LangLogHoare.fact_env_valid fact_env fenv.
Proof.
  induction fact_env; intros.
  - unfold Imp_LangLogHoare.fact_env_valid.
    intros. invs H0.
  - unfold Imp_LangLogHoare.fact_env_valid; intros. invs H. destruct H0.
    + invs H0. assumption.
    + specialize (IHfact_env fenv H5).
      unfold Imp_LangLogHoare.fact_env_valid in IHfact_env.
      apply (IHfact_env P Q H0).
Qed.

Inductive stk_fact_env_valid_relation: implication_env_stk -> fun_env_stk -> Prop :=
| stk_fact_env_valid_nil : 
  forall fenv,
    stk_fact_env_valid_relation nil fenv
| stk_fact_env_valid_cons :
  forall P Q fact_env fenv, 
    aimpstk P Q fenv ->
    stk_fact_env_valid_relation fact_env fenv ->
    stk_fact_env_valid_relation ((P, Q)::fact_env) fenv. 

Lemma stk_valid_rel_implies_valid : 
  forall fact_env fenv,
    stk_fact_env_valid_relation fact_env fenv ->
    fact_env_valid fact_env fenv.
Proof.
  induction fact_env; intros.
  - unfold fact_env_valid.
    intros. invs H0.
  - unfold fact_env_valid; intros. invs H. destruct H0.
    + invs H0. assumption.
    + specialize (IHfact_env fenv H5).
      unfold fact_env_valid in IHfact_env.
      apply (IHfact_env P Q H0).
Qed.

(* absstate_match_rel state fenv_s (stk ++ rho) ->
Imp_Lang_log_rel imp_lang_log fenv_d dbenv nenv. *)

Inductive valid_implication_translation : implication_env -> implication_env_stk -> fun_env -> fun_env_stk -> list ident -> Prop :=
| valid_imp_trans_nil : 
  forall fenv stk_fenv map, 
    valid_implication_translation nil nil fenv stk_fenv map
| valid_imp_trans_cons : 
  forall stk_env imp_lang_env fenv stk_fenv P Q stk_P stk_Q map, 
    fact_env_valid ((stk_P, stk_Q)::stk_env) stk_fenv ->
    Imp_LangLogHoare.fact_env_valid ((P, Q)::imp_lang_env) fenv ->
    valid_implication_translation imp_lang_env stk_env fenv stk_fenv map ->
    ((forall nenv dbenv stk, 
      state_to_stack map nenv dbenv stk ->
      AbsEnv_rel P fenv dbenv nenv <-> absstate_match_rel stk_P stk_fenv stk)
      /\
    (forall nenv dbenv stk, 
      state_to_stack map nenv dbenv stk ->
      AbsEnv_rel Q fenv dbenv nenv <-> absstate_match_rel stk_Q stk_fenv stk)) ->
    valid_implication_translation ((P, Q)::imp_lang_env) ((stk_P, stk_Q)::stk_env) fenv stk_fenv map. 