From Coq Require Import String List Peano Arith Program.Equality.
From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import ProofCompilerBase.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel Imp_LangLogSubst CompilerAssumptionLogicTrans.
From Imp_LangTrick Require Import ParamsWellFormed FunctionWellFormed.

(*
 * Well-foundedness of Imp_Lang Logic
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.

Require Import Coq.Init.Logic.

Import EqNotations.

Section Imp_LangHoareWFAliases.
  Context (imp_wf := fun (idents: list ident) (i: imp_Imp_Lang) =>
  imp_rec_rel (var_map_wf_wrt_imp idents) i).

  (** num_args: frequently also called `n_args` or `args`*)
Inductive hl_Imp_Lang_wf (fenv: fun_env) (func_list: list fun_Imp_Lang) (idents: list ident) (num_args: nat) (d d': AbsEnv) (i: imp_Imp_Lang) (facts : implication_env)
(* (fact_cert : fact_env_valid facts fenv) *)
: (hl_Imp_Lang d i d' facts fenv) -> Prop :=
| HLImp_LangWFSkip :
  forall (hl: hl_Imp_Lang d i d' facts fenv),
  forall (HSkip : SKIP_Imp_Lang = i ),
  forall (Heq: d = d'),
    hl =
      rew [fun H : AbsEnv => hl_Imp_Lang d i H facts fenv] Heq in
    rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H d facts fenv]
        (HSkip) in
      hl_Imp_Lang_skip d facts fenv ->
      AbsEnv_prop_wf idents d ->
      log_Imp_Lang_wf func_list fenv d ->
      log_Imp_Lang_wf_map idents d ->
      AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
      hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hl
| HLImp_LangWFAssign :
  forall x a,
  forall (hl: hl_Imp_Lang d i d' facts fenv)
    (Heq: ASSIGN_Imp_Lang x a = i)
    (Hsubst: (Imp_LangLogSubst.subst_AbsEnv x a d') = d),
    hl =
      rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Heq in
    rew [fun H : AbsEnv => hl_Imp_Lang H (ASSIGN_Imp_Lang x a) d' facts fenv]
        Hsubst in
      hl_Imp_Lang_assign d' facts fenv x a ->
      AbsEnv_prop_wf idents d' ->
      imp_wf idents i ->
      log_Imp_Lang_wf func_list fenv d' ->
      log_Imp_Lang_wf_map idents d' ->
      AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
      ParamsWellFormed.all_params_ok_aexp num_args a ->
      fun_app_well_formed fenv func_list a ->
      hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hl
| HLImp_LangWFSeq :
  forall d0 i1 i2,
  forall (hl1: hl_Imp_Lang d i1 d0 facts fenv) (hl2: hl_Imp_Lang d0 i2 d' facts fenv),
  forall (Heq: SEQ_Imp_Lang i1 i2 = i),
  forall (hlseq : hl_Imp_Lang d i d' facts fenv),
    hlseq =
      rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv]
          Heq in
    hl_Imp_Lang_seq d d' d0 facts fenv i1 i2 hl1 hl2 ->
    imp_wf idents (SEQ_Imp_Lang i1 i2) ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents d0 ->
    AbsEnv_prop_wf idents d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args d d0 i1 facts hl1 ->
    hl_Imp_Lang_wf fenv func_list idents num_args d0 d' i2 facts hl2 ->
    log_Imp_Lang_wf func_list fenv d ->
    log_Imp_Lang_wf func_list fenv d0 ->
    log_Imp_Lang_wf func_list fenv d' ->
    log_Imp_Lang_wf_map idents d ->
    log_Imp_Lang_wf_map idents d0 ->
    log_Imp_Lang_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d0 ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hlseq
| HLImp_LangWFIf :
  forall b i1 i2,
  forall (hl1: hl_Imp_Lang (atrueImp_Lang b d) i1 d' facts fenv)
    (hl2: hl_Imp_Lang (afalseImp_Lang b d) i2 d' facts fenv)
    (heq: IF_Imp_Lang b i1 i2 = i)
    (hlif: hl_Imp_Lang d i d' facts fenv),
    hlif =
      rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv]
          heq in
    hl_Imp_Lang_if d d' b i1 i2 facts fenv hl1 hl2 ->
    imp_wf idents (IF_Imp_Lang b i1 i2) ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args (atrueImp_Lang b d) d' i1 facts hl1 ->
    hl_Imp_Lang_wf fenv func_list idents num_args (afalseImp_Lang b d) d' i2 facts hl2 ->
    log_Imp_Lang_wf func_list fenv d ->
    log_Imp_Lang_wf func_list fenv d' ->
    log_Imp_Lang_wf_map idents d ->
    log_Imp_Lang_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hlif
| HLImp_LangWFWhile :
  forall (b : bexp_Imp_Lang) (i__body : imp_Imp_Lang)
  (hl : hl_Imp_Lang (atrueImp_Lang b d) i__body d facts fenv)
  (hl_while : hl_Imp_Lang d i d' facts fenv) (HeqP : afalseImp_Lang b d = d')
  (Heq : (while b loop i__body done) = i),
    hl_while =
      rew [fun H : AbsEnv => hl_Imp_Lang d i H facts fenv]
          HeqP in
    rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H (afalseImp_Lang b d) facts fenv]
        Heq in
      hl_Imp_Lang_while d b i__body facts fenv hl ->
    imp_wf idents (WHILE_Imp_Lang b i__body) ->
    AbsEnv_prop_wf idents d ->
    hl_Imp_Lang_wf fenv func_list idents num_args (atrueImp_Lang b d) d i__body facts hl ->
    log_Imp_Lang_wf func_list fenv d ->
    log_Imp_Lang_wf_map idents d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hl_while
| HLImp_LangWFConsequencePre :
  forall P n,
  forall (hl: hl_Imp_Lang P i d' facts fenv)
    (aimp1: aimpImp_Lang d P fenv)
    (hlcons: hl_Imp_Lang d i d' facts fenv)
    (nth : nth_error facts n = Some (d, P))
    (imp : aimpImp_Lang d P fenv),
    hlcons = (hl_Imp_Lang_consequence_pre P d' d i n facts fenv hl nth imp) ->
    imp_wf idents i ->
    AbsEnv_prop_wf idents P ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args P d' i facts hl ->
    log_Imp_Lang_wf func_list fenv P ->
    log_Imp_Lang_wf func_list fenv d ->
    log_Imp_Lang_wf func_list fenv d' ->
    log_Imp_Lang_wf_map idents P ->
    log_Imp_Lang_wf_map idents d ->
    log_Imp_Lang_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) P ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hlcons
| HLImp_LangWFConsequencePost :
  forall P n,
  forall (hl: hl_Imp_Lang d i P facts fenv)
    (* (aimp1: aimpImp_Lang d P fenv) *)
    (hlcons: hl_Imp_Lang d i d' facts fenv)
    (nth : nth_error facts n = Some (P, d'))
    (imp : aimpImp_Lang P d' fenv),
    hlcons = (hl_Imp_Lang_consequence_post d P d' i n facts fenv hl nth imp) ->
    imp_wf idents i ->
    AbsEnv_prop_wf idents P ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args d P i facts hl ->
    log_Imp_Lang_wf func_list fenv P ->
    log_Imp_Lang_wf func_list fenv d ->
    log_Imp_Lang_wf func_list fenv d' ->
    log_Imp_Lang_wf_map idents P ->
    log_Imp_Lang_wf_map idents d ->
    log_Imp_Lang_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) P ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Imp_Lang_wf fenv func_list idents num_args d d' i facts hlcons.

End Imp_LangHoareWFAliases.
