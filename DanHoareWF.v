From Coq Require Import String List Peano Arith Program.Equality.
From DanTrick Require Import StackLogic DanLogHoare DanTrickLanguage EnvToStack StackLanguage DanLogProp LogicProp StackLangTheorems StackLogicBase.
From DanTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From DanTrick Require Export ProofSubstitution ImpVarMapTheorems DanLogSubstAdequate.
From DanTrick Require Import ProofCompilerBase.
From DanTrick Require Import DanImpHigherOrderRel DanLogSubst CompilerAssumptionLogicTrans.
From DanTrick Require Import ParamsWellFormed FunctionWellFormed.

(*
 * Well-foundedness of Dan Logic
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Require Import Coq.Init.Logic.

Import EqNotations.

Section DanHoareWFAliases.
  Context (imp_wf := fun (idents: list ident) (i: imp_Dan) =>
  imp_rec_rel (var_map_wf_wrt_imp idents) i).

  (** num_args: frequently also called `n_args` or `args`*)
Inductive hl_Dan_wf (fenv: fun_env) (func_list: list fun_Dan) (idents: list ident) (num_args: nat) (d d': AbsEnv) (i: imp_Dan) : (hl_Dan d i d' fenv) -> Prop :=
| HLDanWFSkip :
  forall (hl: hl_Dan d i d' fenv),
  forall (HSkip : SKIP_Dan = i ),
  forall (Heq: d = d'),
    hl =
      rew [fun H : AbsEnv => hl_Dan d i H fenv] Heq in
    rew [fun H : imp_Dan => hl_Dan d H d fenv]
        (HSkip) in
      hl_Dan_skip d fenv ->
      AbsEnv_prop_wf idents d ->
      log_Dan_wf func_list fenv d ->
      log_Dan_wf_map idents d ->
      AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
      hl_Dan_wf fenv func_list idents num_args d d' i hl
| HLDanWFAssign :
  forall x a,
  forall (hl: hl_Dan d i d' fenv)
    (Heq: ASSIGN_Dan x a = i)
    (Hsubst: (DanLogSubst.subst_AbsEnv x a d') = d),
    hl =
      rew [fun H : imp_Dan => hl_Dan d H d' fenv] Heq in
    rew [fun H : AbsEnv => hl_Dan H (ASSIGN_Dan x a) d' fenv]
        Hsubst in
      hl_Dan_assign d' fenv x a ->
      AbsEnv_prop_wf idents d' ->
      imp_wf idents i ->
      log_Dan_wf func_list fenv d' ->
      log_Dan_wf_map idents d' ->
      AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
      ParamsWellFormed.all_params_ok_aexp num_args a ->
      fun_app_well_formed fenv func_list a ->
      hl_Dan_wf fenv func_list idents num_args d d' i hl
| HLDanWFSeq :
  forall d0 i1 i2,
  forall (hl1: hl_Dan d i1 d0 fenv) (hl2: hl_Dan d0 i2 d' fenv),
  forall (Heq: SEQ_Dan i1 i2 = i),
  forall (hlseq : hl_Dan d i d' fenv),
    hlseq =
      rew [fun H : imp_Dan => hl_Dan d H d' fenv]
          Heq in
    hl_Dan_seq d d' d0 i1 i2 fenv hl1 hl2 ->
    imp_wf idents (SEQ_Dan i1 i2) ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents d0 ->
    AbsEnv_prop_wf idents d' ->
    hl_Dan_wf fenv func_list idents num_args d d0 i1 hl1 ->
    hl_Dan_wf fenv func_list idents num_args d0 d' i2 hl2 ->
    log_Dan_wf func_list fenv d ->
    log_Dan_wf func_list fenv d0 ->
    log_Dan_wf func_list fenv d' ->
    log_Dan_wf_map idents d ->
    log_Dan_wf_map idents d0 ->
    log_Dan_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d0 ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Dan_wf fenv func_list idents num_args d d' i hlseq
| HLDanWFIf :
  forall b i1 i2,
  forall (hl1: hl_Dan (atrueDan b d) i1 d' fenv)
    (hl2: hl_Dan (afalseDan b d) i2 d' fenv)
    (heq: IF_Dan b i1 i2 = i)
    (hlif: hl_Dan d i d' fenv),
    hlif =
      rew [fun H : imp_Dan => hl_Dan d H d' fenv]
          heq in
    hl_Dan_if d d' b i1 i2 fenv hl1 hl2 ->
    imp_wf idents (IF_Dan b i1 i2) ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents d' ->
    hl_Dan_wf fenv func_list idents num_args (atrueDan b d) d' i1 hl1 ->
    hl_Dan_wf fenv func_list idents num_args (afalseDan b d) d' i2 hl2 ->
    log_Dan_wf func_list fenv d ->
    log_Dan_wf func_list fenv d' ->
    log_Dan_wf_map idents d ->
    log_Dan_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Dan_wf fenv func_list idents num_args d d' i hlif
| HLDanWFWhile :
  forall (b : bexp_Dan) (i__body : imp_Dan)
  (hl : hl_Dan (atrueDan b d) i__body d fenv)
  (hl_while : hl_Dan d i d' fenv) (HeqP : afalseDan b d = d')
  (Heq : (while b loop i__body done) = i),
    hl_while =
      rew [fun H : AbsEnv => hl_Dan d i H fenv]
          HeqP in
    rew [fun H : imp_Dan => hl_Dan d H (afalseDan b d) fenv]
        Heq in
      hl_Dan_while d b i__body fenv hl ->
    imp_wf idents (WHILE_Dan b i__body) ->
    AbsEnv_prop_wf idents d ->
    hl_Dan_wf fenv func_list idents num_args (atrueDan b d) d i__body hl ->
    log_Dan_wf func_list fenv d ->
    log_Dan_wf_map idents d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    hl_Dan_wf fenv func_list idents num_args d d' i hl_while
| HLDanWFConsequence :
  forall P Q,
  forall (hl: hl_Dan P i Q fenv)
    (aimp1: aimpDan d P fenv)
    (aimp2: aimpDan Q d' fenv)
    (hlcons: hl_Dan d i d' fenv),
    hlcons = (hl_Dan_consequence P Q d d' i fenv hl aimp1 aimp2) ->
    imp_wf idents i ->
    AbsEnv_prop_wf idents P ->
    AbsEnv_prop_wf idents d ->
    AbsEnv_prop_wf idents Q ->
    AbsEnv_prop_wf idents d' ->
    hl_Dan_wf fenv func_list idents num_args P Q i hl ->
    log_Dan_wf func_list fenv P ->
    log_Dan_wf func_list fenv d ->
    log_Dan_wf func_list fenv Q ->
    log_Dan_wf func_list fenv d' ->
    log_Dan_wf_map idents P ->
    log_Dan_wf_map idents d ->
    log_Dan_wf_map idents Q ->
    log_Dan_wf_map idents d' ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) P ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) Q ->
    AbsEnv_prop_rel (all_params_ok_aexp num_args) (all_params_ok_bexp num_args) d' ->
    hl_Dan_wf fenv func_list idents num_args d d' i hlcons.

End DanHoareWFAliases.
