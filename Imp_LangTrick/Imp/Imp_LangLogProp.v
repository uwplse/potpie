From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.
(* Add LoadPath "./" as Imp_LangTrick. *)
From Imp_LangTrick Require Import Imp.Imp_LangTrickLanguage LogicProp Imp.Imp_LangLogicHelpers.

Local Open Scope imp_langtrick_scope.

Definition assertion: Type := (list nat) -> nat_env -> Prop.

(* Substitutes out a variable for an expression in an arithmetic expression *)

Fixpoint imp_lang_aexp_update substout substin exp :=
  match exp with
  | VAR_Imp_Lang x => if String.eqb x substout then substin else VAR_Imp_Lang x
  | CONST_Imp_Lang n => CONST_Imp_Lang n
  | PARAM_Imp_Lang n => PARAM_Imp_Lang n
  | PLUS_Imp_Lang a1 a2 => 
  PLUS_Imp_Lang 
  (imp_lang_aexp_update substout substin a1) 
  (imp_lang_aexp_update substout substin a2)
  | MINUS_Imp_Lang a1 a2 => 
  MINUS_Imp_Lang
  (imp_lang_aexp_update substout substin a1) 
  (imp_lang_aexp_update substout substin a2)
  | APP_Imp_Lang f lst => 
  APP_Imp_Lang f (List.map (fun x => imp_lang_aexp_update substout substin x) lst)
  end.

(* first arg: ident to replace
 * second arg: arithmetic expression to replace with
 * third arg: arithmetic expression to replace inside
 * fourth arg: arithmetic expression result of replacement *)
Inductive imp_lang_aexp_update_rel : ident -> aexp_Imp_Lang -> aexp_Imp_Lang -> aexp_Imp_Lang -> Prop :=
| UpdateConstImp_Lang :
  forall x' replace_expr n,
    imp_lang_aexp_update_rel x' replace_expr (CONST_Imp_Lang n) (CONST_Imp_Lang n)
| UpdateParamImp_Lang :
  forall x' replace_expr k,
    imp_lang_aexp_update_rel x' replace_expr (PARAM_Imp_Lang k) (PARAM_Imp_Lang k)
| UpdateVarImp_LangEq :
  forall x' replace_expr x,
    x' = x ->
    imp_lang_aexp_update_rel x' replace_expr (VAR_Imp_Lang x) replace_expr
| UpdateVarImp_LangNeq :
  forall x' replace_expr x,
    x' <> x ->
    imp_lang_aexp_update_rel x' replace_expr (VAR_Imp_Lang x) (VAR_Imp_Lang x)
| UpdatePlusImp_Lang :
  forall x' replace_expr a1 a2 a1' a2',
    imp_lang_aexp_update_rel x' replace_expr a1 a1' ->
    imp_lang_aexp_update_rel x' replace_expr a2 a2' ->
    imp_lang_aexp_update_rel x' replace_expr (PLUS_Imp_Lang a1 a2) (PLUS_Imp_Lang a1' a2')
| UpdateMinusImp_Lang :
  forall x' replace_expr a1 a2 a1' a2',
    imp_lang_aexp_update_rel x' replace_expr a1 a1' ->
    imp_lang_aexp_update_rel x' replace_expr a2 a2' ->
    imp_lang_aexp_update_rel x' replace_expr (MINUS_Imp_Lang a1 a2) (MINUS_Imp_Lang a1' a2')
| UpdateAppImp_Lang :
  forall x' replace_expr f args args',
    imp_lang_args_update_rel x' replace_expr args args' ->
    imp_lang_aexp_update_rel x' replace_expr (APP_Imp_Lang f args) (APP_Imp_Lang f args')
with imp_lang_args_update_rel : ident -> aexp_Imp_Lang -> list aexp_Imp_Lang -> list aexp_Imp_Lang -> Prop :=
| UpdateImp_LangArgsNil :
  forall x' replace_expr,
    imp_lang_args_update_rel x' replace_expr nil nil
| UpdateImp_LangArgsCons :
  forall x' replace_expr arg args arg' args',
    imp_lang_aexp_update_rel x' replace_expr arg arg' ->
    imp_lang_args_update_rel x' replace_expr args args' ->
    imp_lang_args_update_rel x' replace_expr (arg :: args) (arg' :: args').

Scheme imp_lang_aexp_update_rel_mut_ind := Induction for imp_lang_aexp_update_rel Sort Prop
    with imp_lang_args_update_rel_mut_ind := Induction for imp_lang_args_update_rel Sort Prop.

Combined Scheme imp_lang_aexp_args_update_rel_mut_ind from imp_lang_aexp_update_rel_mut_ind, imp_lang_args_update_rel_mut_ind.

Definition
  imp_lang_aexp_args_update_rel_theorem (P: ident -> aexp_Imp_Lang -> aexp_Imp_Lang -> aexp_Imp_Lang -> Prop)
  (P0: ident -> aexp_Imp_Lang -> list aexp_Imp_Lang -> list aexp_Imp_Lang -> Prop) : Prop :=
  (forall (x: ident) (a: aexp_Imp_Lang) (aexp aexp': aexp_Imp_Lang),
      imp_lang_aexp_update_rel x a aexp aexp' ->
      P x a aexp aexp') /\
    (forall (x: ident) (a: aexp_Imp_Lang) (aexps aexps': list aexp_Imp_Lang),
        imp_lang_args_update_rel x a aexps aexps' ->
        P0 x a aexps aexps').

Local Definition imp_lang_aexp_args_update_rel_theorem_P (P: ident -> aexp_Imp_Lang -> aexp_Imp_Lang -> aexp_Imp_Lang -> Prop):
  forall (x: ident) (a: aexp_Imp_Lang) (aexp aexp': aexp_Imp_Lang), imp_lang_aexp_update_rel x a aexp aexp' -> Prop :=
  fun (x: ident) (a: aexp_Imp_Lang) (aexp aexp': aexp_Imp_Lang) =>
  fun (_: imp_lang_aexp_update_rel x a aexp aexp') =>
    P x a aexp aexp'.

Local Definition imp_lang_aexp_args_update_rel_theorem_P0 (P0: ident -> aexp_Imp_Lang -> list aexp_Imp_Lang -> list aexp_Imp_Lang -> Prop):
  forall (x: ident) (a: aexp_Imp_Lang) (aexps aexps': list aexp_Imp_Lang), imp_lang_args_update_rel x a aexps aexps' -> Prop :=
  fun (x: ident) (a: aexp_Imp_Lang) (aexps aexps': list aexp_Imp_Lang) =>
  fun (_: imp_lang_args_update_rel x a aexps aexps') =>
    P0 x a aexps aexps'.

Ltac imp_lang_aexp_args_update_mutual_induction P P0 P_def P0_def :=
  pose (imp_lang_aexp_args_update_rel_theorem_P P_def) as P;
  pose (imp_lang_aexp_args_update_rel_theorem_P0 P0_def) as P0;
  apply (imp_lang_aexp_args_update_rel_mut_ind P P0);
  unfold P, P0; unfold imp_lang_aexp_args_update_rel_theorem_P, imp_lang_aexp_args_update_rel_theorem_P0;
  unfold P_def, P0_def.


Fixpoint imp_lang_bexp_update substout substin exp :=
  match exp with
  |TRUE_Imp_Lang => TRUE_Imp_Lang
  |FALSE_Imp_Lang => FALSE_Imp_Lang
  |AND_Imp_Lang b1 b2 => 
    AND_Imp_Lang 
    (imp_lang_bexp_update substout substin b1) 
    (imp_lang_bexp_update substout substin b2)
  |OR_Imp_Lang b1 b2 => 
    OR_Imp_Lang 
    (imp_lang_bexp_update substout substin b1) 
    (imp_lang_bexp_update substout substin b2)
  |NEG_Imp_Lang b =>
    NEG_Imp_Lang
    (imp_lang_bexp_update substout substin b)
  |LEQ_Imp_Lang a1 a2 => 
    LEQ_Imp_Lang
    (imp_lang_aexp_update substout substin a1) 
    (imp_lang_aexp_update substout substin a2)
    end
.

Inductive imp_lang_bexp_update_rel : ident -> aexp_Imp_Lang -> bexp_Imp_Lang -> bexp_Imp_Lang -> Prop :=
| UpdateTrueImp_Lang :
  forall x' replace_expr,
    imp_lang_bexp_update_rel x' replace_expr TRUE_Imp_Lang TRUE_Imp_Lang
| UpdateFalseImp_Lang :
  forall x' replace_expr,
    imp_lang_bexp_update_rel x' replace_expr FALSE_Imp_Lang FALSE_Imp_Lang
| UpdateNegImp_Lang :
  forall x' replace_expr b b',
    imp_lang_bexp_update_rel x' replace_expr b b' ->
    imp_lang_bexp_update_rel x' replace_expr (NEG_Imp_Lang b) (NEG_Imp_Lang b')
| UpdateAndImp_Lang :
  forall x' replace_expr b1 b2 b1' b2',
    imp_lang_bexp_update_rel x' replace_expr b1 b1' ->
    imp_lang_bexp_update_rel x' replace_expr b2 b2' ->
    imp_lang_bexp_update_rel x' replace_expr (AND_Imp_Lang b1 b2) (AND_Imp_Lang b1' b2')
| UpdateOrImp_Lang :
  forall x' replace_expr b1 b2 b1' b2',
    imp_lang_bexp_update_rel x' replace_expr b1 b1' ->
    imp_lang_bexp_update_rel x' replace_expr b2 b2' ->
    imp_lang_bexp_update_rel x' replace_expr (OR_Imp_Lang b1 b2) (OR_Imp_Lang b1' b2')
| UpdateLeqImp_Lang :
  forall x' replace_expr a1 a2 a1' a2',
    imp_lang_aexp_update_rel x' replace_expr a1 a1' ->
    imp_lang_aexp_update_rel x' replace_expr a2 a2' ->
    imp_lang_bexp_update_rel x' replace_expr (LEQ_Imp_Lang a1 a2) (LEQ_Imp_Lang a1' a2').

(* Copied from cdf-mech-sem HoareLogic.v *)
Definition aand (P Q: assertion) : assertion :=
  fun dbenv s => P dbenv s /\ Q dbenv s.

Definition aor (P Q: assertion) : assertion :=
  fun dbenv s => P dbenv s \/ Q dbenv s.

Definition anot (P : assertion) : assertion :=
  fun dbenv s => not (P dbenv s).

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp_Imp_Lang) (v: nat) (fenv: fun_env): assertion :=
  fun dbenv nenv => a_Imp_Lang a dbenv fenv nenv v.

Definition aparam (p: nat) (v: nat) : assertion :=
  fun dbenv nenv => nth_error dbenv p = Some v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp_Imp_Lang) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => b_Imp_Lang b dbenv fenv nenv true /\ P dbenv nenv.

Definition afalse (b: bexp_Imp_Lang) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => b_Imp_Lang b dbenv fenv nenv false /\ P dbenv nenv.

Definition aupdate (x: ident) (a: aexp_Imp_Lang) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => (forall n, a_Imp_Lang a dbenv fenv nenv n -> P dbenv (update x n nenv)). 

Inductive Imp_Lang_lp :=
  |Imp_Lang_lp_arith (l: LogicProp nat aexp_Imp_Lang)
|Imp_Lang_lp_bool (l: LogicProp bool bexp_Imp_Lang).

Inductive Imp_Lang_lp_prop_rel : (aexp_Imp_Lang -> Prop) -> (bexp_Imp_Lang -> Prop) -> Imp_Lang_lp -> Prop :=
| Imp_LangLPPropArith :
  forall (phi1: aexp_Imp_Lang -> Prop) (phi2: bexp_Imp_Lang -> Prop) (l: LogicProp nat aexp_Imp_Lang),
    prop_rel phi1 l ->
    Imp_Lang_lp_prop_rel phi1 phi2 (Imp_Lang_lp_arith l)
| Imp_LangLPPropBool :
  forall (phi1: aexp_Imp_Lang -> Prop) (phi2: bexp_Imp_Lang -> Prop) (l: LogicProp bool bexp_Imp_Lang),
    prop_rel phi2 l ->
    Imp_Lang_lp_prop_rel phi1 phi2 (Imp_Lang_lp_bool l).

Inductive AbsEnv: Type :=
| AbsEnvLP (s: Imp_Lang_lp)
| AbsEnvAnd (s1 s2: AbsEnv)
| AbsEnvOr (s1 s2: AbsEnv).

Inductive AbsEnv_prop_rel : (aexp_Imp_Lang -> Prop) -> (bexp_Imp_Lang -> Prop) -> AbsEnv -> Prop :=
| Imp_LangLogPropRelLP :
  forall (phi1: aexp_Imp_Lang -> Prop) (phi2: bexp_Imp_Lang -> Prop) (l: Imp_Lang_lp),
    Imp_Lang_lp_prop_rel phi1 phi2 l ->
    AbsEnv_prop_rel phi1 phi2 (AbsEnvLP l)
| Imp_LangLogPropRelAnd :
  forall (phi1: aexp_Imp_Lang -> Prop) (phi2: bexp_Imp_Lang -> Prop) (l1 l2: AbsEnv),
    AbsEnv_prop_rel phi1 phi2 l1 ->
    AbsEnv_prop_rel phi1 phi2 l2 ->
    AbsEnv_prop_rel phi1 phi2 (AbsEnvAnd l1 l2)
| Imp_LangLogPropRelOr :
  forall (phi1: aexp_Imp_Lang -> Prop) (phi2: bexp_Imp_Lang -> Prop) (l1 l2: AbsEnv),
    AbsEnv_prop_rel phi1 phi2 l1 ->
    AbsEnv_prop_rel phi1 phi2 l2 ->
    AbsEnv_prop_rel phi1 phi2 (AbsEnvOr l1 l2).

Inductive Imp_Lang_lp_rel: Imp_Lang_lp -> fun_env -> list nat -> nat_env -> Prop :=
| Imp_Lang_lp_rel_bool :
  forall l fenv nenv dbenv,
  eval_prop_rel (fun b v => b_Imp_Lang b dbenv fenv nenv v) l ->
  Imp_Lang_lp_rel (Imp_Lang_lp_bool l) fenv dbenv nenv
| Imp_Lang_lp_rel_arith : 
  forall l fenv nenv dbenv,
    eval_prop_rel (fun a v => a_Imp_Lang a dbenv fenv nenv v) l ->
    Imp_Lang_lp_rel (Imp_Lang_lp_arith l) fenv dbenv nenv. 

Inductive AbsEnv_rel: AbsEnv -> fun_env -> list nat -> nat_env -> Prop :=
| AbsEnv_leaf : 
  forall l fenv dbenv nenv, 
  Imp_Lang_lp_rel l fenv dbenv nenv -> 
  AbsEnv_rel (AbsEnvLP l) fenv dbenv nenv
| AbsEnv_and : 
  forall l1 l2 fenv dbenv nenv,
  AbsEnv_rel l1 fenv dbenv nenv -> 
  AbsEnv_rel l2 fenv dbenv nenv -> 
  AbsEnv_rel (AbsEnvAnd l1 l2) fenv dbenv nenv
| AbsEnv_or_left : 
  forall l1 l2 fenv dbenv nenv,
  AbsEnv_rel l1 fenv dbenv nenv -> 
  AbsEnv_rel (AbsEnvOr l1 l2) fenv dbenv nenv
| AbsEnv_or_right : 
  forall l1 l2 fenv dbenv nenv,
  AbsEnv_rel l2 fenv dbenv nenv -> 
  AbsEnv_rel (AbsEnvOr l1 l2) fenv dbenv nenv
. 

