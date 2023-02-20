From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.
Add LoadPath "./" as DanTrick.
Require Import DanTrick.DanTrickLanguage DanTrick.LogicProp DanTrick.DanLogicHelpers.

Local Open Scope dantrick_scope.

Definition assertion: Type := (list nat) -> nat_env -> Prop.

(* Substitutes out a variable for an expression in an arithmetic expression *)

Fixpoint dan_aexp_update substout substin exp :=
  match exp with
  | VAR_Dan x => if String.eqb x substout then substin else VAR_Dan x
  | CONST_Dan n => CONST_Dan n
  | PARAM_Dan n => PARAM_Dan n
  | PLUS_Dan a1 a2 => 
  PLUS_Dan 
  (dan_aexp_update substout substin a1) 
  (dan_aexp_update substout substin a2)
  | MINUS_Dan a1 a2 => 
  MINUS_Dan
  (dan_aexp_update substout substin a1) 
  (dan_aexp_update substout substin a2)
  | APP_Dan f lst => 
  APP_Dan f (List.map (fun x => dan_aexp_update substout substin x) lst)
  end.

(* first arg: ident to replace
 * second arg: arithmetic expression to replace with
 * third arg: arithmetic expression to replace inside
 * fourth arg: arithmetic expression result of replacement *)
Inductive dan_aexp_update_rel : ident -> aexp_Dan -> aexp_Dan -> aexp_Dan -> Prop :=
| UpdateConstDan :
  forall x' replace_expr n,
    dan_aexp_update_rel x' replace_expr (CONST_Dan n) (CONST_Dan n)
| UpdateParamDan :
  forall x' replace_expr k,
    dan_aexp_update_rel x' replace_expr (PARAM_Dan k) (PARAM_Dan k)
| UpdateVarDanEq :
  forall x' replace_expr x,
    x' = x ->
    dan_aexp_update_rel x' replace_expr (VAR_Dan x) replace_expr
| UpdateVarDanNeq :
  forall x' replace_expr x,
    x' <> x ->
    dan_aexp_update_rel x' replace_expr (VAR_Dan x) (VAR_Dan x)
| UpdatePlusDan :
  forall x' replace_expr a1 a2 a1' a2',
    dan_aexp_update_rel x' replace_expr a1 a1' ->
    dan_aexp_update_rel x' replace_expr a2 a2' ->
    dan_aexp_update_rel x' replace_expr (PLUS_Dan a1 a2) (PLUS_Dan a1' a2')
| UpdateMinusDan :
  forall x' replace_expr a1 a2 a1' a2',
    dan_aexp_update_rel x' replace_expr a1 a1' ->
    dan_aexp_update_rel x' replace_expr a2 a2' ->
    dan_aexp_update_rel x' replace_expr (MINUS_Dan a1 a2) (MINUS_Dan a1' a2')
| UpdateAppDan :
  forall x' replace_expr f args args',
    dan_args_update_rel x' replace_expr args args' ->
    dan_aexp_update_rel x' replace_expr (APP_Dan f args) (APP_Dan f args')
with dan_args_update_rel : ident -> aexp_Dan -> list aexp_Dan -> list aexp_Dan -> Prop :=
| UpdateDanArgsNil :
  forall x' replace_expr,
    dan_args_update_rel x' replace_expr nil nil
| UpdateDanArgsCons :
  forall x' replace_expr arg args arg' args',
    dan_aexp_update_rel x' replace_expr arg arg' ->
    dan_args_update_rel x' replace_expr args args' ->
    dan_args_update_rel x' replace_expr (arg :: args) (arg' :: args').

Scheme dan_aexp_update_rel_mut_ind := Induction for dan_aexp_update_rel Sort Prop
    with dan_args_update_rel_mut_ind := Induction for dan_args_update_rel Sort Prop.

Combined Scheme dan_aexp_args_update_rel_mut_ind from dan_aexp_update_rel_mut_ind, dan_args_update_rel_mut_ind.

Definition
  dan_aexp_args_update_rel_theorem (P: ident -> aexp_Dan -> aexp_Dan -> aexp_Dan -> Prop)
  (P0: ident -> aexp_Dan -> list aexp_Dan -> list aexp_Dan -> Prop) : Prop :=
  (forall (x: ident) (a: aexp_Dan) (aexp aexp': aexp_Dan),
      dan_aexp_update_rel x a aexp aexp' ->
      P x a aexp aexp') /\
    (forall (x: ident) (a: aexp_Dan) (aexps aexps': list aexp_Dan),
        dan_args_update_rel x a aexps aexps' ->
        P0 x a aexps aexps').

Local Definition dan_aexp_args_update_rel_theorem_P (P: ident -> aexp_Dan -> aexp_Dan -> aexp_Dan -> Prop):
  forall (x: ident) (a: aexp_Dan) (aexp aexp': aexp_Dan), dan_aexp_update_rel x a aexp aexp' -> Prop :=
  fun (x: ident) (a: aexp_Dan) (aexp aexp': aexp_Dan) =>
  fun (_: dan_aexp_update_rel x a aexp aexp') =>
    P x a aexp aexp'.

Local Definition dan_aexp_args_update_rel_theorem_P0 (P0: ident -> aexp_Dan -> list aexp_Dan -> list aexp_Dan -> Prop):
  forall (x: ident) (a: aexp_Dan) (aexps aexps': list aexp_Dan), dan_args_update_rel x a aexps aexps' -> Prop :=
  fun (x: ident) (a: aexp_Dan) (aexps aexps': list aexp_Dan) =>
  fun (_: dan_args_update_rel x a aexps aexps') =>
    P0 x a aexps aexps'.

Ltac dan_aexp_args_update_mutual_induction P P0 P_def P0_def :=
  pose (dan_aexp_args_update_rel_theorem_P P_def) as P;
  pose (dan_aexp_args_update_rel_theorem_P0 P0_def) as P0;
  apply (dan_aexp_args_update_rel_mut_ind P P0);
  unfold P, P0; unfold dan_aexp_args_update_rel_theorem_P, dan_aexp_args_update_rel_theorem_P0;
  unfold P_def, P0_def.


Fixpoint dan_bexp_update substout substin exp :=
  match exp with
  |TRUE_Dan => TRUE_Dan
  |FALSE_Dan => FALSE_Dan
  |AND_Dan b1 b2 => 
    AND_Dan 
    (dan_bexp_update substout substin b1) 
    (dan_bexp_update substout substin b2)
  |OR_Dan b1 b2 => 
    OR_Dan 
    (dan_bexp_update substout substin b1) 
    (dan_bexp_update substout substin b2)
  |NEG_Dan b =>
    NEG_Dan
    (dan_bexp_update substout substin b)
  |LEQ_Dan a1 a2 => 
    LEQ_Dan
    (dan_aexp_update substout substin a1) 
    (dan_aexp_update substout substin a2)
    end
.

Inductive dan_bexp_update_rel : ident -> aexp_Dan -> bexp_Dan -> bexp_Dan -> Prop :=
| UpdateTrueDan :
  forall x' replace_expr,
    dan_bexp_update_rel x' replace_expr TRUE_Dan TRUE_Dan
| UpdateFalseDan :
  forall x' replace_expr,
    dan_bexp_update_rel x' replace_expr FALSE_Dan FALSE_Dan
| UpdateNegDan :
  forall x' replace_expr b b',
    dan_bexp_update_rel x' replace_expr b b' ->
    dan_bexp_update_rel x' replace_expr (NEG_Dan b) (NEG_Dan b')
| UpdateAndDan :
  forall x' replace_expr b1 b2 b1' b2',
    dan_bexp_update_rel x' replace_expr b1 b1' ->
    dan_bexp_update_rel x' replace_expr b2 b2' ->
    dan_bexp_update_rel x' replace_expr (AND_Dan b1 b2) (AND_Dan b1' b2')
| UpdateOrDan :
  forall x' replace_expr b1 b2 b1' b2',
    dan_bexp_update_rel x' replace_expr b1 b1' ->
    dan_bexp_update_rel x' replace_expr b2 b2' ->
    dan_bexp_update_rel x' replace_expr (OR_Dan b1 b2) (OR_Dan b1' b2')
| UpdateLeqDan :
  forall x' replace_expr a1 a2 a1' a2',
    dan_aexp_update_rel x' replace_expr a1 a1' ->
    dan_aexp_update_rel x' replace_expr a2 a2' ->
    dan_bexp_update_rel x' replace_expr (LEQ_Dan a1 a2) (LEQ_Dan a1' a2').

(* Copied from cdf-mech-sem HoareLogic.v *)
Definition aand (P Q: assertion) : assertion :=
  fun dbenv s => P dbenv s /\ Q dbenv s.

Definition aor (P Q: assertion) : assertion :=
  fun dbenv s => P dbenv s \/ Q dbenv s.

Definition anot (P : assertion) : assertion :=
  fun dbenv s => not (P dbenv s).

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp_Dan) (v: nat) (fenv: fun_env): assertion :=
  fun dbenv nenv => a_Dan a dbenv fenv nenv v.

Definition aparam (p: nat) (v: nat) : assertion :=
  fun dbenv nenv => nth_error dbenv p = Some v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp_Dan) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => b_Dan b dbenv fenv nenv true /\ P dbenv nenv.

Definition afalse (b: bexp_Dan) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => b_Dan b dbenv fenv nenv false /\ P dbenv nenv.

Definition aupdate (x: ident) (a: aexp_Dan) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => (forall n, a_Dan a dbenv fenv nenv n -> P dbenv (update x n nenv)). 

Inductive Dan_lp :=
  |Dan_lp_arith (l: LogicProp nat aexp_Dan)
|Dan_lp_bool (l: LogicProp bool bexp_Dan).

Inductive Dan_lp_prop_rel : (aexp_Dan -> Prop) -> (bexp_Dan -> Prop) -> Dan_lp -> Prop :=
| DanLPPropArith :
  forall (phi1: aexp_Dan -> Prop) (phi2: bexp_Dan -> Prop) (l: LogicProp nat aexp_Dan),
    prop_rel phi1 l ->
    Dan_lp_prop_rel phi1 phi2 (Dan_lp_arith l)
| DanLPPropBool :
  forall (phi1: aexp_Dan -> Prop) (phi2: bexp_Dan -> Prop) (l: LogicProp bool bexp_Dan),
    prop_rel phi2 l ->
    Dan_lp_prop_rel phi1 phi2 (Dan_lp_bool l).

Inductive AbsEnv: Type :=
| AbsEnvLP (s: Dan_lp)
| AbsEnvAnd (s1 s2: AbsEnv)
| AbsEnvOr (s1 s2: AbsEnv).

Inductive AbsEnv_prop_rel : (aexp_Dan -> Prop) -> (bexp_Dan -> Prop) -> AbsEnv -> Prop :=
| DanLogPropRelLP :
  forall (phi1: aexp_Dan -> Prop) (phi2: bexp_Dan -> Prop) (l: Dan_lp),
    Dan_lp_prop_rel phi1 phi2 l ->
    AbsEnv_prop_rel phi1 phi2 (AbsEnvLP l)
| DanLogPropRelAnd :
  forall (phi1: aexp_Dan -> Prop) (phi2: bexp_Dan -> Prop) (l1 l2: AbsEnv),
    AbsEnv_prop_rel phi1 phi2 l1 ->
    AbsEnv_prop_rel phi1 phi2 l2 ->
    AbsEnv_prop_rel phi1 phi2 (AbsEnvAnd l1 l2)
| DanLogPropRelOr :
  forall (phi1: aexp_Dan -> Prop) (phi2: bexp_Dan -> Prop) (l1 l2: AbsEnv),
    AbsEnv_prop_rel phi1 phi2 l1 ->
    AbsEnv_prop_rel phi1 phi2 l2 ->
    AbsEnv_prop_rel phi1 phi2 (AbsEnvOr l1 l2).

Inductive Dan_lp_rel: Dan_lp -> fun_env -> list nat -> nat_env -> Prop :=
| Dan_lp_rel_bool :
  forall l fenv nenv dbenv,
  eval_prop_rel (fun b v => b_Dan b dbenv fenv nenv v) l ->
  Dan_lp_rel (Dan_lp_bool l) fenv dbenv nenv
| Dan_lp_rel_arith : 
  forall l fenv nenv dbenv,
    eval_prop_rel (fun a v => a_Dan a dbenv fenv nenv v) l ->
    Dan_lp_rel (Dan_lp_arith l) fenv dbenv nenv. 

Inductive AbsEnv_rel: AbsEnv -> fun_env -> list nat -> nat_env -> Prop :=
| AbsEnv_leaf : 
  forall l fenv dbenv nenv, 
  Dan_lp_rel l fenv dbenv nenv -> 
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

