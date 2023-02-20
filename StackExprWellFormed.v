From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage.
Require Import DanTrick.LogicProp.
Require Import DanTrick.StackLogicGrammar.

Inductive aexp_well_formed : aexp_stack -> Prop :=
| WFConst :
  forall n,
    aexp_well_formed (Const_Stk n)
| WFVar :
  forall k,
    1 <= k ->
    aexp_well_formed (Var_Stk k)
| WFPlus :
  forall a1 a2,
    aexp_well_formed a1 ->
    aexp_well_formed a2 ->
    aexp_well_formed (Plus_Stk a1 a2)
| WFMinus :
  forall a1 a2,
    aexp_well_formed a1 ->
    aexp_well_formed a2 ->
    aexp_well_formed (Minus_Stk a1 a2)
| WFApp :
  forall f args,
    args_well_formed args ->
    aexp_well_formed (App_Stk f args)
with args_well_formed : list aexp_stack -> Prop :=
| WFArgsNil :
  args_well_formed nil
| WFArgsCons :
  forall arg args,
    aexp_well_formed arg ->
    args_well_formed args ->
    args_well_formed (arg :: args).

Scheme aexp_wf_ind := Induction for aexp_well_formed Sort Prop
    with args_wf_ind := Induction for args_well_formed Sort Prop.

Combined Scheme aexp_args_wf_mut_ind from aexp_wf_ind, args_wf_ind.

Local Definition mut_ind_P: Type := forall (a: aexp_stack), aexp_well_formed a -> Prop.
Local Definition mut_ind_P0: Type := forall (l: list aexp_stack), args_well_formed l -> Prop.
Local Definition mut_ind_P': Type := aexp_stack -> Prop.
Local Definition mut_ind_P0': Type := list aexp_stack -> Prop.

Definition aexp_args_wf_mut_ind_theorem_P (P: aexp_stack -> Prop): mut_ind_P :=
  fun a: aexp_stack =>
  fun _: aexp_well_formed a =>
    P a.

Definition aexp_args_wf_mut_ind_theorem_P0 (P0: list aexp_stack -> Prop): mut_ind_P0 :=
  fun l: list aexp_stack =>
  fun _: args_well_formed l =>
    P0 l.

Definition aexp_args_wf_mut_ind_theorem (P: mut_ind_P') (P0: mut_ind_P0'): Prop :=
  (forall (a: aexp_stack),
    aexp_well_formed a -> P a) /\
    forall (l: list aexp_stack),
      args_well_formed l -> P0 l.

Ltac aexp_args_wf_mutual_induction P P0 P_def P0_def :=
  pose proof (aexp_args_wf_mut_ind_theorem_P P_def) as P;
  pose proof (aexp_args_wf_mut_ind_theorem_P0 P0_def) as P0;
  apply (aexp_args_wf_mut_ind P P0);
  unfold P, P0;
  unfold aexp_args_wf_mut_ind_theorem, aexp_args_wf_mut_ind_theorem_P, aexp_args_wf_mut_ind_theorem_P0;
  unfold P_def, P0_def.

Inductive bexp_well_formed : bexp_stack -> Prop :=
| WFTrue :
  bexp_well_formed True_Stk
| WFFalse :
  bexp_well_formed False_Stk
| WFNeg :
  forall b,
    bexp_well_formed b ->
    bexp_well_formed (Neg_Stk b)
| WFAnd :
  forall b1 b2,
    bexp_well_formed b1 ->
    bexp_well_formed b2 ->
    bexp_well_formed (And_Stk b1 b2)
| WFOr :
  forall b1 b2,
    bexp_well_formed b1 ->
    bexp_well_formed b2 ->
    bexp_well_formed (Or_Stk b1 b2)
| WFLeq :
  forall a1 a2,
    aexp_well_formed a1 ->
    aexp_well_formed a2 ->
    bexp_well_formed (Leq_Stk a1 a2)
| WFEq :
  forall a1 a2,
    aexp_well_formed a1 ->
    aexp_well_formed a2 ->
    bexp_well_formed (Eq_Stk a1 a2).

Inductive lp_aexp_well_formed : LogicProp nat aexp_stack -> Prop :=
| WFTrueProp:
   lp_aexp_well_formed (TrueProp _ _)
| WFLFalseProp:
   lp_aexp_well_formed (FalseProp _ _)
| WFUnaryProp :
   forall f a,
     aexp_well_formed a ->
     lp_aexp_well_formed (UnaryProp _ _ f a)
| WFBinaryProp :
    forall f a1 a2,
      aexp_well_formed a1 ->
      aexp_well_formed a2 ->
      lp_aexp_well_formed (BinaryProp _ _ f a1 a2)
| WFAndProp :
    forall l1 l2,
      lp_aexp_well_formed l1 ->
      lp_aexp_well_formed l2 ->
      lp_aexp_well_formed (AndProp _ _ l1 l2)
| WFOrProp :
    forall l1 l2,
      lp_aexp_well_formed l1 ->
      lp_aexp_well_formed l2 ->
      lp_aexp_well_formed (OrProp _ _ l1 l2)
| WFTernaryProp :
    forall f a1 a2 a3,
      aexp_well_formed a1 ->
      aexp_well_formed a2 ->
      aexp_well_formed a3 ->
      lp_aexp_well_formed (TernaryProp _ _ f a1 a2 a3)
| WFNaryPropNil :
    forall f,
      lp_aexp_well_formed (NaryProp _ _ f nil)
| WFNaryPropCons :
    forall f a la,
      aexp_well_formed a ->
      lp_aexp_well_formed (NaryProp _ _ f la) ->
      lp_aexp_well_formed (NaryProp _ _ f (a :: la)).

Inductive lp_bexp_well_formed : LogicProp bool bexp_stack -> Prop :=
| WFTruePropB:
   lp_bexp_well_formed (TrueProp _ _)
| WFLFalsePropB:
   lp_bexp_well_formed (FalseProp _ _)
| WFUnaryPropB :
   forall f b,
     bexp_well_formed b ->
     lp_bexp_well_formed (UnaryProp _ _ f b)
| WFBinaryPropB :
    forall f b1 b2,
      bexp_well_formed b1 ->
      bexp_well_formed b2 ->
      lp_bexp_well_formed (BinaryProp _ _ f b1 b2)
| WFAndPropB :
    forall l1 l2,
      lp_bexp_well_formed l1 ->
      lp_bexp_well_formed l2 ->
      lp_bexp_well_formed (AndProp _ _ l1 l2)
| WFOrPropB :
    forall l1 l2,
      lp_bexp_well_formed l1 ->
      lp_bexp_well_formed l2 ->
      lp_bexp_well_formed (OrProp _ _ l1 l2)
| WFTernaryPropB :
    forall f b1 b2 b3,
      bexp_well_formed b1 ->
      bexp_well_formed b2 ->
      bexp_well_formed b3 ->
      lp_bexp_well_formed (TernaryProp _ _ f b1 b2 b3)
| WFNaryPropNilB :
    forall f,
      lp_bexp_well_formed (NaryProp _ _ f nil)
| WFNaryPropConsB :
    forall f b lb,
      bexp_well_formed b ->
      lp_bexp_well_formed (NaryProp _ _ f lb) ->
      lp_bexp_well_formed (NaryProp _ _ f (b :: lb)).


Inductive mv_well_formed : MetavarPred -> Prop :=
| WFMetaBool : 
    forall l, prop_rel bexp_well_formed l -> mv_well_formed (MetaBool l)
| WFMetaNat :
    forall l, prop_rel aexp_well_formed l -> mv_well_formed (MetaNat l).


Inductive absstate_well_formed : AbsState -> Prop :=
| WFBaseState :
    forall a mv,
      mv_well_formed mv ->
      absstate_well_formed (BaseState a mv)
| WFAbsAnd :
    forall a1 a2, 
      absstate_well_formed a1 -> 
      absstate_well_formed a2 ->
      absstate_well_formed (AbsAnd a1 a2)
| WFAbsOr:
    forall a1 a2,
      absstate_well_formed a1 ->
      absstate_well_formed a2 ->
      absstate_well_formed (AbsOr a1 a2).
