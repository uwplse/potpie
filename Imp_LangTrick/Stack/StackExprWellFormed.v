From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick Require Import StackLanguage LogicProp StackLogicGrammar.
From Imp_LangTrick Require Import ReflectionMachinery.


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

Fixpoint construct_1_le_k (k: nat): option (1 <= k) :=
  match k as k' return option (1 <= k') with
  | 0 => None
  | S k'' =>
      match k'' as k4 return option(1 <= S k4) with
      | 0 =>
          Some (le_n (S 0))
      | S k''' =>
          match construct_1_le_k k''' with
          | Some P =>
              (* Have to re-wrap with S twice to make type checker happy *)
              Some (le_S 1 (S k''') (le_S 1 k''' P))
          | None =>
              (* k''' must have been 0 *)
              match k''' as k5 return option (1 <= S (S k5)) with
              | 0 => Some (le_S 1 1 (le_n (S 0)))
              | _ => None
              end
          end
      end
  end.
  

Fixpoint construct_aexp_well_formed (a: aexp_stack): option(aexp_well_formed a) :=
  match a as a' return (option (aexp_well_formed a')) with
  | Const_Stk n =>
      Some (WFConst n)
  | Var_Stk k =>
      match construct_1_le_k k with
      | Some P =>
          Some (WFVar k P)
      | None => None
      end
  | Plus_Stk a1 a2 =>
      match construct_aexp_well_formed a1 with
      | Some P1 =>
          match construct_aexp_well_formed a2 with
          | Some P2 =>
              Some (WFPlus a1 a2 P1 P2)
          | None => None
          end
      | None => None
      end
  | Minus_Stk a1 a2 =>
      match construct_aexp_well_formed a1 with
      | Some P1 =>
          match construct_aexp_well_formed a2 with
          | Some P2 =>
              Some (WFMinus a1 a2 P1 P2)
          | None => None
          end
      | None => None
      end
  | App_Stk f args =>
      match ((fix construct_args_well_formed (args: list aexp_stack): option (args_well_formed args) :=
               match args with
               | nil =>
                   Some (WFArgsNil)
               | arg :: args' =>
                   match construct_aexp_well_formed arg, construct_args_well_formed args' with
                   | Some Parg, Some Pargs' =>
                       Some (WFArgsCons arg args' Parg Pargs')
                   | _, _ => None
                   end
               end) args) with
      | Some Pargs =>
          Some (WFApp f args Pargs)
      | None => None
      end
  end.
           

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

Fixpoint construct_bexp_well_formed (b: bexp_stack): option (bexp_well_formed b) :=
  match b as b' return option (bexp_well_formed b') with
  | True_Stk =>
      Some WFTrue
  | False_Stk =>
      Some WFFalse
  | Neg_Stk b1 =>
      match construct_bexp_well_formed b1 with
      | Some P =>
          Some (WFNeg b1 P)
      | None => None
      end
  | And_Stk b1 b2 =>
      match construct_bexp_well_formed b1, construct_bexp_well_formed b2 with
      | Some P1, Some P2 =>
          Some (WFAnd b1 b2 P1 P2)
      | _, _ => None
      end
  | Or_Stk b1 b2 =>
      match construct_bexp_well_formed b1, construct_bexp_well_formed b2 with
      | Some P1, Some P2 =>
          Some (WFOr b1 b2 P1 P2)
      | _, _ => None
      end
  | Leq_Stk a1 a2 =>
      match construct_aexp_well_formed a1, construct_aexp_well_formed a2 with
      | Some P1, Some P2 =>
          Some (WFLeq a1 a2 P1 P2)
      | _, _ => None
      end
  | Eq_Stk a1 a2 =>
      match construct_aexp_well_formed a1, construct_aexp_well_formed a2 with
      | Some P1, Some P2 =>
          Some (WFEq a1 a2 P1 P2)
      | _, _ => None
      end
  end.

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

Definition construct_mv_well_formed (mv: MetavarPred) : option (mv_well_formed mv) :=
  match mv as mv' return option (mv_well_formed mv') with
  | MetaBool l =>
      match (construct_prop_rel bexp_well_formed l construct_bexp_well_formed) with
      | Some P =>
          Some (WFMetaBool l P)
      | None => None
      end
  | MetaNat l =>
      match (construct_prop_rel aexp_well_formed l construct_aexp_well_formed) with
      | Some P => Some (WFMetaNat l P)
      | None => None
      end
  end.
          


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

Fixpoint construct_absstate_well_formed (a: AbsState) : option (absstate_well_formed a) :=
  match a as a' return option (absstate_well_formed a') with
  | BaseState s m =>
      match construct_mv_well_formed m with
      | Some Pm => Some (WFBaseState s m Pm)
      | None => None
      end
  | AbsAnd a1 a2 =>
      match construct_absstate_well_formed a1, construct_absstate_well_formed a2 with
      | Some P1, Some P2 => Some (WFAbsAnd a1 a2 P1 P2)
      | _, _ => None
      end
  | AbsOr a1 a2 =>
      match construct_absstate_well_formed a1, construct_absstate_well_formed a2 with
      | Some P1, Some P2 => Some (WFAbsOr a1 a2 P1 P2)
      | _, _ => None
      end
  end.

Ltac prove_absstate_well_formed :=
  match goal with
  | [ |- absstate_well_formed ?a ] =>
      exact (optionOut (absstate_well_formed a) (construct_absstate_well_formed a))
  | [ |- mv_well_formed ?m ] =>
      exact (optionOut (mv_well_formed m) (construct_mv_well_formed m))
  | [ |- prop_rel bexp_well_formed ?l ] =>
      exact (optionOut (prop_rel bexp_well_formed l) (construct_prop_rel bexp_well_formed l construct_bexp_well_formed))
  | [ |- prop_rel aexp_well_formed ?l ] =>
      exact (optionOut (prop_rel aexp_well_formed l) (construct_prop_rel aexp_well_formed l construct_aexp_well_formed))
  | [ |- aexp_well_formed ?a ] =>
      exact (optionOut (aexp_well_formed a) (construct_aexp_well_formed a))
  | [ |- bexp_well_formed ?b ] =>
      exact (optionOut (bexp_well_formed b) (construct_bexp_well_formed b))
  end.
