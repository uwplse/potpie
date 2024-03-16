From Coq Require Import Arith Bool Nat String.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.


From Imp_LangTrick Require Import MyOptionUtils.
From Imp_LangTrick Require Import StackExprWellFormed StackLanguage StackPurestBase StackFrame StackFrameReflection ReflectionMachinery.

Definition option_apply' {A B: Type} (f: option (A -> B)) (a: option A): option B :=
  match f with
  | Some f' =>
      option_map f' a
  | None => None
  end.


Fixpoint construct_aexp_stack_pure_rel (fenv: fun_env_stk) (a: aexp_stack) {struct a} : option (aexp_stack_pure_rel a fenv) :=
  let caspr := construct_aexp_stack_pure_rel fenv in
  match a with
  | Const_Stk n => Some (PureConstStk fenv n)
  | Var_Stk k => option_map (fun H => PureVarStk fenv k H) (construct_1_le_k k)
  | Plus_Stk a1 a2 =>
      option_map_map (PurePlusStk fenv a1 a2)
                     (construct_aexp_stack_pure_rel fenv a1)
                     (construct_aexp_stack_pure_rel fenv a2)
  | Minus_Stk a1 a2 =>
      option_map_map (PureMinusStk fenv a1 a2)
                     (construct_aexp_stack_pure_rel fenv a1)
                     (construct_aexp_stack_pure_rel fenv a2)
  | App_Stk f args =>
      let func := fenv f in
      match
        ((fix inner (args: list aexp_stack) :=
            match args with
            | nil => Some (PureArgsNil fenv)
            | arg :: args' =>
                option_map_map (PureArgsCons fenv arg args')
                               (construct_aexp_stack_pure_rel fenv arg)
                               (inner args')
            end)
            args),
        construct_imp_frame_rule (Body func) fenv (Args func) ((Return_pop func) + (Args func)) 1000,
        construct_aexp_frame_rule (Return_expr func) fenv ((Return_pop func) + (Args func)) 1000 with
      | Some Hargs, Some Hbody, Some Hret =>
          
          Some (PureAppStk fenv func f args
                           eq_refl
                           Hargs
                           Hbody
                           Hret
                           (StackPurestBase.aexp_frame_implies_aexp_pure
                              (Return_expr func) fenv ((Return_pop func) + (Args func)) Hret))
      | _, _, _ => None
      end
  end.

Fixpoint construct_bexp_stack_pure_rel (fenv: fun_env_stk) (b: bexp_stack): option (bexp_stack_pure_rel b fenv) :=
  let cbspr := construct_bexp_stack_pure_rel fenv in
  match b with
  | True_Stk => Some (PureTrueStk fenv)
  | False_Stk => Some (PureFalseStk fenv)
  | Neg_Stk b' =>
      option_map (fun H => PureNegStk fenv b' H) (cbspr b')
  | And_Stk b1 b2 =>
      option_map_map (PureAndStk fenv b1 b2)
                     (cbspr b1)
                     (cbspr b2)
  | Or_Stk b1 b2 =>
      option_map_map (PureOrStk fenv b1 b2)
                     (cbspr b1)
                     (cbspr b2)
  | Leq_Stk a1 a2 =>
      option_map_map (PureLeqStk fenv a1 a2)
                     (construct_aexp_stack_pure_rel fenv a1)
                     (construct_aexp_stack_pure_rel fenv a2)
  | Eq_Stk a1 a2 =>
      option_map_map (PureEqStk fenv a1 a2)
                     (construct_aexp_stack_pure_rel fenv a1)
                     (construct_aexp_stack_pure_rel fenv a2)
  end.


Ltac prove_exp_stack_pure_rel :=
  match goal with
  | [ |- aexp_stack_pure_rel ?a ?fenv] =>
      exact (optionOut (aexp_stack_pure_rel a fenv) (construct_aexp_stack_pure_rel fenv a))
  | [ |- bexp_stack_pure_rel ?b ?fenv] =>
      exact (optionOut (bexp_stack_pure_rel b fenv) (construct_bexp_stack_pure_rel fenv b))
  end.
