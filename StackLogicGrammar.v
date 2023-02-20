From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangEval DanTrick.LogicProp DanTrick.StackPurestBase.

Scheme Equality for list.

Definition assertion: Type := stack -> Prop.

Inductive AbsStack: Type :=
| AbsStkTrue
| AbsStkSize (gt: nat).

Definition StkBoolProp: Type := LogicProp bool bexp_stack.
Definition StkNatProp: Type := LogicProp nat aexp_stack.

Inductive MetavarPred: Type :=
| MetaBool (l: LogicProp bool bexp_stack)
| MetaNat (l: LogicProp nat aexp_stack).

Inductive AbsState: Type :=
| BaseState (s: AbsStack) (m: MetavarPred)
| AbsAnd (s1 s2: AbsState)
| AbsOr (s1 s2: AbsState).


Fixpoint list_of_options_to_option_list {A} (xs: list (option A)) (acc: option (list A)): (option (list A)) :=
  match xs with
  | x :: xs' =>
      match (x, acc) with
      | (Some xa, Some acc') =>
          list_of_options_to_option_list xs' (Some (xa :: acc'))
        | _ => None
      end
  | nil => match acc with
          | Some acc' => Some (rev acc')
          | None => None
          end
  end.

Inductive absstack_match_rel: AbsStack -> stack -> Prop :=
| RelAbsStkTrue :
  forall stk,
    absstack_match_rel AbsStkTrue stk
| RelAbsStkSize :
  forall geq_num stk,
    List.length stk >= geq_num ->
    absstack_match_rel (AbsStkSize geq_num) stk.
Inductive meta_match_rel: MetavarPred -> fun_env_stk -> stack -> Prop :=
| RelMetaBool :
  forall fenv stk l,
    eval_prop_rel (fun boolexpr boolval => bexp_stack_sem boolexpr fenv stk (stk, boolval)) l ->
    prop_rel (fun boolexpr => bexp_stack_pure_rel boolexpr fenv) l ->
    meta_match_rel (MetaBool l) fenv stk
| RelMetaNat :
  forall fenv stk l,
    eval_prop_rel (fun natexpr natval => aexp_stack_sem natexpr fenv stk (stk, natval)) l ->
    prop_rel (fun natexpr => aexp_stack_pure_rel natexpr fenv) l ->
    meta_match_rel (MetaNat l) fenv stk.


Inductive absstate_match_rel: AbsState -> fun_env_stk -> stack -> Prop :=
| RelBaseState :
  forall s m fenv stk,
    absstack_match_rel s stk ->
    meta_match_rel m fenv stk ->
    absstate_match_rel (BaseState s m) fenv stk
| RelAbsAnd :
  forall fenv stk s1 s2,
    absstate_match_rel s1 fenv stk ->
    absstate_match_rel s2 fenv stk ->
    absstate_match_rel (AbsAnd s1 s2) fenv stk
| RelAbsOrLeft :
  forall fenv stk s1 s2,
    absstate_match_rel s1 fenv stk ->
    absstate_match_rel (AbsOr s1 s2) fenv stk
| RelAbsOrRight :
  forall fenv stk s1 s2,
    absstate_match_rel s2 fenv stk ->
    absstate_match_rel (AbsOr s1 s2) fenv stk.

                                          
Definition silly: assertion := (absstate_match_rel (BaseState (AbsStkTrue)
                                     (MetaNat (BinaryProp nat aexp_stack
                                                          (fun n1 n2 => n1 = n2)
                                                          (Const_Stk 3)
                                                          (Const_Stk 1))))
                                                   init_fenv_stk).

Check silly.

Lemma silly_theorem :
  forall stk,
    ~ (silly stk).
Proof.
  intros.
  unfold not. intros.
  unfold silly in H.
  inversion H.
  subst.
  inversion H5.
  subst.
  inversion H1.
  subst.
  inversion H8.
  subst.
  inversion H9.
Qed.

Definition aexp_unary_rel: Type := aexp_stack -> Prop.

Definition bexp_unary_rel: Type := bexp_stack -> Prop.

Definition aexp_binary_rel: Type := aexp_stack -> aexp_stack -> Prop.

Definition bexp_binary_rel: Type := bexp_stack -> bexp_stack -> Prop.

Definition nat_prop_rel (f: aexp_unary_rel): StkNatProp -> Prop :=
  prop_rel (V := nat) f.

Definition bool_prop_rel (f: bexp_unary_rel): StkBoolProp -> Prop :=
  prop_rel (V := bool) f.

Definition nat_prop_args_rel (f: aexp_unary_rel): (list aexp_stack) -> Prop :=
  prop_args_rel (V := nat) f.

Definition bool_prop_args_rel (f: bexp_unary_rel): (list bexp_stack) -> Prop :=
  prop_args_rel (V := bool) f.

Definition nat_binary_prop_rel (f: aexp_binary_rel): StkNatProp -> StkNatProp -> Prop :=
  transformed_prop_exprs (V := nat) f.

Definition bool_binary_prop_rel (f: bexp_binary_rel): StkBoolProp -> StkBoolProp -> Prop :=
  transformed_prop_exprs (V := bool) f.

Definition nat_prop_args_binary_rel (f: aexp_binary_rel): (list aexp_stack) -> (list aexp_stack) -> Prop :=
  transformed_prop_exprs_args (V := nat) f.

Definition bool_prop_args_binary_rel (f: bexp_binary_rel): (list bexp_stack) -> (list bexp_stack) -> Prop :=
  transformed_prop_exprs_args (V := bool) f.

Ltac unfold_prop_helpers :=
  unfold nat_prop_rel, bool_prop_rel, nat_prop_args_rel, bool_prop_args_rel, nat_binary_prop_rel, bool_binary_prop_rel, nat_prop_args_binary_rel, bool_prop_args_binary_rel.
                                                                                                  
