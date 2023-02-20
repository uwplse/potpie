From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangEval DanTrick.LogicProp.
(* DanTrick.StackLogicBase DanTrick.StackPure. *)

(* A stronger version of pure -- this stipulates that not only is the stack not changed
   by functions, but it doesn't actually _need_ any indices outside of a given frame *)

Inductive aexp_frame_rule : aexp_stack -> fun_env_stk -> nat -> Prop :=
| FrameConst :
  forall fenv frame n,
    aexp_frame_rule (Const_Stk n) fenv frame
| FrameVar :
  forall fenv frame k,
    1 <= k ->
    k <= frame ->
    aexp_frame_rule (Var_Stk k) fenv frame
| FramePlus :
  forall fenv frame a1 a2,
    aexp_frame_rule a1 fenv frame ->
    aexp_frame_rule a2 fenv frame ->
    aexp_frame_rule (Plus_Stk a1 a2) fenv frame
| FrameMinus :
  forall fenv frame a1 a2,
    aexp_frame_rule a1 fenv frame ->
    aexp_frame_rule a2 fenv frame ->
    aexp_frame_rule (Minus_Stk a1 a2) fenv frame
| FrameApp :
  forall fenv frame f args func,
    args_frame_rule args fenv frame ->
    func = fenv f ->
    imp_frame_rule (Body func) fenv (Args func) (Args func + Return_pop func) ->
    aexp_frame_rule (Return_expr func) fenv (Args func + Return_pop func) ->
    aexp_frame_rule (App_Stk f args) fenv frame
with args_frame_rule : list aexp_stack -> fun_env_stk -> nat -> Prop :=
| FrameArgsNil :
  forall fenv frame,
    args_frame_rule nil fenv frame
| FrameArgsCons :
  forall fenv frame arg args,
    aexp_frame_rule arg fenv frame ->
    args_frame_rule args fenv frame ->
    args_frame_rule (arg :: args) fenv frame
with bexp_frame_rule : bexp_stack -> fun_env_stk -> nat -> Prop :=
| FrameTrue :
  forall fenv frame,
    bexp_frame_rule True_Stk fenv frame
| FrameFalse :
  forall fenv frame,
    bexp_frame_rule False_Stk fenv frame
| FrameNeg :
  forall fenv frame b,
    bexp_frame_rule b fenv frame ->
    bexp_frame_rule (Neg_Stk b) fenv frame
| FrameAnd :
  forall fenv frame b1 b2,
    bexp_frame_rule b1 fenv frame ->
    bexp_frame_rule b2 fenv frame ->
    bexp_frame_rule (And_Stk b1 b2) fenv frame
| FrameOr :
  forall fenv frame b1 b2,
    bexp_frame_rule b1 fenv frame ->
    bexp_frame_rule b2 fenv frame ->
    bexp_frame_rule (Or_Stk b1 b2) fenv frame
| FrameLeq :
  forall fenv frame a1 a2,
    aexp_frame_rule a1 fenv frame ->
    aexp_frame_rule a2 fenv frame ->
    bexp_frame_rule (Leq_Stk a1 a2) fenv frame
| FrameEq :
  forall fenv frame a1 a2,
    aexp_frame_rule a1 fenv frame ->
    aexp_frame_rule a2 fenv frame ->
    bexp_frame_rule (Eq_Stk a1 a2) fenv frame
with imp_frame_rule : imp_stack -> fun_env_stk -> nat -> nat -> Prop :=
| FrameSkip :
  forall fenv frame,
    imp_frame_rule Skip_Stk fenv frame frame
| FrameAssign :
  forall fenv frame k a,
    1 <= k ->
    k <= frame ->
    aexp_frame_rule a fenv frame ->
    imp_frame_rule (Assign_Stk k a) fenv frame frame
| FramePush :
  forall fenv frame,
    imp_frame_rule Push_Stk fenv frame (frame + 1)
| FramePop :
  forall fenv frame,
    frame >= 1 ->
    imp_frame_rule Pop_Stk fenv frame (frame - 1)
| FrameSeq :
  forall fenv frame i1 i2 frame' frame'',
    imp_frame_rule i1 fenv frame frame' ->
    imp_frame_rule i2 fenv frame' frame'' ->
    imp_frame_rule (Seq_Stk i1 i2) fenv frame frame''
| FrameIf :
  forall fenv frame b i1 i2 frame',
    bexp_frame_rule b fenv frame ->
    imp_frame_rule i1 fenv frame frame' ->
    imp_frame_rule i2 fenv frame frame' ->
    imp_frame_rule (If_Stk b i1 i2) fenv frame frame'
| FrameWhile :
  forall fenv frame b loop_body,
    bexp_frame_rule b fenv frame ->
    imp_frame_rule loop_body fenv frame frame ->
    imp_frame_rule (While_Stk b loop_body) fenv frame frame.

Scheme aexp_frame_rule_ind' := Induction for aexp_frame_rule Sort Prop
    with args_frame_rule_ind' := Induction for args_frame_rule Sort Prop
    with bexp_frame_rule_ind' := Induction for bexp_frame_rule Sort Prop
with imp_frame_rule_ind' := Induction for imp_frame_rule Sort Prop.

Combined Scheme stack_frame_rule_mut_ind from aexp_frame_rule_ind', args_frame_rule_ind', bexp_frame_rule_ind', imp_frame_rule_ind'.
