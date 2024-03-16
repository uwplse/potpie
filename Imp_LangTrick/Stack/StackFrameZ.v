From Coq Require Import Arith Psatz Bool String List Nat Program.Equality ZArith.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import Imp_LangTrick.Stack.StackLanguage Imp_LangTrick.LogicProp.LogicProp.

(* A stronger version of pure -- this stipulates that not only is the stack not changed
   by functions, but it doesn't actually _need_ any indices outside of a given frame,
   and uses Z for the frame instead *)

Inductive aexp_frame_z_rule : aexp_stack -> fun_env_stk -> Z -> Prop :=
| ZFrameConst :
  forall fenv zframe n,
    0 <= zframe ->
    aexp_frame_z_rule (Const_Stk n) fenv zframe
| ZFrameVar :
  forall fenv zframe k,
    (1 <= k)%nat ->
    Z.of_nat k <= zframe ->
    aexp_frame_z_rule (Var_Stk k) fenv zframe
| ZFramePlus :
  forall fenv zframe a1 a2,
    0 <= zframe ->
    aexp_frame_z_rule a1 fenv zframe ->
    aexp_frame_z_rule a2 fenv zframe ->
    aexp_frame_z_rule (Plus_Stk a1 a2) fenv zframe
| ZFrameMinus :
  forall fenv zframe a1 a2,
    0 <= zframe ->
    aexp_frame_z_rule a1 fenv zframe ->
    aexp_frame_z_rule a2 fenv zframe ->
    aexp_frame_z_rule (Minus_Stk a1 a2) fenv zframe
| ZFrameApp :
  forall fenv zframe f args func,
    0 <= zframe ->
    args_frame_z_rule args fenv zframe ->
    func = fenv f ->
    imp_frame_z_rule (Body func) fenv (Z.of_nat (Args func)) (Z.of_nat(Args func + Return_pop func)) ->
    aexp_frame_z_rule (Return_expr func) fenv (Z.of_nat (Args func + Return_pop func)) ->
    aexp_frame_z_rule (App_Stk f args) fenv zframe
with args_frame_z_rule : list aexp_stack -> fun_env_stk -> Z -> Prop :=
| ZFrameArgsNil :
  forall fenv zframe,
    0 <= zframe ->
    args_frame_z_rule nil fenv zframe
| ZFrameArgsCons :
  forall fenv zframe arg args,
    0 <= zframe ->
    aexp_frame_z_rule arg fenv zframe ->
    args_frame_z_rule args fenv zframe ->
    args_frame_z_rule (arg :: args) fenv zframe
with bexp_frame_z_rule : bexp_stack -> fun_env_stk -> Z -> Prop :=
| ZFrameTrue :
  forall fenv zframe,
    0 <= zframe ->
    bexp_frame_z_rule True_Stk fenv zframe
| ZFrameFalse :
  forall fenv zframe,
    0 <= zframe ->
    bexp_frame_z_rule False_Stk fenv zframe
| ZFrameNeg :
  forall fenv zframe b,
    0 <= zframe ->
    bexp_frame_z_rule b fenv zframe ->
    bexp_frame_z_rule (Neg_Stk b) fenv zframe
| ZFrameAnd :
  forall fenv zframe b1 b2,
    0 <= zframe ->
    bexp_frame_z_rule b1 fenv zframe ->
    bexp_frame_z_rule b2 fenv zframe ->
    bexp_frame_z_rule (And_Stk b1 b2) fenv zframe
| ZFrameOr :
  forall fenv zframe b1 b2,
    0 <= zframe ->
    bexp_frame_z_rule b1 fenv zframe ->
    bexp_frame_z_rule b2 fenv zframe ->
    bexp_frame_z_rule (Or_Stk b1 b2) fenv zframe
| ZFrameLeq :
  forall fenv zframe a1 a2,
    0 <= zframe ->
    aexp_frame_z_rule a1 fenv zframe ->
    aexp_frame_z_rule a2 fenv zframe ->
    bexp_frame_z_rule (Leq_Stk a1 a2) fenv zframe
| ZFrameEq :
  forall fenv zframe a1 a2,
    0 <= zframe ->
    aexp_frame_z_rule a1 fenv zframe ->
    aexp_frame_z_rule a2 fenv zframe ->
    bexp_frame_z_rule (Eq_Stk a1 a2) fenv zframe
with imp_frame_z_rule : imp_stack -> fun_env_stk -> Z -> Z -> Prop :=
| ZFrameSkip :
  forall fenv zframe,
    0 <= zframe ->
    imp_frame_z_rule Skip_Stk fenv zframe zframe
| ZFrameAssign :
  forall fenv zframe k a,
    (1 <= k)%nat ->
    Z.of_nat k <= zframe ->
    aexp_frame_z_rule a fenv zframe ->
    imp_frame_z_rule (Assign_Stk k a) fenv zframe zframe
| ZFramePush :
  forall fenv zframe,
    0 <= zframe ->
    imp_frame_z_rule Push_Stk fenv zframe (zframe + 1)
| ZFramePop :
  forall fenv zframe,
    zframe >= 1 ->
    imp_frame_z_rule Pop_Stk fenv zframe (zframe - 1)
| ZFrameSeq :
  forall fenv zframe i1 i2 zframe' zframe'',
    0 <= zframe ->
    0 <= zframe' ->
    0 <= zframe'' ->
    imp_frame_z_rule i1 fenv zframe zframe' ->
    imp_frame_z_rule i2 fenv zframe' zframe'' ->
    imp_frame_z_rule (Seq_Stk i1 i2) fenv zframe zframe''
| ZFrameIf :
  forall fenv zframe b i1 i2 zframe',
    0 <= zframe ->
    0 <= zframe' ->
    bexp_frame_z_rule b fenv zframe ->
    imp_frame_z_rule i1 fenv zframe zframe' ->
    imp_frame_z_rule i2 fenv zframe zframe' ->
    imp_frame_z_rule (If_Stk b i1 i2) fenv zframe zframe'
| ZFrameWhile :
  forall fenv zframe b loop_body,
    0 <= zframe ->
    bexp_frame_z_rule b fenv zframe ->
    imp_frame_z_rule loop_body fenv zframe zframe ->
    imp_frame_z_rule (While_Stk b loop_body) fenv zframe zframe.

Scheme aexp_frame_z_rule_ind' := Induction for aexp_frame_z_rule Sort Prop
    with args_frame_z_rule_ind' := Induction for args_frame_z_rule Sort Prop
    with bexp_frame_z_rule_ind' := Induction for bexp_frame_z_rule Sort Prop
with imp_frame_z_rule_ind' := Induction for imp_frame_z_rule Sort Prop.

Combined Scheme stack_frame_z_rule_mut_ind from aexp_frame_z_rule_ind', args_frame_z_rule_ind', bexp_frame_z_rule_ind', imp_frame_z_rule_ind'.



Definition frame_z_rule_mut_ind_theorem (P: aexp_stack -> fun_env_stk -> Z -> Prop) (P0: list aexp_stack -> fun_env_stk -> Z -> Prop) (P1: bexp_stack -> fun_env_stk -> Z -> Prop) (P2: imp_stack -> fun_env_stk -> Z -> Z -> Prop): Prop :=
  (forall (a : aexp_stack) (fenv : fun_env_stk) (zframe : Z),
      aexp_frame_z_rule a fenv zframe ->
      P a fenv zframe) /\
    (forall (args: list aexp_stack) (fenv: fun_env_stk) (zframe: Z),
        args_frame_z_rule args fenv zframe ->
        P0 args fenv zframe) /\
    (forall (b: bexp_stack) (fenv: fun_env_stk) (zframe: Z),
        bexp_frame_z_rule b fenv zframe ->
        P1 b fenv zframe) /\
    (forall (i: imp_stack) (fenv: fun_env_stk) (zframe zframe': Z),
        imp_frame_z_rule i fenv zframe zframe' ->
        P2 i fenv zframe zframe').

Definition frame_z_rule_mut_ind_theorem_P (P: aexp_stack -> fun_env_stk -> Z -> Prop): forall (a: aexp_stack) (f20: fun_env_stk) (n: Z), aexp_frame_z_rule a f20 n -> Prop :=
    fun (a: aexp_stack) (fenv: fun_env_stk) (zframe: Z) =>
    fun (_: aexp_frame_z_rule a fenv zframe) =>
      P a fenv zframe.
                                                                                 
Definition frame_z_rule_mut_ind_theorem_P0 (P0: list aexp_stack -> fun_env_stk -> Z -> Prop): forall (l: list aexp_stack) (f20: fun_env_stk) (n: Z), args_frame_z_rule l f20 n -> Prop :=
  fun (args: list aexp_stack) (fenv: fun_env_stk) (zframe: Z) =>
  fun (_: args_frame_z_rule args fenv zframe) =>
    P0 args fenv zframe.
Definition frame_z_rule_mut_ind_theorem_P1 (P1: bexp_stack -> fun_env_stk -> Z -> Prop): forall (b: bexp_stack) (f20: fun_env_stk) (n: Z), bexp_frame_z_rule b f20 n -> Prop :=
  fun (b: bexp_stack) (fenv: fun_env_stk) (zframe: Z) =>
  fun (_: bexp_frame_z_rule b fenv zframe) =>
    P1 b fenv zframe.

Definition frame_z_rule_mut_ind_theorem_P2 (P2: imp_stack -> fun_env_stk -> Z -> Z -> Prop): forall (i: imp_stack) (f20: fun_env_stk) (n n0: Z), imp_frame_z_rule i f20 n n0 -> Prop :=
  fun (i: imp_stack) (fenv: fun_env_stk) (zframe zframe': Z) =>
  fun (_: imp_frame_z_rule i fenv zframe zframe') =>
    P2 i fenv zframe zframe'.

Ltac frame_z_rule_mutual_induction P P0 P1 P2 P_def P0_def P1_def P2_def :=
  pose (frame_z_rule_mut_ind_theorem_P P_def) as P;
  pose (frame_z_rule_mut_ind_theorem_P0 P0_def) as P0;
  pose (frame_z_rule_mut_ind_theorem_P1 P1_def) as P1;
  pose (frame_z_rule_mut_ind_theorem_P2 P2_def) as P2;
  apply (stack_frame_z_rule_mut_ind P P0 P1 P2);
  unfold P, P0, P1, P2;
  unfold frame_z_rule_mut_ind_theorem_P, frame_z_rule_mut_ind_theorem_P0, frame_z_rule_mut_ind_theorem_P1, frame_z_rule_mut_ind_theorem_P2;
  unfold P_def, P0_def, P1_def, P2_def.
