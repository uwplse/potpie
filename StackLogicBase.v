From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangEval DanTrick.LogicProp DanTrick.StackPurestBase.
Require Export DanTrick.StackLogicGrammar DanTrick.StackIncrease DanTrick.StackLangTheorems.


Definition stk_update (k: stack_index) (a: aexp_stack) (P: assertion) (fenv: fun_env_stk): assertion :=
  fun stk =>
    forall (n: nat) stk' stk'',
      aexp_stack_sem a fenv stk (stk', n) ->
      stack_mutated_at_index stk'' k n stk' ->
      P stk''.


Fixpoint arith_update (k: stack_index) (newval: aexp_stack) (a: aexp_stack) {struct a}: aexp_stack :=
  match a with
  | Var_Stk k' =>
      if Nat.eqb k k' then newval else a
  | Plus_Stk m1 m2 =>
      Plus_Stk (arith_update k newval m1) (arith_update k newval m2)
  | Minus_Stk m1 m2 =>
      Minus_Stk (arith_update k newval m1) (arith_update k newval m2)
  | App_Stk f_id args =>
      App_Stk f_id (List.map (arith_update k newval) args)
  | _ => a
  end.


Fixpoint bool_update (k: stack_index) (newval: aexp_stack) (b: bexp_stack): bexp_stack :=
  match b with
  | Neg_Stk b' => Neg_Stk (bool_update k newval b')
  | And_Stk b1 b2 => And_Stk (bool_update k newval b1) (bool_update k newval b2)
  | Or_Stk b1 b2 => Or_Stk (bool_update k newval b1) (bool_update k newval b2)
  | Leq_Stk a1 a2 => Leq_Stk (arith_update k newval a1) (arith_update k newval a2)
  | Eq_Stk a1 a2 => Eq_Stk (arith_update k newval a1) (arith_update k newval a2)
  | _ => b
  end.


Definition meta_update (k: stack_index) (newval: aexp_stack) (P: MetavarPred): MetavarPred :=
  match P with
  | MetaBool l => MetaBool (transform_prop_exprs l (bool_update k newval))
  | MetaNat l => MetaNat (transform_prop_exprs l (arith_update k newval))
  end.

Fixpoint state_update (k: stack_index) (newval: aexp_stack) (P: AbsState): AbsState :=
  match P with
  | BaseState s m =>
      BaseState s (meta_update k newval m)
  | AbsAnd s1 s2 =>
      AbsAnd (state_update k newval s1) (state_update k newval s2)
  | AbsOr s1 s2 =>
      AbsOr (state_update k newval s1) (state_update k newval s2)
  end.



Inductive arith_update_rel: stack_index -> aexp_stack -> aexp_stack -> aexp_stack -> Prop :=
| UpConstStk :
  forall k a n,
    arith_update_rel k a (Const_Stk n) (Const_Stk n)
| UpVarStkMatch :
  forall k a k',
    k = k' ->
    arith_update_rel k a (Var_Stk k') a
| UpVarStkNoMatch :
  forall k a k',
    k <> k' ->
    arith_update_rel k a (Var_Stk k') (Var_Stk k')
| UpPlusStk :
  forall k a a1 a2 a1' a2',
    arith_update_rel k a a1 a1' ->
    arith_update_rel k a a2 a2' ->
    arith_update_rel k a (Plus_Stk a1 a2) (Plus_Stk a1' a2')
| UpMinusStk :
  forall k a a1 a2 a1' a2',
    arith_update_rel k a a1 a1' ->
    arith_update_rel k a a2 a2' ->
    arith_update_rel k a (Minus_Stk a1 a2) (Minus_Stk a1' a2')
| UpAppStk :
  forall k a f args args',
    args_update_rel k a args args' ->
    arith_update_rel k a (App_Stk f args) (App_Stk f args')
with args_update_rel: stack_index -> aexp_stack -> (list aexp_stack) -> (list aexp_stack) -> Prop :=
| UpArgsNilStk :
  forall k a,
    args_update_rel k a nil nil
| UpArgsConsStk :
  forall k a arg args arg' args',
    arith_update_rel k a arg arg' ->
    args_update_rel k a args args' ->
    args_update_rel k a (arg :: args) (arg' :: args').

Scheme arith_update_rel_mut := Induction for arith_update_rel Sort Prop
    with args_update_rel_mut := Induction for args_update_rel Sort Prop.

Combined Scheme expr_update_rel_mutind from arith_update_rel_mut, args_update_rel_mut.

Definition expr_update_mut_ind_theorem (P: stack_index -> aexp_stack -> aexp_stack -> aexp_stack -> Prop) (P0: stack_index -> aexp_stack -> list aexp_stack -> list aexp_stack -> Prop): Prop :=
  (forall (s: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack),
      arith_update_rel s a aexp aexp' ->
      P s a aexp aexp') /\
    (forall (s: stack_index) (a: aexp_stack) (args args': list aexp_stack),
        args_update_rel s a args args' ->
        P0 s a args args').

Definition expr_update_mut_ind_theorem_P (P: stack_index -> aexp_stack -> aexp_stack -> aexp_stack -> Prop): forall (s : stack_index) (a a0 a1 : aexp_stack), arith_update_rel s a a0 a1 -> Prop :=
  fun (s: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack) =>
  fun (_: arith_update_rel s a aexp aexp') =>
    P s a aexp aexp'.

Definition expr_update_mut_ind_theorem_P0 (P0: stack_index -> aexp_stack -> list aexp_stack -> list aexp_stack -> Prop): forall (s : stack_index) (a : aexp_stack) (l l0 : list aexp_stack), args_update_rel s a l l0 -> Prop := 
  fun (s: stack_index) (a: aexp_stack) (args args': list aexp_stack) =>
  fun (_: args_update_rel s a args args') =>
    P0 s a args args'.

Ltac expr_update_mut_ind_theorem_unfold P P0 P_def P0_def :=
  unfold P, P0; unfold expr_update_mut_ind_theorem_P, expr_update_mut_ind_theorem_P0; unfold P_def, P0_def.


Ltac expr_update_mutual_induction P P0 P_def P0_def :=
  pose (expr_update_mut_ind_theorem_P P_def) as P;
  pose (expr_update_mut_ind_theorem_P0 P0_def) as P0;
  apply (expr_update_rel_mutind P P0);
  expr_update_mut_ind_theorem_unfold P P0 P_def P0_def.

Inductive bool_update_rel: stack_index -> aexp_stack -> bexp_stack -> bexp_stack -> Prop :=
| UpTrueStk :
  forall k a,
    bool_update_rel k a True_Stk True_Stk
| UpFalseStk :
  forall k a,
    bool_update_rel k a False_Stk False_Stk
| UpNegStk :
  forall k a b b',
    bool_update_rel k a b b' ->
    bool_update_rel k a (Neg_Stk b) (Neg_Stk b')
| UpAndStk :
  forall k a b1 b2 b1' b2',
    bool_update_rel k a b1 b1' ->
    bool_update_rel k a b2 b2' ->
    bool_update_rel k a (And_Stk b1 b2) (And_Stk b1' b2')
| UpOrStk :
  forall k a b1 b2 b1' b2',
    bool_update_rel k a b1 b1' ->
    bool_update_rel k a b2 b2' ->
    bool_update_rel k a (Or_Stk b1 b2) (Or_Stk b1' b2')
| UpLeqStk :
  forall k a a1 a2 a1' a2',
    arith_update_rel k a a1 a1' ->
    arith_update_rel k a a2 a2' ->
    bool_update_rel k a (Leq_Stk a1 a2) (Leq_Stk a1' a2').
Inductive meta_update_rel: stack_index -> aexp_stack -> MetavarPred -> MetavarPred -> Prop :=
| UpMetaBool :
  forall k a l l',
    transformed_prop_exprs (bool_update_rel k a) l l' ->
    meta_update_rel k a (MetaBool l) (MetaBool l')
| UpMetaNat :
  forall k a l l',
    transformed_prop_exprs (arith_update_rel k a) l l' ->
    meta_update_rel k a (MetaNat l) (MetaNat l').
    

Inductive stack_large_enough: stack_index -> AbsStack -> Prop :=
| LargeEnoughGeq :
  forall k geq_num,
    k <= geq_num ->
    stack_large_enough k (AbsStkSize geq_num).

Inductive state_update_rel: stack_index -> aexp_stack -> AbsState -> AbsState -> Prop :=
| UpBaseState :
  forall k a s m m',
    meta_update_rel k a m m' ->
    StackExprWellFormed.aexp_well_formed a ->
    StackExprWellFormed.mv_well_formed m ->
    stack_large_enough k s ->
    state_update_rel k a (BaseState s m) (BaseState s m')
| UpAbsAnd :
  forall k a s1 s2 s1' s2',
    state_update_rel k a s1 s1' ->
    state_update_rel k a s2 s2' ->
    StackExprWellFormed.aexp_well_formed a ->
    StackExprWellFormed.absstate_well_formed s1 ->
    StackExprWellFormed.absstate_well_formed s2 ->
    state_update_rel k a (AbsAnd s1 s2) (AbsAnd s1' s2')
| UpAbsOr :
  forall k a s1 s2 s1' s2',
    state_update_rel k a s1 s1' ->
    state_update_rel k a s2 s2' ->
    StackExprWellFormed.absstate_well_formed s1 ->
    StackExprWellFormed.absstate_well_formed s2 ->
    StackExprWellFormed.aexp_well_formed a ->
    state_update_rel k a (AbsOr s1 s2) (AbsOr s1' s2').


(* Higher-order relations on states, stacks, and metavar preds, because I felt like I was going crazy, writing the same relations over and over again *)

Inductive transform_meta_rel (rel_aexp: aexp_stack -> aexp_stack -> Prop) (rel_bexp: bexp_stack -> bexp_stack -> Prop): MetavarPred -> MetavarPred -> Prop :=
| TMetaNat :
  forall l l',
    transformed_prop_exprs rel_aexp l l' ->
    transform_meta_rel rel_aexp rel_bexp (MetaNat l) (MetaNat l')
| TMetaBool :
  forall l l',
    transformed_prop_exprs rel_bexp l l' ->
    transform_meta_rel rel_aexp rel_bexp (MetaBool l) (MetaBool l').

Inductive transform_state_rel (rel_meta: MetavarPred -> MetavarPred -> Prop) (rel_stack: AbsStack -> AbsStack -> Prop) : AbsState -> AbsState -> Prop :=
| TBaseState :
  forall s m s' m',
    rel_stack s s' ->
    rel_meta m m' ->
    transform_state_rel rel_meta rel_stack (BaseState s m) (BaseState s' m')
| TAbsAnd :
  forall s1 s2 s1' s2',
    transform_state_rel rel_meta rel_stack s1 s1' ->
    transform_state_rel rel_meta rel_stack s2 s2' ->
    transform_state_rel rel_meta rel_stack (AbsAnd s1 s2) (AbsAnd s1' s2')
| TAbsOr :
  forall s1 s2 s1' s2',
    transform_state_rel rel_meta rel_stack s1 s1' ->
    transform_state_rel rel_meta rel_stack s2 s2' ->
    transform_state_rel rel_meta rel_stack (AbsOr s1 s2) (AbsOr s1' s2').

Inductive aexp_stk_size_dec_rel: nat -> aexp_stack -> aexp_stack -> Prop :=
| DecConstStk :
  forall dec n,
    aexp_stk_size_dec_rel dec (Const_Stk n) (Const_Stk n)
| DecVarStk :
  forall dec k,
    k > dec ->
    aexp_stk_size_dec_rel dec (Var_Stk k) (Var_Stk (k - dec))
| DecPlusStk :
  forall dec a1 a2 a1' a2',
    aexp_stk_size_dec_rel dec a1 a1' ->
    aexp_stk_size_dec_rel dec a2 a2' ->
    aexp_stk_size_dec_rel dec (Plus_Stk a1 a2) (Plus_Stk a1' a2')
| DecMinusStk :
  forall dec a1 a2 a1' a2',
    aexp_stk_size_dec_rel dec a1 a1' ->
    aexp_stk_size_dec_rel dec a2 a2' ->
    aexp_stk_size_dec_rel dec (Minus_Stk a1 a2) (Minus_Stk a1' a2')
| DecAppStk :
  forall dec f args args',
    args_stk_size_dec_rel dec args args' ->
    aexp_stk_size_dec_rel dec (App_Stk f args) (App_Stk f args')
with args_stk_size_dec_rel : nat -> list aexp_stack -> list aexp_stack -> Prop :=
| DecArgsStkNil :
  forall dec,
    args_stk_size_dec_rel dec nil nil
| DecArgsStkCons :
  forall dec arg arg' args args',
    aexp_stk_size_dec_rel dec arg arg' ->
    args_stk_size_dec_rel dec args args' ->
    args_stk_size_dec_rel dec (arg :: args) (arg' :: args').

Inductive bexp_stk_size_dec_rel : nat -> bexp_stack -> bexp_stack -> Prop :=
| DecTrueStk :
  forall (dec: nat),
    bexp_stk_size_dec_rel dec (True_Stk) (True_Stk)
| DecFalseStk :
  forall (dec: nat),
    bexp_stk_size_dec_rel dec (False_Stk) (False_Stk)
| DecNegStk :
  forall (dec: nat) (b b': bexp_stack),
    bexp_stk_size_dec_rel dec b b' ->
    bexp_stk_size_dec_rel dec (Neg_Stk b) (Neg_Stk b')
| DecAndStk :
  forall (dec: nat) (b1 b2 b1' b2': bexp_stack),
    bexp_stk_size_dec_rel dec b1 b1' ->
    bexp_stk_size_dec_rel dec b2 b2' ->
    bexp_stk_size_dec_rel dec (And_Stk b1 b2) (And_Stk b1' b2')
| DecOrStk :
  forall (dec: nat) (b1 b2 b1' b2': bexp_stack),
    bexp_stk_size_dec_rel dec b1 b1' ->
    bexp_stk_size_dec_rel dec b2 b2' ->
    bexp_stk_size_dec_rel dec (Or_Stk b1 b2) (Or_Stk b1' b2')
| DecLeqStk :
  forall (dec: nat) (a1 a2 a1' a2': aexp_stack),
    aexp_stk_size_dec_rel dec a1 a1' ->
    aexp_stk_size_dec_rel dec a2 a2' ->
    bexp_stk_size_dec_rel dec (Leq_Stk a1 a2) (Leq_Stk a1' a2')
| DecEqStk :
  forall (dec: nat) (a1 a2 a1' a2': aexp_stack),
    aexp_stk_size_dec_rel dec a1 a1' ->
    aexp_stk_size_dec_rel dec a2 a2' ->
    bexp_stk_size_dec_rel dec (Eq_Stk a1 a2) (Eq_Stk a1' a2').
    
                                          

Definition meta_stk_size_dec (dec: nat): MetavarPred -> MetavarPred -> Prop :=
  transform_meta_rel (aexp_stk_size_dec_rel dec) (bexp_stk_size_dec_rel dec).


Inductive absstack_stk_size_dec : nat -> AbsStack -> AbsStack -> Prop :=
| DecAbsStkSize :
  forall dec size,
    size >= dec ->
    absstack_stk_size_dec dec (AbsStkSize size) (AbsStkSize (size - dec)).

Definition absstate_stk_size_dec (dec: nat) : AbsState -> AbsState -> Prop :=
  transform_state_rel (meta_stk_size_dec dec) (absstack_stk_size_dec dec).


Lemma args_stk_size_inc_preserves_args_length :
  forall (args args': list aexp_stack) (inc: nat),
    args_stk_size_inc_rel inc args args' ->
    List.length args = List.length args'.
Proof.
  induction args; intros.
  - invs H. reflexivity.
  - invs H.
    simpl. apply f_equal.
    eapply IHargs; eassumption.
Qed.


