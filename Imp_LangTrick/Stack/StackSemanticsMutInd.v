From Coq Require Import List Arith Psatz.
From Imp_LangTrick Require Import StackLanguage StackLangTheorems.

Definition stack_sem_mut_ind_theorem (P: imp_stack -> fun_env_stk -> stack -> stack -> Prop)
           (P0: aexp_stack -> fun_env_stk -> stack -> stack * nat -> Prop)
           (P1: bexp_stack -> fun_env_stk -> stack -> stack * bool -> Prop)
           (P2: list aexp_stack -> fun_env_stk -> stack -> stack * (list nat) -> Prop): Prop :=
  (forall i fenv stk stk',
      imp_stack_sem i fenv stk stk' ->
      P i fenv stk stk') /\
    (forall a fenv stk stk'n,
        aexp_stack_sem a fenv stk stk'n ->
        P0 a fenv stk stk'n) /\
    (forall b fenv stk stk'v,
        bexp_stack_sem b fenv stk stk'v ->
        P1 b fenv stk stk'v) /\
    (forall args fenv stk stk'vals,
        args_stack_sem args fenv stk stk'vals ->
        P2 args fenv stk stk'vals).

Definition stack_sem_mut_ind_theorem_P (P: imp_stack -> fun_env_stk -> stack -> stack -> Prop): forall (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack), imp_stack_sem i fenv stk stk' -> Prop :=
  fun (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack) =>
  fun (_: imp_stack_sem i fenv stk stk') =>
    P i fenv stk stk'.

Definition stack_sem_mut_ind_theorem_P0 (P0: aexp_stack -> fun_env_stk -> stack -> stack * nat -> Prop) :=
  fun (a: aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'n: stack * nat) =>
  fun (_: aexp_stack_sem a fenv stk stk'n) =>
    P0 a fenv stk stk'n.
Definition stack_sem_mut_ind_theorem_P1 (P1: bexp_stack -> fun_env_stk -> stack -> stack * bool -> Prop) :=
  fun (b: bexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'v: stack * bool) =>
  fun (_: bexp_stack_sem b fenv stk stk'v) =>
    P1 b fenv stk stk'v.
Definition stack_sem_mut_ind_theorem_P2 (P2: list aexp_stack -> fun_env_stk -> stack -> stack * (list nat) -> Prop) :=
  fun (args: list aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'vals: stack * (list nat)) =>
  fun (_: args_stack_sem args fenv stk stk'vals) =>
    P2 args fenv stk stk'vals.


Ltac stack_sem_mutual_induction P P0 P1 P2 P_def P0_def P1_def P2_def :=
  pose (stack_sem_mut_ind_theorem_P P_def) as P;
  pose (stack_sem_mut_ind_theorem_P0 P0_def) as P0;
  pose (stack_sem_mut_ind_theorem_P1 P1_def) as P1;
  pose (stack_sem_mut_ind_theorem_P2 P2_def) as P2;
  apply (imp_stack_mutind P P0 P1 P2);
  unfold P, P0, P1, P2;
  unfold stack_sem_mut_ind_theorem_P, stack_sem_mut_ind_theorem_P0, stack_sem_mut_ind_theorem_P1, stack_sem_mut_ind_theorem_P2;
  unfold P_def, P0_def, P1_def, P2_def.
