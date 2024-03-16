From Coq Require Import List Arith Psatz.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLangTheorems.

Definition imp_langtrick_sem_mut_ind_theorem (P: imp_Imp_Lang -> list nat -> fun_env -> nat_env -> nat_env -> Prop)
           (P0: aexp_Imp_Lang -> list nat -> fun_env -> nat_env -> nat -> Prop)
           (P1: bexp_Imp_Lang -> list nat -> fun_env -> nat_env -> bool -> Prop)
           (P2: list aexp_Imp_Lang -> list nat -> fun_env -> nat_env -> (list nat) -> Prop): Prop :=
  (forall i dbenv fenv nenv nenv',
      i_Imp_Lang i dbenv fenv nenv nenv' ->
      P i dbenv fenv nenv nenv') /\
    (forall a dbenv fenv nenv n,
        a_Imp_Lang a dbenv fenv nenv n ->
        P0 a dbenv fenv nenv n) /\
    (forall b dbenv fenv nenv v,
        b_Imp_Lang b dbenv fenv nenv v ->
        P1 b dbenv fenv nenv v) /\
    (forall args dbenv fenv nenv vals,
        args_Imp_Lang args dbenv fenv nenv vals ->
        P2 args dbenv fenv nenv vals).

Definition imp_langtrick_sem_mut_ind_theorem_P (P: imp_Imp_Lang -> list nat -> fun_env -> nat_env -> nat_env -> Prop): forall (i: imp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv nenv': nat_env), i_Imp_Lang i dbenv fenv nenv nenv' -> Prop :=
  fun (i: imp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv nenv': nat_env) =>
  fun (_: i_Imp_Lang i dbenv fenv nenv nenv') =>
    P i dbenv fenv nenv nenv'.

Definition imp_langtrick_sem_mut_ind_theorem_P0 (P0: aexp_Imp_Lang -> list nat -> fun_env -> nat_env -> nat -> Prop) :=
  fun (a: aexp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) (n: nat) =>
  fun (_: a_Imp_Lang a dbenv fenv nenv n) =>
    P0 a dbenv fenv nenv n.
Definition imp_langtrick_sem_mut_ind_theorem_P1 (P1: bexp_Imp_Lang -> list nat -> fun_env -> nat_env -> bool -> Prop) :=
  fun (b: bexp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) (v: bool) =>
  fun (_: b_Imp_Lang b dbenv fenv nenv v) =>
    P1 b dbenv fenv nenv v.
Definition imp_langtrick_sem_mut_ind_theorem_P2 (P2: list aexp_Imp_Lang -> list nat -> fun_env -> nat_env -> (list nat) -> Prop) :=
  fun (args: list aexp_Imp_Lang) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) (vals: (list nat)) =>
  fun (_: args_Imp_Lang args dbenv fenv nenv vals) =>
    P2 args dbenv fenv nenv vals.


Ltac imp_langtrick_sem_mutual_induction P P0 P1 P2 P_def P0_def P1_def P2_def :=
  pose (imp_langtrick_sem_mut_ind_theorem_P P_def) as P;
  pose (imp_langtrick_sem_mut_ind_theorem_P0 P0_def) as P0;
  pose (imp_langtrick_sem_mut_ind_theorem_P1 P1_def) as P1;
  pose (imp_langtrick_sem_mut_ind_theorem_P2 P2_def) as P2;
  apply (i_Imp_Lang_mutind P P0 P1 P2);
  unfold P, P0, P1, P2;
  unfold imp_langtrick_sem_mut_ind_theorem_P, imp_langtrick_sem_mut_ind_theorem_P0, imp_langtrick_sem_mut_ind_theorem_P1, imp_langtrick_sem_mut_ind_theorem_P2;
  unfold P_def, P0_def, P1_def, P2_def.

Ltac imp_langtrick_sem_mutual_induction' P P0 P1 P2 P_term P0_term P1_term P2_term P_def P0_def P1_def P2_def :=
  pose (imp_langtrick_sem_mut_ind_theorem_P P_term) as P;
  pose (imp_langtrick_sem_mut_ind_theorem_P0 P0_term) as P0;
  pose (imp_langtrick_sem_mut_ind_theorem_P1 P1_term) as P1;
  pose (imp_langtrick_sem_mut_ind_theorem_P2 P2_term) as P2;
  apply (i_Imp_Lang_mutind P P0 P1 P2);
  unfold P, P0, P1, P2;
  unfold imp_langtrick_sem_mut_ind_theorem_P, imp_langtrick_sem_mut_ind_theorem_P0, imp_langtrick_sem_mut_ind_theorem_P1, imp_langtrick_sem_mut_ind_theorem_P2;
  unfold P_def, P0_def, P1_def, P2_def.
