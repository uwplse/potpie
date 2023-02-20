From DanTrick Require Import EnvToStack DanTrickLanguage StackLanguage.

Definition rcomp_imp_mut_ind_theorem
           (P : list ident -> aexp_Dan -> aexp_stack -> Prop)
           (P0: list ident -> list aexp_Dan -> list aexp_stack -> Prop)
           (P1: list ident -> bexp_Dan -> bexp_stack -> Prop)
           (P2: list ident -> imp_Dan -> imp_stack -> Prop): Prop :=
  (forall (idents: list ident) (a: aexp_Dan) (a': aexp_stack),
      rcompile_aexp idents a a' ->
      P idents a a') /\
    (forall (idents: list ident) (args: list aexp_Dan) (args': list aexp_stack),
        rcompile_args idents args args' ->
        P0 idents args args') /\
    (forall (idents: list ident) (b: bexp_Dan) (b': bexp_stack),
        rcompile_bexp idents b b' ->
        P1 idents b b') /\
    (forall (idents: list ident) (i: imp_Dan) (i': imp_stack),
        rcompile_imp idents i i' ->
        P2 idents i i').

Local Definition rcomp_imp_mut_ind_P (P : list ident -> aexp_Dan -> aexp_stack -> Prop) :=
  fun (idents: list ident) (a: aexp_Dan) (a': aexp_stack) =>
  fun (_: rcompile_aexp idents a a') =>
    P idents a a'.

Local Definition rcomp_imp_mut_ind_P0 (P0: list ident -> list aexp_Dan -> list aexp_stack -> Prop) :=
  fun (idents: list ident) (args: list aexp_Dan) (args': list aexp_stack) =>
  fun (_: rcompile_args idents args args') =>
    P0 idents args args'.

Local Definition rcomp_imp_mut_ind_P1 (P1: list ident -> bexp_Dan -> bexp_stack -> Prop) :=
  fun (idents: list ident) (b: bexp_Dan) (b': bexp_stack) =>
  fun (_: rcompile_bexp idents b b') =>
    P1 idents b b'.

Local Definition rcomp_imp_mut_ind_P2 (P2: list ident -> imp_Dan -> imp_stack -> Prop) :=
  fun (idents: list ident) (i: imp_Dan) (i': imp_stack) =>
  fun (_: rcompile_imp idents i i') =>
    P2 idents i i'.

Ltac rcomp_imp_mutual_induction P P0 P1 P2 P_def P0_def P1_def P2_def :=
  pose (rcomp_imp_mut_ind_P P_def) as P;
  pose (rcomp_imp_mut_ind_P0 P0_def) as P0;
  pose (rcomp_imp_mut_ind_P1 P1_def) as P1;
  pose (rcomp_imp_mut_ind_P2 P2_def) as P2;
  apply (rcomp_imp_mut_ind P P0 P1 P2);
  unfold P, P0, P1, P2;
  unfold rcomp_imp_mut_ind_theorem;
  unfold rcomp_imp_mut_ind_P, rcomp_imp_mut_ind_P0, rcomp_imp_mut_ind_P1, rcomp_imp_mut_ind_P2;
  unfold P_def, P0_def, P1_def, P2_def.
