From Imp_LangTrick Require Import StackLanguage StackLangTheorems Imp_LangLogicHelpers AexpSind.

From Coq Require Import Eqdep_dec String List Arith.

Ltac not_eq := right; intros neq; invs neq.

Ltac rule_out := try (right; congruence); try (left; reflexivity).

Local Open Scope list_scope.

(* May need mutual induction because of args? Or at least some kind of list eq_dec lemma. *)
Lemma aexp_stack_dec :
  forall (a1 a2: aexp_stack),
      {a1 = a2} + {a1 <> a2}.
     (* forall (args1 args2: list aexp_stack), *)
     (*   {args1 = args2} + {args1 <> args2}). *)
Proof.
  (* destruct a1, a2; try (right; congruence). *)
  (* - *)

  (* intros a1. *)
  Print aexp_stack_ind2.
  pose (fun a1: aexp_stack => forall a2, {a1 = a2} + {a1 <> a2}) as P'.
  intros a1.
  eapply aexp_stack_rec2 with (P := P'); unfold P'; rule_out; intros.
  - destruct a2; rule_out.
    pose proof (Nat.eq_dec n n0). destruct H; subst. left. reflexivity.
    right. congruence.
  - destruct a2; rule_out.
    pose proof (Nat.eq_dec k n). destruct H; rule_out. subst. left; reflexivity.
  - destruct a3; rule_out.
    specialize (H a3_1). specialize (H0 a3_2).
    destruct H, H0; subst; rule_out.
  - destruct a3; rule_out.
    specialize (H a3_1). specialize (H0 a3_2).
    destruct H, H0; subst; rule_out.
  - destruct a2; rule_out.
    pose proof (string_dec f f0).
    destruct H; subst.
    + enough ({args = aexps} + {args <> aexps}).
      * destruct H; subst; rule_out.
      * revert aexps. revert X. clear f0. clear a1. induction args; intros.
        -- destruct aexps; rule_out.
        -- inversion X.
           subst.
           clear X. specialize (IHargs X0).
           destruct aexps; rule_out.
           specialize (H1 a0).
           destruct H1; rule_out.
           subst.
           specialize (IHargs aexps).
           destruct IHargs; rule_out; subst. left. reflexivity.
    + right. congruence.
Defined.

Lemma bexp_stack_dec :
  forall (b1 b2: bexp_stack),
    {b1 = b2} + {b1 <> b2}.
Proof.
  induction b1; rule_out; destruct b2; rule_out; intros; try (left; reflexivity).
  - destruct (IHb1 b2); subst; rule_out.
  - destruct (IHb1_1 b2_1); subst; rule_out.
    destruct (IHb1_2 b2_2); subst; rule_out.
  - destruct (IHb1_1 b2_1); subst; rule_out.
    destruct (IHb1_2 b2_2); subst; rule_out.
  - destruct (aexp_stack_dec a1 a0); subst; rule_out.
    destruct (aexp_stack_dec a2 a3); subst; rule_out.
  - destruct (aexp_stack_dec a1 a0); subst; rule_out.
    destruct (aexp_stack_dec a2 a3); subst; rule_out.
Defined.

Lemma imp_stack_dec :
  forall (i1 i2: imp_stack),
    {i1 = i2} + {i1 <> i2}.
Proof.
  induction i1; rule_out; destruct i2; rule_out; intros; try (left; reflexivity).
  - destruct (aexp_stack_dec a a0); subst; rule_out.
    destruct (Nat.eq_dec k k0); subst; rule_out.
  - destruct (IHi1_1 i2_1); subst; rule_out.
    destruct (IHi1_2 i2_2); subst; rule_out.
  - destruct (bexp_stack_dec b b0); subst; rule_out.
    destruct (IHi1_1 i2_1); subst; rule_out.
    destruct (IHi1_2 i2_2); subst; rule_out.
  - destruct (bexp_stack_dec b b0); subst; rule_out.
    destruct (IHi1 i2); subst; rule_out.
Defined.


Lemma fun_stk_dec :
  forall (f1 f2: fun_stk),
    {f1 = f2} + {f1 <> f2}.
Proof.
  intros. destruct f1, f2.
  destruct (string_dec Name Name0); subst; rule_out.
  destruct (Nat.eq_dec Args Args0); subst; rule_out.
  destruct (Nat.eq_dec Return_pop Return_pop0); subst; rule_out.
  destruct (aexp_stack_dec Return_expr Return_expr0); subst; rule_out.
  destruct (imp_stack_dec Body Body0); subst; rule_out.
Defined.
