From Coq Require Import List String Arith Psatz.

From Imp_LangTrick Require Import  Imp_LangLogicHelpers StackLangTheorems.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Ltac exclude_ridiculous :=
  match goal with
  | [ H: ?x = ?y |- _ ] =>
      match goal with
      | [ H' : x <> y |- _ ] =>
          eapply H' in H; invs H
      | [ H' : y <> x |- _ ] =>
          symmetry in H; eapply H' in H; invs H
      end
  | [ H: ?x <> ?y |- _ ] =>
      match goal with
      | [ |- ?y <> ?x ] =>
          let EQ := fresh "EQ" in
          unfold not; intros EQ; symmetry in EQ; eapply H in EQ; invs EQ
      end
  end.

Tactic Notation "destruct_discrim_r" constr(x) "eqn:" simple_intropattern(EQ1) :=
  destruct x eqn:EQ1;
  match goal with
  | [ H: x = true |- _ ] =>
      try eapply String.eqb_eq in H
  | [ H: x = false |- _ ] =>
      try eapply String.eqb_neq in H
  end;
  try exclude_ridiculous;
  try discriminate; try discrim_neq.

Tactic Notation "copy_hyp" hyp(H) "as" simple_intropattern(H') :=
  pose proof (H' := H).

Tactic Notation "rename_hyp" hyp(H) "as" simple_intropattern(H') :=
  copy_hyp H as H';
  clear H.

Ltac unnot :=
  unfold not; intros.
