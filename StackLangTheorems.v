From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage.

Ltac invs H :=
  inversion H; subst.

Ltac invc H :=
  invs H; clear H.

Lemma args_stack_sem_preserves_length :
  forall args fenv stk stk' vals,
    args_stack_sem args fenv stk (stk', vals) ->
    List.length args = List.length vals.
Proof.
  induction args; intros.
  - invc H. reflexivity.
  - invc H.
    eapply IHargs in H7.
    simpl. f_equal. assumption.
Qed.

Lemma skip_n_of_mutated_stack :
  forall k n c stk'0 stk',
    k <= n ->
    1 <= k ->
    k <= Datatypes.length stk'0 ->
    stack_mutated_at_index stk' k c stk'0 ->
    skipn n stk'0 = skipn n stk'.
Proof.
  intros k n c stk'0.
  revert k n c.
  induction stk'0; intros.
  - inversion H2.
  - inversion H2.
    + induction n.
      * simpl. subst. inversion H.
      * simpl. invs H2.
        -- reflexivity.
        -- inversion H11.
           inversion H4.
    + subst.
      assert (exists (k': nat), k = S (k')).
      {
        destruct k.
        inversion H5.
        exists k. reflexivity.
      }
      destruct H3. subst.
      assert (exists n', n = S n').
      {
        destruct n.
        inversion H.
        exists n.
        reflexivity.
      }
      destruct H3. subst.
      simpl.
      eapply IHstk'0.
      assert (x <= x0) by intuition.
      eassumption.
      intuition.
      rewrite H7 in H6.
      intuition.
      assert (S x - 1 = x) by intuition.
      rewrite H3 in H11.
      eassumption.
Qed.

Lemma same_after_popping_skipn :
  forall stk1 n stk3 stk',
    stk1 = skipn n stk3 ->
    same_after_popping stk' stk3 n ->
    stk1 = stk'.
Proof.
  intros stk1 n stk3. revert stk3 stk1. induction n; induction stk3; intros.
  - simpl in *.
    invc H0.
    reflexivity.
  - simpl in H. invc H0.
    reflexivity.
  - invc H0.
  - simpl in H.
    inversion H0.
    revert H. subst. intros H.
    eapply IHn.
    + eassumption.
    + eassumption.
Qed.

(* You pop the entire prepended list off, you end up with the other list *)
Lemma same_after_popping_length :
  forall stk stk' stk'' n,
    same_after_popping stk (stk' ++ stk'') n ->
    Datatypes.length stk' = n ->
    stk = stk''.
Proof.
  intros stk stk' stk'' n. revert stk stk' stk''.
  dependent induction n; intros.
  - invs H. rewrite length_zero_iff_nil in H0. subst. auto.
  - invs H. destruct stk'.
    + invs H0.
    + simpl in H1. invs H1. eapply IHn; eauto.
Qed.

Lemma same_after_popping_length1:
  forall stk stk' stk'' n,
    Datatypes.length stk' = n ->
    stk = stk'' ->
    same_after_popping stk (stk' ++ stk'') n.
Proof.
  intros stk stk' stk'' n. revert stk stk' stk''.
  induction n; intros.
  - subst. destruct stk'; [ | simpl in H; inversion H ].
    simpl. constructor. reflexivity.
  - destruct stk'; [ simpl in H; inversion H | ].
    simpl. constructor.
    apply IHn.
    + simpl in H. inversion H. reflexivity.
    + assumption.
Qed.
