From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick.Stack Require Import StackLanguage StackPure StackLangTheorems StackSemanticsMutInd StackFrame1.

Require Import Imp_LangTrick.LogicProp.LogicProp.


Lemma max_helper :
  forall (x x0 frame' frame frame'': nat),
    max x (max x0 (max ((x + frame') - frame) ((x0 + frame'') - frame'))) +
      ((x + (frame' - frame))) - x =
      max x (max x0 (max ((x + frame') - frame) ((x0 + frame'') - frame'))) +
        (frame' - frame).
Proof.
  induction x, x0, frame', frame; intros; simpl; repeat rewrite Nat.sub_0_r; repeat rewrite Nat.add_0_r; try reflexivity.
  - rewrite Nat.add_comm. rewrite minus_plus. reflexivity.
  - rewrite Nat.add_comm. rewrite minus_plus. reflexivity.
  - rewrite <- Nat.add_sub_assoc; [ | lia ].
    rewrite <- Nat.add_succ_l. rewrite minus_plus. reflexivity.
  - rewrite <- Nat.add_sub_assoc; [ | lia ]. rewrite <- Nat.add_succ_l.
    rewrite minus_plus. reflexivity.
  - rewrite <- Nat.add_sub_assoc; [ | lia ]. assert (S x - x = S 0) by lia. rewrite H. rewrite Nat.add_1_r. reflexivity.
  - rewrite Nat.add_sub. reflexivity.
  - rewrite <- Nat.add_sub_assoc; [ | lia ]. rewrite <- Nat.add_succ_l. rewrite minus_plus. reflexivity.
  - rewrite <- Nat.add_sub_assoc; [ | lia ]. rewrite <- Nat.add_succ_l. rewrite minus_plus. reflexivity.
Qed.

Lemma max3_3 :
  forall (x x0 frame' frame: nat),
    frame' >= frame ->
    max x (max x0 (max x x0 + frame' - frame)) = max x x0 + frame' - frame.
Proof.
  lia.
Qed.

Lemma max3 :
  forall (x x0 frame' frame: nat),
    frame' <= frame ->
    max x (max x0 (max x x0 + frame' - frame)) = max x x0.
Proof.
  lia.
Qed.

Lemma destruct_max3 :
  forall (n1 n2 n3: nat),
    max n1 (max n2 n3) = n1 \/ max n1 (max n2 n3) = n2 \/ max n1 (max n2 n3) = n3.
Proof.
  lia.
Qed.

Lemma destruct_max2 :
  forall (n1 n2: nat),
    max n1 n2 = n1 \/ max n1 n2 = n2.
Proof.
  lia.
Qed.

Lemma add_add_sub :
  forall n1 n2 n3,
    n1 + (n3 + n2) - n3 = n1 + n2.
Proof.
  destruct n1; intros.
  - simpl. rewrite minus_plus. reflexivity.
  - simpl. destruct n3.
    + simpl. reflexivity.
    + rewrite Nat.add_assoc. rewrite Nat.add_comm. rewrite Nat.add_assoc.
      rewrite <- (Nat.add_1_l n3).
      rewrite Nat.add_assoc. rewrite Nat.add_sub. rewrite Nat.add_1_r.
      rewrite Nat.add_comm. reflexivity.
Qed.

Lemma add_add_sub' :
  forall n1 n2 n3,
    n1 + (n2 + n3) - n1 = n2 + n3.
Proof.
  induction n1; intros.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - simpl. eapply IHn1.
Qed.

Lemma max_silly :
  forall (n1 n2 n3: nat),
    (max n1 (max n2 (max n1 n2 + n3))) = max n1 n2 + n3.
Proof.
  intros. lia.
Qed.

Lemma destruct_max_min :
  forall (n1 n2 n3: nat),
    max n1 (min n2 n3) = n1 \/ max n1 (min n2 n3) = n2 \/ max n1 (min n2 n3) = n3.
Proof.
  lia.
Qed.

Lemma max_min1 :
  forall (n1 n2 n3: nat),
    max n1 (min n2 n3) = n1 ->
    min n2 n3 <= n1 /\ ((n2 <= n3 /\ n2 <= n1) \/ (n2 >= n3 /\ n3 <= n1)).
Proof.
  intros. split.
  - lia.
  - assert (min n2 n3 <= n1) by lia.
    pose proof (le_ge_dec n2 n3).
    destruct H1.
    + left. lia.
    + right. lia.
Qed.
