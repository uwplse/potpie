From DanTrick Require Import LogicProp DanTrickLanguage StackLangTheorems DanLogicHelpers.
Require Import Coq.Arith.Peano_dec Coq.Strings.String Coq.Lists.List.
Require Import Coq.Logic.PropExtensionalityFacts Coq.Logic.Eqdep_dec.
From Coq Require Import Arith.

(*
 * We assume UIP holds over AbsEnv. For this to be a reasonable assumption that doesn't imply
 * too many bad things, we want it to be true that UIP holds over parameters A and V to LogicProp.
 * Thus, we require that A and V have decidable equality.
 *)

(* useful tactic *)
Ltac not_eq := right; intros neq; inversion neq.  

Lemma list_forall_eq_dec :
  forall (l l' : list aexp_Dan),
    SForall (fun x => forall y, {x = y} + {x <> y}) l ->
    {l = l'} + {l <> l'}.
Proof.
  induction l, l'; intros; try (solve [not_eq | intuition]).
  inversion H. subst. destruct (H2 a0).
  - subst. destruct (IHl l'); auto.
    + subst. left. auto.
    + not_eq. subst. apply n. auto.
  - not_eq. subst. apply n. auto.
Qed.

(* lemma to make sure requiring V to be decidable is at least sometimes possible *)
Lemma aexp_Dan_dec :
  forall (a1 a2 : aexp_Dan), ({a1 = a2} + {a1 <> a2}).
Proof.
  intros a1.
  induction a1 using aexp_Dan_rec2 with (P := (fun a1 => forall a2, {a1 = a2} + {a1 <> a2}));
  induction a2 using aexp_Dan_rec2; try (solve [not_eq | intuition]).
  - destruct (eq_nat_dec n n0).
    + subst. left. auto.
    + not_eq. subst. apply n1. auto.
  - destruct (string_dec x x0).
    + subst. left. auto.
    + not_eq. subst. apply n. auto.
  - destruct (eq_nat_dec n n0).
    + subst. left. auto.
    + not_eq. subst. apply n1. auto.
  - destruct (IHa1_1 a2_1).
    + subst. destruct (IHa1_2 a2_2).
      * subst. left. auto.
      * not_eq. subst. apply n. auto.
    + not_eq. subst. apply n. auto.
  - destruct (IHa1_1 a2_1).
    + subst. destruct (IHa1_2 a2_2).
      * subst. left. auto.
      * not_eq. subst. apply n. auto.
    + not_eq. subst. apply n. auto.
  - destruct (string_dec f f0).
    + subst. destruct (list_forall_eq_dec aexps aexps0 H).
      * subst. left. auto.
      * not_eq. subst. apply n. auto.
    + not_eq. subst. apply n. auto.
Qed.

Lemma bexp_neg_not_identity :
  forall b: bexp_Dan,
    b <> NEG_Dan b.
Proof.
  induction b; unfold not; intros; invs H.
  eapply IHb in H1. eassumption.
Qed.

Lemma bexp_Dan_dec :
  forall (b1 b2: bexp_Dan),
    {b1 = b2} + {b1 <> b2}.
Proof.
  induction b1; induction b2; intros; try (left; reflexivity);
    match goal with
    | [ |- { ?bdan_op ?b1 ?b2 = ?bdan_op' ?b3 ?b4 } + { _ <> _ } ] =>
        match bdan_op with
        | bdan_op' => idtac
        | _ => not_eq
        end
    | [ |- {_ _ _ = _ } + { _ } ] =>
        not_eq
    | [ |- { _ = _ _ _ } + { _ } ] =>
        not_eq
    | [ |- { ?bdan_const = _ _ } + { _ } ] =>
        match bdan_const with
        | TRUE_Dan => not_eq
        | FALSE_Dan => not_eq
        | _ => idtac
        end
    | [ |- { _ _ = ?bdan_const } + { _ } ] =>
        match bdan_const with
        | TRUE_Dan => not_eq
        | FALSE_Dan => not_eq
        end
    | _ => idtac
    end; [> not_eq | not_eq | .. ].
  - specialize (IHb1 b2).
    destruct IHb1.
    + rewrite e. left. reflexivity.
    + right. unfold not; intros. invs H. discrim_neq.
  - specialize (IHb1_1 b2_1). specialize (IHb1_2 b2_2).
    destruct IHb1_1, IHb1_2; [ subst; left; reflexivity | .. ]; not_eq; subst; try discrim_neq.
  - specialize (IHb1_1 b2_1). specialize (IHb1_2 b2_2).
    destruct IHb1_1, IHb1_2; [ subst; left; reflexivity | .. ]; not_eq; subst; try discrim_neq.
  - pose proof (aexp_Dan_dec).
    pose proof (H' := H).
    specialize (H a1 a0).
    specialize (H' a2 a3).
    destruct H, H'; [ subst; left; reflexivity | .. ]; not_eq; subst; try discrim_neq.
Qed.

(*
 * OK, since it's reasonable to assume A and V are decidable, and thus proof irrelevant,
 * maybe it is not so bad to assume LogicProp is proof irrelevant in general.
 * At the very least, it shouldn't mess with any computation over A and V.
 *
 * What would that imply? Would that mess with computation? It would almost certainly
 * help us inside of our proofs.
 *)
Section UIP_LP.

Parameter A : Set.
Parameter V : Set.
Parameter A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.
Parameter V_eq_dec : forall (v1 v2 : V), {v1 = v2} + {v1 <> v2}.

Lemma UIP_on_A :
  forall (a1 a2 : A) (p1 p2 : a1 = a2), p1 = p2.
Proof.
  intros. apply UIP_dec. apply A_eq_dec.
Defined.

Lemma UIP_on_V :
  forall (v1 v2 : V) (p1 p2 : v1 = v2), p1 = p2.
Proof.
  intros. apply UIP_dec. apply V_eq_dec.
Defined.

End UIP_LP.

Module Type LPModule.
  Parameter V: Set.
  Parameter A: Set.

  Definition lp_t := LogicProp V A.

  Parameter V_eq_dec : forall (v1 v2: V), {v1 = v2} + {v1 <> v2}.
  Parameter A_eq_dec : forall (a1 a2: A), {a1 = a2} + {a1 <> a2}.

  Parameter UIP_on_A :
    forall (a1 a2 : A) (p1 p2 : a1 = a2), p1 = p2.

  Parameter UIP_on_V :
    forall (v1 v2 : V) (p1 p2 : v1 = v2), p1 = p2.
End LPModule.

Module Type UIP_LPType.
  Declare Module LP : LPModule.
End UIP_LPType.

Module UIP_LPModule (LP: LPModule) <: UIP_LPType.
  Module LP := LP.
End UIP_LPModule.

Module LogicPropAexpDan <: LPModule.
  Definition V := nat.
  Definition A := aexp_Dan.
  Definition lp_t := LogicProp nat aexp_Dan.

  Definition V_eq_dec := PeanoNat.Nat.eq_dec.
  Definition A_eq_dec := aexp_Dan_dec.

  Lemma UIP_on_A :
  forall (a1 a2 : A) (p1 p2 : a1 = a2), p1 = p2.
  Proof.
    intros. apply UIP_dec. apply A_eq_dec.
  Defined.

  Lemma UIP_on_V :
    forall (v1 v2 : V) (p1 p2 : v1 = v2), p1 = p2.
  Proof.
    intros. apply UIP_dec. apply V_eq_dec.
  Defined.
End LogicPropAexpDan.

Module UIP_LogicPropAexpDan := UIP_LPModule(LogicPropAexpDan).

Module LPBexpDan <: LPModule.
  
  Definition V := bool.
  Definition A := bexp_Dan.
  Definition lp_t := LogicProp bool bexp_Dan.
  
  Lemma V_eq_dec :
    forall (v1 v2: V),
      {v1 = v2} + {v1 <> v2}.
  Proof.
    destruct v1, v2; [ left | not_eq .. | left ];
      try reflexivity.
  Defined.
  
  Definition A_eq_dec := bexp_Dan_dec.

  Lemma UIP_on_A :
  forall (a1 a2 : A) (p1 p2 : a1 = a2), p1 = p2.
  Proof.
    intros. apply UIP_dec. apply A_eq_dec.
  Defined.

  Lemma UIP_on_V :
    forall (v1 v2 : V) (p1 p2 : v1 = v2), p1 = p2.
  Proof.
    intros. apply UIP_dec. apply V_eq_dec.
  Defined.

End LPBexpDan.

Module UIP_LPBexpDan := UIP_LPModule(LPBexpDan).


