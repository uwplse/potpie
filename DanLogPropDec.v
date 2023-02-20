From Coq Require Import Arith Eqdep_dec.
From DanTrick Require Import DanTrickLanguage DanLogProp.
From DanTrick Require Import LogicProp LogicPropDec.

Ltac unfold_logic_prop_defs :=
  unfold UIP_LogicPropAexpDan.LP.lp_t in *;
  unfold UIP_LogicPropAexpDan.LP.A in *;
  unfold UIP_LogicPropAexpDan.LP.V in *;
  unfold UIP_LPBexpDan.LP.lp_t in *;
  unfold UIP_LPBexpDan.LP.A, UIP_LPBexpDan.LP.V in *.

(*
 * Here is our axiom that UIP holds over AbsEnv, which is consistent
 * and doesn't have any serious implications since A and V are
 * decidable. It's also true in spirit, and it makes dependent 
 * induction and dependent pattern matching much easier.
 * There may be ways around this eventually if need be, though.
 *)
Axiom UIP_AbsEnv :
  forall (l1 l2: AbsEnv)
    (p1 p2: l1 = l2),
    p1 = p2.

Lemma UIP_AbsEnv_refl :
  forall (l: AbsEnv)
    (p: l = l),
    p = eq_refl.
Proof.
  intros.
  pose proof (UIP_AbsEnv).
  specialize (H l l p (@eq_refl _ l)).
  eassumption.
Qed.
