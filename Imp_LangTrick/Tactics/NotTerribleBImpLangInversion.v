From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLangTheorems.

Lemma bexp_imp_lang_leq_backwards :
  forall a1 a2 dbenv fenv nenv bval,
    b_Imp_Lang
      (LEQ_Imp_Lang a1 a2) dbenv fenv nenv bval ->
    (exists n1 n2,
        a_Imp_Lang a1 dbenv fenv nenv n1 /\
          a_Imp_Lang a2 dbenv fenv nenv n2 /\
          bval = Nat.leb n1 n2).
Proof.
  intros.
  invc H.
  exists n1. exists n2.
  repeat split; eassumption.
Qed.


Lemma bexp_imp_lang_or_backwards :
  forall b1 b2 dbenv fenv nenv bval,
    b_Imp_Lang
      (OR_Imp_Lang b1 b2) dbenv fenv nenv bval ->
    (exists bv1 bv2,
        b_Imp_Lang b1 dbenv fenv nenv bv1 /\
          b_Imp_Lang b2 dbenv fenv nenv bv2 /\
          bval = orb bv1 bv2).
Proof.
  intros.
  invc H.
  exists b0. exists b3.
  repeat split; eassumption.
Qed.

Lemma bexp_imp_lang_and_backwards :
  forall b1 b2 dbenv fenv nenv bval,
    b_Imp_Lang
      (AND_Imp_Lang b1 b2) dbenv fenv nenv bval ->
    (exists bv1 bv2,
        b_Imp_Lang b1 dbenv fenv nenv bv1 /\
          b_Imp_Lang b2 dbenv fenv nenv bv2 /\
          bval = andb bv1 bv2).
Proof.
  intros.
  invc H.
  exists b0. exists b3.
  repeat split; eassumption.
Qed.

Lemma bexp_imp_lang_neg_backwards :
  forall b dbenv fenv nenv bval,
    b_Imp_Lang
      (NEG_Imp_Lang b) dbenv fenv nenv bval ->
    exists bv,
      b_Imp_Lang b dbenv fenv nenv bv /\
        bval = negb bv.
Proof.
  intros.
  invc H.
  exists b0.
  split; eauto.
Qed.

Ltac smart_b_Imp_Lang_inversion :=
  repeat match goal with
         | [ H: b_Imp_Lang (LEQ_Imp_Lang _ _) _ _ _ _ |- _ ] =>
             eapply bexp_imp_lang_leq_backwards in H;
             let n := fresh "n" in
             let n0 := fresh "n" in
             let A1 := fresh "A1" in
             let A2 := fresh "A2" in
             let Hleq := fresh "Hleq" in
             destruct H as (n & n0 & A1 & A2 & Hleq)
         | [ H: b_Imp_Lang (?AND_OR _ _) _ _ _ _ |- _ ] =>
             let v := fresh "v" in
             let v0 := fresh "v" in
             let B1 := fresh "B1" in
             let B2 := fresh "B2" in
             match AND_OR with
             | OR_Imp_Lang =>
                 eapply bexp_imp_lang_or_backwards in H;
                 let H_or := fresh "H_or" in
                 destruct H as (v & v0 & B1 & B2 & H_or)
             | AND_Imp_Lang =>
                 eapply bexp_imp_lang_and_backwards in H;
                 let H_and := fresh "H_and" in
                 destruct H as (v & v0 & B1 & B2 & H_and)
             end
         | [ H: b_Imp_Lang (NEG_Imp_Lang _ ) _ _ _ _ |- _ ] =>
             eapply bexp_imp_lang_neg_backwards in H;
             let v := fresh "v" in
             let B := fresh "B" in
             let H_neg := fresh "H_neg" in
             destruct H as (v & B & H_neg)
         end.
