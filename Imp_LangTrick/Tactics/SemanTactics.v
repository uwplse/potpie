From Coq Require Import Arith Psatz String List.

From Imp_LangTrick Require Import Imp_LangTrickLanguage SeriesHelperCompilation ImpExampleHelpers rsa_impLang Imp_LangLogProp LogicProp NotTerribleBImpLangInversion.

(** Seman(tics)-related Tactics *)



Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Lemma imp_if :
  forall b i1 i2 dbenv nenv fenv nenv' bval,
    b_Imp_Lang b dbenv fenv nenv bval ->
    (if bval then i_Imp_Lang i1 dbenv fenv nenv nenv' else i_Imp_Lang i2 dbenv fenv nenv nenv') ->
    i_Imp_Lang (IF_Imp_Lang b i1 i2) dbenv fenv nenv nenv'.
Proof.
  intros. destruct bval.
  - eapply Imp_Lang_if_true; eassumption.
  - eapply Imp_Lang_if_false; eassumption.
Qed.

Lemma imp_while :
  forall b i dbenv nenv fenv nenv' bval,
    b_Imp_Lang b dbenv fenv nenv bval ->
    (if bval then (exists nenv'', i_Imp_Lang i dbenv fenv nenv nenv'' /\ i_Imp_Lang (WHILE_Imp_Lang b i) dbenv fenv nenv'' nenv')
     else nenv = nenv') ->
    i_Imp_Lang (WHILE_Imp_Lang b i) dbenv fenv nenv nenv'.
Proof.
  intros. destruct bval.
  - destruct H0.
    destruct H0.
    eapply Imp_Lang_while_step; eassumption.
  - subst. eapply Imp_Lang_while_done. eassumption.
Qed.

Lemma imp_assign :
  forall x a n dbenv fenv nenv nenv',
    a_Imp_Lang a dbenv fenv nenv n ->
    nenv' = update x n nenv ->
    i_Imp_Lang (ASSIGN_Imp_Lang x a) dbenv fenv nenv nenv'.
Proof.
  intros. rewrite H0. econstructor. assumption.   
Qed. 

Lemma b_Imp_Lang_neg_bval :
  forall b dbenv fenv nenv bval,
    b_Imp_Lang b dbenv fenv nenv (negb bval) ->
    b_Imp_Lang (NEG_Imp_Lang b) dbenv fenv nenv bval.
Proof.
  intros. rewrite Bool.negb_involutive_reverse. econstructor. assumption.   
Qed. 

Lemma b_Imp_Lang_and_bval :
  forall b1 b2 dbenv fenv nenv bval bv1 bv2,
    b_Imp_Lang b1 dbenv fenv nenv bv1 ->
    b_Imp_Lang b2 dbenv fenv nenv bv2 ->
    bval = andb bv1 bv2 ->
    b_Imp_Lang (AND_Imp_Lang b1 b2) dbenv fenv nenv bval.
Proof.
  intros. rewrite H1. econstructor; assumption.   
Qed. 

Lemma b_Imp_Lang_or_bval :
  forall b1 b2 dbenv fenv nenv bval bv1 bv2,
    b_Imp_Lang b1 dbenv fenv nenv bv1 ->
    b_Imp_Lang b2 dbenv fenv nenv bv2 ->
    bval = orb bv1 bv2 ->
    b_Imp_Lang (OR_Imp_Lang b1 b2) dbenv fenv nenv bval.
Proof.
  intros. rewrite H1. econstructor; assumption. 
Qed. 

Lemma b_Imp_Lang_leq_bval :
  forall a1 a2 dbenv fenv nenv bval n1 n2,
    a_Imp_Lang a1 dbenv fenv nenv n1 ->
    a_Imp_Lang a2 dbenv fenv nenv n2 ->
    bval = Nat.leb n1 n2 ->
    b_Imp_Lang (LEQ_Imp_Lang a1 a2) dbenv fenv nenv bval.
Proof.
  intros. rewrite H1. econstructor; assumption. 
Qed. 

Lemma a_Imp_Lang_const_nat_val :
  forall n n' dbenv fenv nenv,
    n = n' ->
    a_Imp_Lang (CONST_Imp_Lang n) dbenv fenv nenv n'.
Proof.
  intros. rewrite H. econstructor. 
Qed. 

Lemma a_Imp_Lang_plus_nat_val :
  forall a1 a2 n n1 n2 dbenv fenv nenv,
    a_Imp_Lang a1 dbenv fenv nenv n1 ->
    a_Imp_Lang a2 dbenv fenv nenv n2 ->
    n = n1 + n2 ->
    a_Imp_Lang (PLUS_Imp_Lang a1 a2) dbenv fenv nenv n.
Proof.
  intros. rewrite H1; econstructor; assumption. 
Qed. 

Lemma a_Imp_Lang_minus_nat_val :
  forall a1 a2 n n1 n2 dbenv fenv nenv,
    a_Imp_Lang a1 dbenv fenv nenv n1 ->
    a_Imp_Lang a2 dbenv fenv nenv n2 ->
    n = n1 - n2 ->
    a_Imp_Lang (MINUS_Imp_Lang a1 a2) dbenv fenv nenv n.
Proof.
  intros. rewrite H1; econstructor; assumption. 
Qed. 




Ltac smarter_a_Imp_Lang_econstructor :=
  match goal with
  | [ |- a_Imp_Lang (APP_Imp_Lang "mult" _) _ _ _ _ ] =>
      eapply mult_aexp_wrapper; try reflexivity; try smarter_a_Imp_Lang_econstructor
  | [ |- a_Imp_Lang (APP_Imp_Lang "frac_add_denominator" _ ) _ _ _ _ ] =>
      eapply frac_add_denominator_wrapper; try reflexivity; try smarter_a_Imp_Lang_econstructor
  | [ |- a_Imp_Lang (APP_Imp_Lang "frac_add_numerator" _ ) _ _ _ _ ] =>
      eapply frac_add_numerator_wrapper; try reflexivity; try smarter_a_Imp_Lang_econstructor
  | [ |- a_Imp_Lang (APP_Imp_Lang "frac_sub_numerator" _ ) _ _ _ _ ] =>
      eapply frac_sub_numerator_wrapper; try (cbn; reflexivity); try smarter_a_Imp_Lang_econstructor
  | [ |- a_Imp_Lang (PLUS_Imp_Lang _ _ ) _ _ _ _ ] =>
      eapply a_Imp_Lang_plus_nat_val; [ try smarter_a_Imp_Lang_econstructor .. | try reflexivity ]
  | [ |- a_Imp_Lang (MINUS_Imp_Lang _ _ ) _ _ _ _ ] =>
      eapply a_Imp_Lang_minus_nat_val; [ try smarter_a_Imp_Lang_econstructor .. | try reflexivity ]
  | [ |- a_Imp_Lang (CONST_Imp_Lang _ ) _ _ _ _ ] =>
      eapply a_Imp_Lang_const_nat_val; try reflexivity
  | [ |- a_Imp_Lang _ _ _ _ _ ] =>
      econstructor; try (cbn; reflexivity); try smarter_a_Imp_Lang_econstructor
  | [ |- args_Imp_Lang (_ :: _) _ _ _ _ ] =>
      econstructor; smarter_a_Imp_Lang_econstructor
  | [ |- args_Imp_Lang nil _ _ _ _ ] =>
      eapply args_nil
  end.


Ltac smarter_b_Imp_Lang_econstructor :=
  try unfold gt_Imp_Lang;
  try unfold lt_Imp_Lang;
  try unfold neq_Imp_Lang;
  try unfold eq_Imp_Lang;
  match goal with
  | [ |- b_Imp_Lang (LEQ_Imp_Lang _ _ ) _ _ _ _ ] =>
      eapply b_Imp_Lang_leq_bval; try smarter_b_Imp_Lang_econstructor
  | [ |- b_Imp_Lang (AND_Imp_Lang _ _ ) _ _ _ _ ] =>
      eapply b_Imp_Lang_and_bval; try smarter_b_Imp_Lang_econstructor
  | [ |- b_Imp_Lang (OR_Imp_Lang _ _ ) _ _ _ _ ] =>
      eapply b_Imp_Lang_or_bval; try smarter_b_Imp_Lang_econstructor
  | [ |- b_Imp_Lang (NEG_Imp_Lang _) _ _ _ _ ] =>
      eapply b_Imp_Lang_neg_bval; try smarter_b_Imp_Lang_econstructor
  | [ |- a_Imp_Lang _ _ _ _ _  ] =>
      try smarter_a_Imp_Lang_econstructor
  end.

Ltac smarter_i_Imp_Lang_econstructor :=
  match goal with
  | [ |- i_Imp_Lang (ASSIGN_Imp_Lang _ _ ) _ _ _ _ ] =>
      eapply imp_assign; [try smarter_a_Imp_Lang_econstructor | try reflexivity]
  | [ |- i_Imp_Lang (IF_Imp_Lang _ _ _ ) _ _ _ _ ] =>
      eapply imp_if; [ try smarter_b_Imp_Lang_econstructor | simpl; try smarter_i_Imp_Lang_econstructor .. ]
  | [ |- i_Imp_Lang (WHILE_Imp_Lang _ _) _ _ _ _ ] =>
      eapply imp_while; [ try smarter_b_Imp_Lang_econstructor | simpl; try smarter_i_Imp_Lang_econstructor .. ]
  | [ |- i_Imp_Lang _ _ _ _ _ ] =>
      econstructor; try smarter_i_Imp_Lang_econstructor
  end.

Ltac smarter_imp_econstructor :=
  match goal with
  | [ |- i_Imp_Lang _ _ _ _ _ ] =>
      smarter_i_Imp_Lang_econstructor
  | [ |- a_Imp_Lang _ _ _ _ _ ] =>
      smarter_a_Imp_Lang_econstructor
  | [ |- b_Imp_Lang _ _ _ _ _ ] =>
      smarter_b_Imp_Lang_econstructor
  | [ |- args_Imp_Lang _ _ _ _ _ ] =>
      smarter_a_Imp_Lang_econstructor
  end.


Ltac AbsEnv_rel_inversion :=
  repeat match goal with
         | [ H: AbsEnv_rel _ _ _ _ |- _ ] =>
             invc H
         | [ H: Imp_Lang_lp_rel _ _ _ _ |- _ ] =>
             invc H
         | [ H: eval_prop_rel _ _ |- _ ] =>
             invc H
         | [ H: eval_prop_args_rel _ _ _ |- _ ] =>
             invc H
         | [ H: a_Imp_Lang (MINUS_Imp_Lang _ _ ) _ _ _ _ |- _ ] =>
             invc H
         | [ H: a_Imp_Lang (PLUS_Imp_Lang _ _ ) _ _ _ _ |- _ ] =>
             invc H
         | [ H: b_Imp_Lang _ _ _ _ _ |- _ ] =>
             repeat (try unfold lt_Imp_Lang in H;
                     try unfold gt_Imp_Lang in H;
                     try unfold neq_Imp_Lang in H;
                     try unfold eq_Imp_Lang in H);
             try smart_b_Imp_Lang_inversion
         end;
  repeat Imp_LangLogicHelpers.a_Imp_Lang_same;
  repeat Imp_LangLogicHelpers.b_Imp_Lang_same.

