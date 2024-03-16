From Coq Require Import String List Arith Psatz.
From Imp_LangTrick Require Import StackLanguage StackLogicBase.


Lemma arith_update_adequacy_forward :
  forall (a: aexp_stack) (k: stack_index) (newval: aexp_stack) (a': aexp_stack),
    a' = arith_update k newval a ->
    arith_update_rel k newval a a'.
  (* /\ *)
    (* (forall (k: stack_index) (newval: aexp_stack) (args args': list aexp_stack), *)
        (* args' = List.map (arith_update k newval) args -> *)
        (* args_update_rel k newval args args'). *)
Proof.
  Check expr_update_mut_ind_theorem_P.
  Check aexp_stack_ind2.
  pose (fun a => forall (k: stack_index) (newval: aexp_stack) (a': aexp_stack),
            a' = arith_update k newval a ->
            arith_update_rel k newval a a') as P.

  intros a.
  apply (aexp_stack_ind2 P); unfold P; simpl; intros; clear P; subst.
  - econstructor.
  - destruct (Nat.eq_dec k n).
    + pose proof (Nat.eqb_eq k n) as Eqb.
      destruct Eqb.
      eapply H0 in e.
      rewrite e. econstructor; eauto.
    + eapply Nat.eqb_neq in n0.
      rewrite n0.
      econstructor; eauto.
      eapply Nat.eqb_neq. eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor. revert H. revert k newval. clear a f.
    induction aexps; intros.
    + econstructor.
    + simpl. invc H.
      econstructor; eauto.
Defined.

Check expr_update_rel_mutind.


Section ArithUpdateOtherDirection.
  Let P s a a0 a1 :=
        a1 = arith_update s a a0.
  Let P0 s a l l0 :=
        l0 = List.map (arith_update s a) l.
  Lemma arith_update_adequacy_obfuscated:
    expr_update_mut_ind_theorem P P0.
  Proof using P P0.
    (* pose (fun s a a0 a1 => *)
    (*       fun (H: arith_update_rel s a a0 a1) => *)
    (*         P s a a0 a1) as P'. *)
    (* pose (fun s a l l0 => *)
    (*       fun (H: args_update_rel s a l l0) => *)
    (*         P0 s a l l0) as P0'. *)
    (* unfold expr_update_mut_ind_theorem. unfold P, P0. *)
    
    expr_update_mutual_induction P' P0' P P0; clear P P0 P' P0'; simpl; intros.
    - reflexivity.
    - eapply Nat.eqb_eq in e. rewrite e. reflexivity.
    - eapply Nat.eqb_neq in n. rewrite n. reflexivity.
    - subst. econstructor.
    - subst. reflexivity.
    - subst. reflexivity.
    - reflexivity.
    - subst. reflexivity.
  Defined.

  Lemma arith_update_adequacy_backward:
    forall (s : stack_index) (a aexp aexp' : aexp_stack),
      arith_update_rel s a aexp aexp' ->
      aexp' = arith_update s a aexp.
  Proof.
    eapply arith_update_adequacy_obfuscated.
  Defined.
  Lemma args_update_adequacy_backward:
    forall (s : stack_index) (a : aexp_stack)
     (args args' : list aexp_stack),
      args_update_rel s a args args' ->
      args' = map (arith_update s a) args.
  Proof.
    eapply arith_update_adequacy_obfuscated.
  Defined.
End ArithUpdateOtherDirection.

Lemma args_update_adequacy_forward :
  forall (k: stack_index) (a: aexp_stack)
    (args args': list aexp_stack),
    args' = map (arith_update k a) args ->
    args_update_rel k a args args'.
Proof.
  induction args; intros.
  simpl in H; subst. econstructor.
  simpl in H. subst. econstructor.
  eapply arith_update_adequacy_forward. reflexivity.
  eapply IHargs; eauto.
Defined.

Lemma bool_update_adequacy:
  forall (k: stack_index) (newval: aexp_stack) (b b': bexp_stack),
    b' = bool_update k newval b <->
      bool_update_rel k newval b b'.
Proof.
  intros k newval b.
  revert k newval.
  induction b; intros; split; intros; subst; simpl; try econstructor; eauto.
  - invs H. reflexivity.
  - invs H. eauto.
  - eapply IHb. reflexivity.
  - invs H. eapply IHb in H3. subst. reflexivity.
  - eapply IHb1. reflexivity.
  - eapply IHb2. eauto.
  - invs H. f_equal.
    eapply IHb1; eauto. eapply IHb2; eauto.
  - eapply IHb1. reflexivity.
  - eapply IHb2. reflexivity.
  - invs H. f_equal; [eapply IHb1 | eapply IHb2]; eauto.
  - eapply arith_update_adequacy_forward; eauto.
  - eapply arith_update_adequacy_forward; eauto.
  - invs H. f_equal; eapply arith_update_adequacy_backward; eauto.
  - eauto using arith_update_adequacy_forward.
  - eauto using arith_update_adequacy_forward.
  - invs H. f_equal; eauto using arith_update_adequacy_backward.
Defined.


From Imp_LangTrick Require Import LogicPropTheorems.
Lemma meta_update_adequacy :
  forall (k: stack_index) (newval: aexp_stack) (P P': MetavarPred),
    P' = meta_update k newval P <->
      meta_update_rel k newval P P'.
Proof.
  intros.
  destruct P; simpl; split; intros; subst.
  - econstructor.
    eapply transform_prop_exprs_adequacy_forward.
    intros. eapply bool_update_adequacy; eauto.
    reflexivity.
  - invs H. eapply transform_prop_exprs_adequacy_backward in H3.
    rewrite H3. reflexivity.
    intros. eapply bool_update_adequacy.
  - econstructor. eapply transform_prop_exprs_adequacy_forward.
    intros. split. intros.
    eapply arith_update_adequacy_forward. eassumption.
    eapply arith_update_adequacy_backward.
    reflexivity.
  - invs H. eapply transform_prop_exprs_adequacy_backward in H3.
    rewrite H3. reflexivity.
    intros. split.
    eapply arith_update_adequacy_forward. eapply arith_update_adequacy_backward.
Defined.

Lemma state_update_adequacy_backwards :
  forall (k: stack_index) (newval: aexp_stack) (P P': AbsState),
    state_update_rel k newval P P' ->
    P' = state_update k newval P.
Proof.
  intros k newval P.
  induction P; intros; invs H; simpl.
  - f_equal. eapply meta_update_adequacy. eassumption.
  - f_equal; eauto.
  - f_equal; eauto.
Defined.

(* The forward direction is trickier since the function doesn't give
 * us any notion of the relation being fine. *)
(*
Lemma state_update_adequacy :
  forall (k: stack_index) (newval: aexp_stack) (P P': AbsState),
    StackExprWellFormed.aexp_well_formed newval ->
    StackExprWellFormed.absstate_well_formed P ->
    P' = state_update k newval P <->
      state_update_rel k newval P P'.
Proof.
  intros k newval P. revert k newval. induction P; intros; split; simpl; intros; subst.
  - econstructor. eapply meta_update_adequacy. reflexivity.
    assumption.
    invs H0. eassumption.
    *)
    


  (* Print arith_update_adequacy''. *)

  
