From Coq Require Import List Arith.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel Imp_LangTrickLanguage ImpVarMap ImpVarMapTheorems StackLangTheorems.

Lemma imp_rec_rel_var_map_wf_adequacy_forward :
  forall (i: imp_Imp_Lang) (idents: list ident),
    imp_rec_rel (var_map_wf_wrt_imp idents) i ->
    var_map_wf_wrt_imp idents i.
Proof.
  induction i; intros; invs H.
  - eapply IHi1 in H4.  eapply IHi2 in H5.
    unfold_wf_imp_in H4; unfold_wf_imp_in H5; unfold_wf_imp.
    + eapply WF0.
    + econstructor; unfold_wf_imp_in H6;
        invs WF'1; eassumption.
    + unfold_wf_imp_in H6.
      eassumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma imp_rec_rel_var_map_wf_adequacy_backward :
  forall (i: imp_Imp_Lang) (idents: list ident),
    var_map_wf_wrt_imp idents i ->
    imp_rec_rel (var_map_wf_wrt_imp idents) i.
Proof.
  induction i; intros; pose proof (WF__orig := H); unfold_wf_imp_in H.
  - econstructor.
    + eapply IHi1.
      unfold_wf_imp.
      * eassumption.
      * invs WF'. assumption.
      * intros.
        eapply WF''. eapply ImpHasVarIf__then. assumption.
    + eapply IHi2. unfold_wf_imp.
      * eassumption.
      * invs WF'. eassumption.
      * intros. eapply WF''. eapply ImpHasVarIf__else. assumption.
    + assumption.
  - econstructor. assumption.
  - econstructor.
    + eapply IHi. unfold_wf_imp.
      * eassumption.
      * invs WF'. assumption.
      * intros.  eapply WF''.
        eapply ImpHasVarWhile__body. assumption.
    + eassumption.
  - econstructor. eassumption.
  - econstructor.
    + eapply IHi1. unfold_wf_imp.
      * eassumption.
      * invs WF'. eassumption.
      * intros. eapply WF''. econstructor. assumption.
    + eapply IHi2. unfold_wf_imp.
      * eassumption.
      * invs WF'. eassumption.
      * intros. eapply WF''. eapply ImpHasVarSeq__right. assumption.
    + assumption.
Qed.

Theorem imp_rec_rel_var_map_wf_adequacy :
  forall (i: imp_Imp_Lang) (idents: list ident),
    imp_rec_rel (var_map_wf_wrt_imp idents) i <->
      var_map_wf_wrt_imp idents i.
Proof.
  split; intros;
    first [eapply imp_rec_rel_var_map_wf_adequacy_forward | eapply imp_rec_rel_var_map_wf_adequacy_backward];
    eauto.
Qed.

Ltac smart_unfold_wf_imp_in H :=
  let typeH := type of H in
  match typeH with
  | imp_rec_rel (var_map_wf_wrt_imp ?map) ?i =>
      eapply imp_rec_rel_var_map_wf_adequacy in H
  | _ =>
      idtac
  end;
  unfold_wf_imp_in H.

Ltac smart_unfold_wf_imp :=
  match goal with
  | [ |- imp_rec_rel (var_map_wf_wrt_imp _) _ ] =>
      eapply imp_rec_rel_var_map_wf_adequacy
  | _ => idtac
  end;
  unfold_wf_imp.
