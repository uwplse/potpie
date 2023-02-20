From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.
Add LoadPath "./" as DanTrick.
Require Import DanTrick.DanTrickLanguage 
  DanTrick.LogicProp 
  DanTrick.DanLogicHelpers 
  DanTrick.DanLogProp 
  DanTrick.DanLogSubst .


Definition triple_Dan (P: AbsEnv) (i: imp_Dan) (Q: AbsEnv) (fenv: fun_env) : Prop :=
  forall dbenv nenv nenv', 
  i_Dan i dbenv fenv nenv nenv' ->
  AbsEnv_rel P fenv dbenv nenv -> 
  AbsEnv_rel Q fenv dbenv nenv'.
  
Definition atrueDan (b: bexp_Dan) (P: AbsEnv): AbsEnv :=
  (AbsEnvAnd P (AbsEnvLP (Dan_lp_bool (UnaryProp _ _
                                            (fun bval => bval = true)
                                            b)))).

Definition afalseDan (b: bexp_Dan) (P: AbsEnv): AbsEnv :=
  (AbsEnvAnd P (AbsEnvLP (Dan_lp_bool (UnaryProp _ _
                                            (fun bval => bval = false)
                                            b)))).

Definition aimpDan (P Q: AbsEnv) (fenv: fun_env): Prop :=
  forall dbenv nenv,
    AbsEnv_rel P fenv dbenv nenv -> AbsEnv_rel Q fenv dbenv nenv. 

Definition aandDan (P Q: assertion): assertion :=
  fun dbenv nenv => P dbenv nenv /\ Q dbenv nenv.

Notation "P -->> Q" := (aimpDan P Q) (at level 95, no associativity).

Inductive hl_Dan : AbsEnv -> imp_Dan -> AbsEnv -> fun_env -> Type :=
| hl_Dan_skip :
  forall P fenv,
    hl_Dan P SKIP_Dan P fenv 
| hl_Dan_assign :
  forall P fenv x a,
    hl_Dan (subst_AbsEnv x a P) (ASSIGN_Dan x a) P fenv
| hl_Dan_seq :
  forall P Q R i1 i2 fenv,
    hl_Dan P i1 R fenv ->
    hl_Dan R i2 Q fenv ->
    hl_Dan P (SEQ_Dan i1 i2) Q fenv
| hl_Dan_if :
  forall P Q b i1 i2 fenv,
    hl_Dan (atrueDan b P) i1 Q fenv ->
    hl_Dan (afalseDan b P) i2 Q fenv ->
    hl_Dan P (IF_Dan b i1 i2) Q fenv 
| hl_Dan_while :
  forall P b i fenv,
    hl_Dan (atrueDan b P) i P fenv ->
    hl_Dan P (WHILE_Dan b i) (afalseDan b P) fenv 
| hl_Dan_consequence :
  forall P Q P' Q' c fenv,
    hl_Dan P c Q fenv ->
    (P' -->> P) fenv->
    (Q -->> Q') fenv ->
    hl_Dan P' c Q' fenv.

Lemma Hoare_Dan_consequence_pre :
  forall P P' Q i fenv,
    hl_Dan P i Q fenv ->
    (P' -->> P) fenv ->
    hl_Dan P' i Q fenv.
Proof.
  intros.
  eapply hl_Dan_consequence; try apply H; unfold aimpDan; eauto. 
Qed.

Lemma Hoare_Dan_consequence_post :
  forall P Q Q' i fenv,
    hl_Dan P i Q fenv ->
    (Q -->> Q') fenv ->
    hl_Dan P i Q' fenv.
Proof.
  intros.
  eapply hl_Dan_consequence; try apply H; unfold aimpDan; eauto. 
Qed.

Lemma Hoare_Dan_ifthen :
  forall b i P Q fenv,
    hl_Dan (atrueDan b P) i Q fenv ->
    ((afalseDan b P) -->> Q) fenv ->
    hl_Dan P (IF_Dan b i SKIP_Dan) Q fenv.
Proof.
  intros. apply (hl_Dan_if P Q b i SKIP_Dan fenv); eauto.
  apply Hoare_Dan_consequence_pre with Q.
  - auto using hl_Dan_skip.
  - assumption.
Qed.

Lemma triple_Dan_skip : 
  forall P fenv, 
    triple_Dan P SKIP_Dan P fenv. 
Proof.
unfold triple_Dan. intros. inversion H. subst. eauto.
Qed.

Lemma triple_Dan_assign :
  forall P x a fenv,
  triple_Dan (subst_AbsEnv x a P) (ASSIGN_Dan x a) P fenv. 
Proof.
unfold triple_Dan. intros. inversion H. subst. 
pose proof (aupdate_subst_equiv P fenv dbenv nenv a n x H7 H0).
unfold aupdate in H1. apply H1. eauto.
Qed.

Lemma triple_Dan_seq :
  forall P Q R i1 i2 fenv,
    triple_Dan P i1 Q fenv ->
    triple_Dan Q i2 R fenv ->
    triple_Dan P (SEQ_Dan i1 i2) R fenv. 
Proof.
  unfold triple_Dan. intros.
  inversion H1. subst.  
  pose proof (H dbenv nenv nenv'0 H5 H2).
  pose proof (H0 dbenv nenv'0 nenv' H10 H3).
  eauto.   
Qed.

Lemma triple_Dan_ifthenelse :
  forall P Q b (i1 i2 : imp_Dan) fenv,
    triple_Dan (atrueDan b P) i1 Q fenv -> 
    triple_Dan (afalseDan b P) i2 Q fenv -> 
    triple_Dan P (IF_Dan b i1 i2) Q fenv. 
Proof.
  unfold triple_Dan. intros. inversion H1; subst.
  - pose proof (H dbenv nenv nenv' H11). apply H3.
    unfold atrueDan. apply AbsEnv_and; eauto.
    apply AbsEnv_leaf. apply Dan_lp_rel_bool.
    eapply RelUnaryProp. apply H10. eauto.
  - pose proof (H0 dbenv nenv nenv' H11). apply H3.
    unfold afalseDan. apply AbsEnv_and; eauto.
    apply AbsEnv_leaf. apply Dan_lp_rel_bool.
    eapply RelUnaryProp. apply H10. eauto.
Qed.

Lemma triple_Dan_while :
  forall P b l fenv,
  triple_Dan (atrueDan b P) l P fenv -> 
  triple_Dan P (WHILE_Dan b l) (afalseDan b P) fenv.
Proof.
  unfold triple_Dan. intros P b c fenv T db s s' E.
  dependent induction E; intros.
  - unfold afalseDan.  apply AbsEnv_and; eauto.
  apply AbsEnv_leaf. apply Dan_lp_rel_bool.
  eapply RelUnaryProp. apply H. eauto.
  - eapply IHE2; eauto. apply T with nenv; eauto. unfold atrueDan.
    apply AbsEnv_and; eauto.
    apply AbsEnv_leaf. apply Dan_lp_rel_bool.
    eapply RelUnaryProp. apply H. eauto.
Qed.

Lemma triple_Dan_consequence :
  forall P Q P' Q' i fenv,
    triple_Dan P i Q fenv ->
    (P' -->> P) fenv ->
    (Q -->> Q') fenv ->
    triple_Dan P' i Q' fenv. 
Proof.
  unfold triple_Dan, aimpDan; intros. eauto.
Qed.

Theorem Hoare_Dan_sound :
  forall P i Q fenv,
    hl_Dan P i Q fenv ->
    triple_Dan P i Q fenv. 
Proof.
  induction 1;
    eauto using triple_Dan_skip, triple_Dan_assign, triple_Dan_seq, triple_Dan_ifthenelse, triple_Dan_while, triple_Dan_consequence.
Qed.





