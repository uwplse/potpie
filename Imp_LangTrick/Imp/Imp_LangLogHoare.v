From Coq Require Import List String Arith Program.Equality.

From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogProp Imp_LangLogSubst LogicProp
Imp_LangLogicHelpers.

Definition triple_Imp_Lang (P: AbsEnv) (i: imp_Imp_Lang) (Q: AbsEnv) (fenv: fun_env) : Prop :=
  forall dbenv nenv nenv', 
  i_Imp_Lang i dbenv fenv nenv nenv' ->
  AbsEnv_rel P fenv dbenv nenv -> 
  AbsEnv_rel Q fenv dbenv nenv'.
  
Definition atrueImp_Lang (b: bexp_Imp_Lang) (P: AbsEnv): AbsEnv :=
  (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _
                                            (fun bval => bval = true)
                                            b)))).

Definition afalseImp_Lang (b: bexp_Imp_Lang) (P: AbsEnv): AbsEnv :=
  (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _
                                            (fun bval => bval = false)
                                            b)))).

Definition aimpImp_Lang (P Q: AbsEnv) (fenv: fun_env): Prop :=
  forall dbenv nenv,
    AbsEnv_rel P fenv dbenv nenv -> AbsEnv_rel Q fenv dbenv nenv. 

Definition aandImp_Lang (P Q: assertion): assertion :=
  fun dbenv nenv => P dbenv nenv /\ Q dbenv nenv.

Definition implication_env := list (AbsEnv * AbsEnv). 

Definition fact_env_valid (fact_env : implication_env) fenv :=
  forall P Q, 
  List.In (P, Q) fact_env ->
  aimpImp_Lang P Q fenv. 

Inductive hl_Imp_Lang : 
forall (P : AbsEnv) (i: imp_Imp_Lang) (Q: AbsEnv) (facts: implication_env) (fenv: fun_env), Type :=
| hl_Imp_Lang_skip :
  forall P fact_env fenv,
    hl_Imp_Lang P SKIP_Imp_Lang P fact_env fenv
| hl_Imp_Lang_assign :
  forall P fact_env fenv x a,
    hl_Imp_Lang (subst_AbsEnv x a P) (ASSIGN_Imp_Lang x a) P fact_env fenv
| hl_Imp_Lang_seq :
  forall P Q R fact_env fenv i1 i2,
    hl_Imp_Lang P i1 R fact_env fenv ->
    hl_Imp_Lang R i2 Q fact_env fenv ->
    hl_Imp_Lang P (SEQ_Imp_Lang i1 i2) Q fact_env fenv
| hl_Imp_Lang_if :
  forall P Q b i1 i2 fact_env fenv,
    hl_Imp_Lang (atrueImp_Lang b P) i1 Q fact_env fenv ->
    hl_Imp_Lang (afalseImp_Lang b P) i2 Q fact_env fenv ->
    hl_Imp_Lang P (IF_Imp_Lang b i1 i2) Q fact_env fenv 
| hl_Imp_Lang_while :
  forall P b i fact_env fenv,
    hl_Imp_Lang (atrueImp_Lang b P) i P fact_env fenv ->
    hl_Imp_Lang P (WHILE_Imp_Lang b i) (afalseImp_Lang b P) fact_env fenv
| hl_Imp_Lang_consequence_pre :
  forall P Q P' c n fact_env fenv,
    hl_Imp_Lang P c Q fact_env fenv ->
    List.nth_error fact_env n = Some (P', P) ->
    aimpImp_Lang P' P fenv ->
    hl_Imp_Lang P' c Q fact_env fenv
| hl_Imp_Lang_consequence_post :
  forall P Q Q' c n fact_env fenv,
    hl_Imp_Lang P c Q fact_env fenv ->
    List.nth_error fact_env n = Some (Q, Q') ->
    aimpImp_Lang Q Q' fenv ->
    hl_Imp_Lang P c Q' fact_env fenv. 
    (* (P' -->> P) fenv->
    (Q -->> Q') fenv ->
    hl_Imp_Lang P' c Q' fenv. *)
(* | hl_Imp_Lang_consequence_and1 :
  forall P Q R i fact_env fenv,
    fact_env_valid fact_env fenv ->
    hl_Imp_Lang P i Q fact_env fenv ->
    hl_Imp_Lang (Imp_Lang_and_log P R) i Q fact_env fenv
| hl_Imp_Lang_and2 :
  forall P Q R i fact_env fenv,
    fact_env_valid fact_env fenv ->
    hl_Imp_Lang P i Q fact_env fenv ->
    hl_Imp_Lang (Imp_Lang_and_log R P) i Q fact_env fenv
| hl_Imp_Lang_consequence_or1 :
  forall P Q R i fact_env fenv,
    fact_env_valid fact_env fenv ->
    hl_Imp_Lang P i Q fact_env fenv ->
    hl_Imp_Lang P i (Imp_Lang_or_log Q R) fact_env fenv
| hl_Imp_Lang_consequence_or2 :
  forall P Q R i fact_env fenv,
    fact_env_valid fact_env fenv ->
    hl_Imp_Lang P i Q fact_env fenv ->
    hl_Imp_Lang P i (Imp_Lang_or_log R Q) fact_env fenv
| hl_Imp_Lang_consequence_fun_pre :
  forall P Q P' Q' R n fact_env fenv (f: fun_Imp_Lang)
    (args: list aexp_Imp_Lang) (fun_body: imp_Imp_Lang) i,
    fact_env_valid fact_env fenv ->
    List.nth_error fact_env n = Some (P,f,Q) ->
    log_subst P f args P' ->
    log_subst Q f args Q' ->
    fun_precondition_implies_termination P f fenv args ->
    fun_precondition_implies_args_terminate P P' f fenv args ->
    fenv (Name f) = f ->
    hl_Imp_Lang Q' i R fact_env fenv ->
    hl_Imp_Lang P' i R fact_env fenv
| hl_Imp_Lang_consequence_fun_post :   
    forall P Q P' Q' R n fact_env fenv (f: fun_Imp_Lang)
    (args: list aexp_Imp_Lang) (fun_body: imp_Imp_Lang) i,
    fact_env_valid fact_env fenv ->
    List.nth_error fact_env n = Some (P,f,Q) ->
    log_subst P f args P' ->
    log_subst Q f args Q' ->
    fun_precondition_implies_termination P f fenv args ->
    fun_precondition_implies_args_terminate P P' f fenv args ->
    fenv (Name f) = f ->
    hl_Imp_Lang R i P' fact_env fenv ->
    hl_Imp_Lang R i Q' fact_env fenv *)
(* | hl_Imp_Lang_consequence_fun_pre :
  forall P Q P' Q' R fenv (f: fun_Imp_Lang) (args: list aexp_Imp_Lang) (fun_body: imp_Imp_Lang) i,
    hl_Imp_Lang P fun_body Q fenv ->
    (Body f) = fun_body ->
    pre_admissible_log f P ->
    post_admissible_log f Q ->
    log_subst P f args P' ->
    log_subst Q f args Q' ->
    fun_precondition_implies_termination P f fenv args ->
    fun_precondition_implies_args_terminate P P' f fenv args ->
    fenv (Name f) = f ->
    hl_Imp_Lang Q' i R fenv ->
    hl_Imp_Lang P' i R fenv *)
(* | hl_Imp_Lang_consequence_fun_post :
  forall (P Q R Q' R': AbsEnv) (fenv: fun_env) (f: fun_Imp_Lang) (args: list aexp_Imp_Lang) (fun_body: imp_Imp_Lang) i,
    hl_Imp_Lang Q fun_body R fenv ->
    (Body f) = fun_body ->
    pre_admissible_log f Q ->
    post_admissible_log f R ->
    log_subst Q f args Q' ->
    log_subst R f args R' ->
    fun_precondition_implies_termination Q f fenv args ->
    fun_precondition_implies_args_terminate Q Q' f fenv args ->
    fenv (Name f) = f ->
    hl_Imp_Lang P i Q' fenv ->
    hl_Imp_Lang P i R' fenv. *)

(* Lemma Hoare_Imp_Lang_ifthen : *)
(*   forall b i P Q fenv, *)
(*     hl_Imp_Lang (atrueImp_Lang b P) i Q fenv -> *)
(*     ((afalseImp_Lang b P) -->> Q) fenv -> *)
(*     hl_Imp_Lang P (IF_Imp_Lang b i SKIP_Imp_Lang) Q fenv. *)
(* Proof. *)


Lemma triple_Imp_Lang_skip : 
  forall P fenv, 
    triple_Imp_Lang P SKIP_Imp_Lang P fenv. 
Proof.
unfold triple_Imp_Lang. intros. inversion H. subst. eauto.
Qed.

Lemma triple_Imp_Lang_assign :
  forall P x a fenv,
  triple_Imp_Lang (subst_AbsEnv x a P) (ASSIGN_Imp_Lang x a) P fenv. 
Proof.
unfold triple_Imp_Lang. intros. inversion H. subst. 
pose proof (aupdate_subst_equiv P fenv dbenv nenv a n x H7 H0).
unfold aupdate in H1. apply H1. eauto.
Qed.

Lemma triple_Imp_Lang_seq :
  forall P Q R i1 i2 fenv,
    triple_Imp_Lang P i1 Q fenv ->
    triple_Imp_Lang Q i2 R fenv ->
    triple_Imp_Lang P (SEQ_Imp_Lang i1 i2) R fenv. 
Proof.
  unfold triple_Imp_Lang. intros.
  inversion H1. subst.  
  pose proof (H dbenv nenv nenv'0 H5 H2).
  pose proof (H0 dbenv nenv'0 nenv' H10 H3).
  eauto.   
Qed.

Lemma triple_Imp_Lang_ifthenelse :
  forall P Q b (i1 i2 : imp_Imp_Lang) fenv,
    triple_Imp_Lang (atrueImp_Lang b P) i1 Q fenv -> 
    triple_Imp_Lang (afalseImp_Lang b P) i2 Q fenv -> 
    triple_Imp_Lang P (IF_Imp_Lang b i1 i2) Q fenv. 
Proof.
  unfold triple_Imp_Lang; intros.
  inversion H1; subst.
  - eapply H.
    eassumption. econstructor.
    eassumption.
    repeat econstructor.
    assumption.
  - eapply H0; try eassumption.
    econstructor; try eassumption; repeat econstructor.
    eassumption.
Qed.

Lemma triple_Imp_Lang_while :
  forall P b l fenv,
  triple_Imp_Lang (atrueImp_Lang b P) l P fenv -> 
  triple_Imp_Lang P (WHILE_Imp_Lang b l) (afalseImp_Lang b P) fenv.
Proof.
  unfold triple_Imp_Lang; intros P b l fenv TRUE.
  intros dbenv nenv nenv' IIMP_LANG.
  dependent induction IIMP_LANG; intros.
  - econstructor; try eassumption.
    repeat econstructor.
    assumption.
  - 
    eapply IHIIMP_LANG2.
    eassumption.
    reflexivity.
    eapply TRUE. eassumption. econstructor. eassumption. repeat econstructor. eassumption.
Qed.

(* Lemma triple_Imp_Lang_consequence_fun_pre :
    forall P Q P' Q' R n fact_env fenv (f: fun_Imp_Lang)
    (args: list aexp_Imp_Lang) (fun_body: imp_Imp_Lang) i,
    fact_env_valid fact_env fenv ->
    List.nth_error fact_env n = Some (P,f,Q) ->
    log_subst P f args P' ->
    log_subst Q f args Q' ->
    fun_precondition_implies_termination P f fenv args ->
    fun_precondition_implies_args_terminate P P' f fenv args ->
    fenv (Name f) = f ->
    triple_Imp_Lang Q' i R fenv ->
    triple_Imp_Lang P' i R fenv.
Proof.
  unfold triple_Imp_Lang; intros P Q P' Q' R n fact_env fenv f args fun_body i.
  (* intros TRIPLE_FUN BODY PRE_ADMIT POST_ADMIT SUBSTP SUBSTQ FUNTERM ARGSTERM NAME TRIPLE. *)
  (* intros dbenv nenv nenv' IIMP_LANG RELP'. *)
  intros faenv_valid nthfact substp substq funterm argsterm name triple. 
  intros dbenv nenv nenv' iexe relp'. 
  unfold fact_env_valid in faenv_valid.
  pose proof nth_error_In fact_env n nthfact as withinfactenv. 
  specialize (faenv_valid P f Q fun_body withinfactenv name).
  destruct faenv_valid; destruct H0; destruct H1.   
  pose proof (FUN_FACTS := fun_fact_other'').
  specialize (FUN_FACTS P Q fenv f args P' Q' (Name f)).
  unfold Imp_LangLogHoare.aimpImp_Lang, Imp_LangLogHoare.triple_Imp_Lang in FUN_FACTS.
  specialize (FUN_FACTS H H0 substp substq name (eq_refl (Name f))).
  eapply triple. eassumption. eapply FUN_FACTS; try eassumption. 
  intros. eapply H2; try eassumption. 
  rewrite <- H1; eassumption. 
Qed.

Lemma triple_Imp_Lang_consequence_fun_post :
    forall P Q P' Q' R n fact_env fenv (f: fun_Imp_Lang)
    (args: list aexp_Imp_Lang) (fun_body: imp_Imp_Lang) i,
    fact_env_valid fact_env fenv ->
    List.nth_error fact_env n = Some (P,f,Q) ->
    log_subst P f args P' ->
    log_subst Q f args Q' ->
    fun_precondition_implies_termination P f fenv args ->
    fun_precondition_implies_args_terminate P P' f fenv args ->
    fenv (Name f) = f ->
    triple_Imp_Lang R i P' fenv ->
    triple_Imp_Lang R i Q' fenv. 
Proof.
  unfold triple_Imp_Lang; intros P Q P' Q' R n fact_env fenv f args fun_body i.
  (* intros TRIPLE_FUN BODY PRE_ADMIT POST_ADMIT SUBSTP SUBSTQ FUNTERM ARGSTERM NAME TRIPLE. *)
  (* intros dbenv nenv nenv' IIMP_LANG RELP'. *)
  intros faenv_valid nthfact substp substq funterm argsterm name triple. 
  intros dbenv nenv nenv' iexe relp'. 
  unfold fact_env_valid in faenv_valid.
  pose proof nth_error_In fact_env n nthfact as withinfactenv. 
  specialize (faenv_valid P f Q fun_body withinfactenv name).
  destruct faenv_valid; destruct H0; destruct H1.   
  pose proof (FUN_FACTS := fun_fact_other'').
  specialize (FUN_FACTS P Q fenv f args P' Q' (Name f)).
  unfold Imp_LangLogHoare.aimpImp_Lang, Imp_LangLogHoare.triple_Imp_Lang in FUN_FACTS.
  specialize (FUN_FACTS H H0 substp substq name (eq_refl (Name f))).
  eapply FUN_FACTS; try eassumption. 
  intros. eapply H2; try eassumption. 
  rewrite <- H1; eassumption.
  eapply triple; eassumption.   
Qed. *)


Lemma triple_Imp_Lang_consequence_pre : 
  forall P Q P' c n fact_env fenv,
    triple_Imp_Lang P c Q fenv ->
    List.nth_error fact_env n = Some (P', P) ->
    aimpImp_Lang P' P fenv ->
    triple_Imp_Lang P' c Q fenv.
Proof. 
  unfold triple_Imp_Lang, aimpImp_Lang in *. intros.
  apply (H dbenv nenv nenv' H2).
  apply H1. assumption.   
Qed. 


(* forall P Q Q' c n fact_env fenv,
fact_env_valid fact_env fenv ->
hl_Imp_Lang P c Q fact_env fenv ->
List.nth_error fact_env n = Some (Q, Q') ->
hl_Imp_Lang P c Q' fact_env fenv.  *)
Lemma triple_Imp_Lang_consequence_post : 
  forall P Q Q' c n fact_env fenv,
    triple_Imp_Lang P c Q fenv ->
    List.nth_error fact_env n = Some (Q, Q') ->
    aimpImp_Lang Q Q' fenv ->
    triple_Imp_Lang P c Q' fenv.
Proof.
  unfold triple_Imp_Lang, aimpImp_Lang in *. intros.
  specialize (H dbenv nenv nenv' H2 H3).
  apply H1. assumption.   
Qed. 
Theorem Hoare_Imp_Lang_sound :
  forall P i Q fact_env fenv,
    hl_Imp_Lang P i Q fact_env fenv ->
    triple_Imp_Lang P i Q fenv. 
Proof.
  induction 1;
    eauto using triple_Imp_Lang_skip, triple_Imp_Lang_assign, triple_Imp_Lang_seq, triple_Imp_Lang_ifthenelse, triple_Imp_Lang_while, triple_Imp_Lang_consequence_pre, triple_Imp_Lang_consequence_post.
Qed.
