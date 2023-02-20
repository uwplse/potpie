From Coq Require Import List Bool Arith String Psatz Arith.PeanoNat Program.Equality.
From Coq Require Import Wellfounded FunctionalExtensionality.
Add LoadPath "./" as DanTrick.
Require Import DanTrick.DanTrickLanguage.

Local Open Scope dantrick_scope.

Definition assertion: Type := (list nat) -> nat_env -> Prop.

Inductive assertion_grammar : Type :=
|DanLogTrue
|DanLogFalse
|DanLogAnd (a1 a2 : assertion_grammar)
|DanLogOr (a1 a2 : assertion_grammar)
|DanLogNeg (a : assertion_grammar)
|DanLogLeq (a1 a2 :aexp_Dan). 

Definition ConstTrueAssert : assertion := fun dbenv nenv => True.
Definition ConstFalseAssert : assertion := fun dbenv nenv => False.

(* Copied from cdf-mech-sem HoareLogic.v *)
Definition aand (P Q: assertion) : assertion :=
  fun dbenv s => P dbenv s /\ Q dbenv s.

Definition aor (P Q: assertion) : assertion :=
  fun dbenv s => P dbenv s \/ Q dbenv s.

Definition anot (P : assertion) : assertion :=
  fun dbenv s => not (P dbenv s).

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp_Dan) (v: nat) (fenv: fun_env): assertion :=
  fun dbenv nenv => a_Dan a dbenv fenv nenv v.

Definition aparam (p: nat) (v: nat) : assertion :=
  fun dbenv nenv => nth_error dbenv p = Some v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp_Dan) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => b_Dan b dbenv fenv nenv true /\ P dbenv nenv.

Definition afalse (b: bexp_Dan) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => b_Dan b dbenv fenv nenv false /\ P dbenv nenv.

  Inductive dan_grammar_interp : assertion_grammar -> fun_env -> assertion -> Prop :=
  | true_interp:
    forall fenv (P : assertion),
    (forall dbenv nenv, (P dbenv nenv)) -> 
    dan_grammar_interp DanLogTrue fenv P
  | false_interp:
  forall fenv (P : assertion),
  (forall dbenv nenv, ~(P dbenv nenv)) -> 
    dan_grammar_interp DanLogFalse fenv P
  | and_interp:
    forall a1 a2 a1' a2' fenv, 
    dan_grammar_interp a1 fenv a1' ->
    dan_grammar_interp a2 fenv a2' -> 
    dan_grammar_interp (DanLogAnd a1 a2) fenv (aand a1' a2')
  |or_interp: 
    forall a1 a2 a1' a2' fenv, 
    dan_grammar_interp a1 fenv a1' ->
    dan_grammar_interp a2 fenv a2' -> 
    dan_grammar_interp (DanLogOr a1 a2) fenv (aor a1' a2')
  |neg_interp:
    forall a a' fenv, 
    dan_grammar_interp a fenv a' -> 
    dan_grammar_interp (DanLogNeg a) fenv (anot a')
  |leq_interp: 
    forall a1 a2 fenv, 
    dan_grammar_interp (DanLogLeq a1 a2) fenv (atrue (LEQ_Dan a1 a2) fenv ConstTrueAssert)
    . 

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp_Dan) (fenv: fun_env) (P: assertion) : assertion :=
  fun dbenv nenv => (forall n, a_Dan a dbenv fenv nenv n -> P dbenv (update x n nenv)). 
  

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall db s, P db s -> Q db s.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

Definition triple_Dan (P: assertion) (c: imp_Dan) (Q: assertion) (fenv: fun_env): Prop :=
  forall dbenv s s',  i_Dan c dbenv fenv s s'  -> P dbenv s -> Q dbenv s'.


Notation "{{ P }} c {{ Q }}" := (triple_Dan P c Q) (at level 90, c at next level).

Inductive hl_Dan : assertion -> imp_Dan -> assertion -> (list nat) -> fun_env -> Prop :=
| hl_dan_skip :
  forall P dbenv fenv,
    hl_Dan P SKIP_Dan P dbenv fenv
| hl_dan_assign :
  forall P x a dbenv fenv,
    hl_Dan (aupdate x a fenv P) (ASSIGN_Dan x a) P dbenv fenv 
| hl_dan_seq :
  forall P Q R c1 c2 dbenv fenv,
    hl_Dan P c1 Q dbenv fenv ->
    hl_Dan Q c2 R dbenv fenv ->
    hl_Dan P (SEQ_Dan c1 c2) R dbenv fenv
| hl_dan_ifthenelse :
  forall P Q b c1 c2 dbenv fenv,
    hl_Dan (atrue b fenv P) c1 Q dbenv fenv ->
    hl_Dan (afalse b fenv P) c2 Q dbenv fenv ->
    hl_Dan P (IF_Dan b c1 c2) Q dbenv fenv
| hl_dan_while :
  forall P b c dbenv fenv,
    hl_Dan (atrue b fenv P) c P dbenv fenv ->
    hl_Dan P (WHILE_Dan b c) (afalse b fenv P) dbenv fenv
| hl_dan_consequence :
  forall P Q P' Q' c dbenv fenv,
    hl_Dan P c Q dbenv fenv ->
    P' -->> P ->
    Q -->> Q' ->
    hl_Dan P' c Q' dbenv fenv.


Lemma Hoare_Dan_consequence_pre :
  forall P P' Q c dbenv fenv,
    hl_Dan P c Q dbenv fenv ->
    P' -->> P ->
    hl_Dan P' c Q dbenv fenv.
Proof.
  intros. apply hl_dan_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_Dan_consequence_post :
  forall P Q Q' c dbenv fenv,
    hl_Dan P c Q dbenv fenv ->
    Q -->> Q' ->
    hl_Dan P c Q' dbenv fenv.
Proof.
  intros. apply hl_dan_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_Dan_ifthen :
  forall b c P Q dbenv fenv,
    hl_Dan (atrue b fenv P) c Q dbenv fenv ->
    (afalse b fenv P) -->> Q ->
    hl_Dan P (IF_Dan b c SKIP_Dan) Q dbenv fenv.
Proof.
  intros. apply (hl_dan_ifthenelse P Q b c SKIP_Dan dbenv fenv); auto.
  apply Hoare_Dan_consequence_pre with Q. auto using hl_dan_skip.
  assumption.
Qed.


Local Open Scope string_scope.
Definition double_y :=
  ASSIGN_Dan "x" (PLUS_Dan (VAR_Dan "y") (VAR_Dan "y")) ;;
  ASSIGN_Dan "y" (VAR_Dan "x").

Local Open Scope nat_scope.

Definition while_loop (n: nat) :=
  ASSIGN_Dan "x" (CONST_Dan n) ;;
  ASSIGN_Dan "y" (CONST_Dan 0) ;;
  WHILE_Dan (LEQ_Dan (VAR_Dan "y") (VAR_Dan "x"))
        (ASSIGN_Dan "y" (PLUS_Dan (VAR_Dan "y") (CONST_Dan 1))).




Lemma triple_Dan_skip :
  forall P fenv,
    ({{P}} SKIP_Dan {{P}}) fenv.
Proof.
  unfold triple_Dan; intros. inversion H; subst.
  apply H0.  
Qed.

Lemma triple_skip_interp_sound :
  forall P_gram P fenv,
    dan_grammar_interp P_gram fenv P -> 
    ({{P}} SKIP_Dan {{P}}) fenv.
Proof.
  intros. apply triple_Dan_skip.  
Qed.

Lemma triple_Dan_assign :
  forall P x a fenv,
    {{aupdate x a fenv P}} ASSIGN_Dan x a {{P}} fenv.
Proof.
  unfold triple_Dan, aupdate. intros. inversion H; subst.
  apply (H0 n).
  assumption.   
Qed.

Ltac invc H :=
  inversion H; subst; clear H.

Lemma triple_Dan_seq :
  forall P Q R c1 c2 fenv,
    {{P}} c1 {{Q}} fenv ->
    {{Q}} c2 {{R}} fenv ->
    {{P}} c1;;c2 {{R}} fenv.
Proof.
  unfold triple_Dan; intros P Q R c1 c2 fenv PQ QR dbenv nenv' s' Hi_Dan PPR. invc Hi_Dan.
  eapply QR.
  eassumption.
  eapply PQ in H1. assumption.
  assumption.
Qed.

Lemma triple_Dan_ifthenelse :
  forall P Q b c1 c2 fenv,
    {{(atrue b fenv P)}} c1 {{Q}} fenv ->
    {{(afalse b fenv P)}} c2 {{Q}} fenv ->
    {{P}} IF_Dan b c1 c2 {{Q}} fenv .
Proof.
  unfold triple_Dan, atrue, afalse.
  intros. inversion H1; subst; [eapply H; [| split]; eassumption | eapply H0; [|split]; eassumption].
Qed.

Lemma triple_Dan_while :
  forall P b c fenv,
    {{atrue b fenv P}} c {{P}} fenv ->
    {{P}} WHILE_Dan b c {{afalse b fenv P}} fenv.
Proof.
  unfold triple_Dan. intros P b c fenv T db s s' E.
  dependent induction E; intros.
  - split. assumption. assumption. 
  - eapply IHE2; eauto. apply T with nenv; auto. unfold atrue; split; assumption.
Qed.

Lemma triple_Dan_consequence :
  forall P Q P' Q' c fenv,
    {{P}} c {{Q}} fenv ->
    P' -->> P ->
    Q -->> Q' ->
    {{P'}} c {{Q'}} fenv.
Proof.
  unfold triple_Dan, aimp; intros. eauto.
Qed.

Theorem Hoare_Dan_sound :
  forall P c Q db fenv,
    hl_Dan P c Q db fenv -> {{P}} c {{Q}} fenv.
Proof.
  induction 1;
    eauto using triple_Dan_skip, triple_Dan_assign, triple_Dan_seq, triple_Dan_ifthenelse, triple_Dan_while, triple_Dan_consequence.
Qed.

(* Weakest preconditions *)

Definition wp (c: imp_Dan) (Q: assertion) (fenv: fun_env) : assertion :=
  fun db s => forall s', i_Dan c db fenv s s' -> Q db s'.

Lemma wp_precondition :
  forall c Q fenv,
    {{wp c Q fenv}} c {{Q}} fenv.
Proof.
  unfold triple_Dan, wp; intros. auto.
Qed.

Lemma wp_weakest :
  forall P c Q fenv,
    {{P}} c {{Q}} fenv -> P -->> wp c Q fenv.
Proof.
  unfold triple_Dan, wp, aimp; intros. eauto.
Qed.

Lemma Hoare_Dan_wp :
  forall c Q dbenv fenv,
    hl_Dan (wp c Q fenv) c Q dbenv fenv.
Proof.
  induction c; intros Q db fenv.
  - apply hl_dan_ifthenelse.
    + eapply Hoare_Dan_consequence_pre. apply IHc1.
      unfold aand, atrue, aimp, wp; intros.
      destruct H. apply H1.
      apply Dan_if_true; assumption.
    + eapply Hoare_Dan_consequence_pre. apply IHc2.
      unfold aand, wp, aimp, afalse; intros.
      destruct H. apply H1. apply Dan_if_false; assumption.
  - eapply Hoare_Dan_consequence_pre. apply hl_dan_skip.
    unfold aimp, wp; intros.
    apply H. apply Dan_skip.
  - eapply Hoare_Dan_consequence_post.
    + eapply hl_dan_while.
      eapply Hoare_Dan_consequence_pre. apply IHc.
      unfold atrue, aand, aimp, wp; intros.
      destruct H. apply H2.
      apply Dan_while_step with (nenv' := s'); assumption.
    + unfold afalse, wp, aimp; intros. unfold aand in H. destruct H.
      apply H0. apply Dan_while_done. assumption.
  - eapply Hoare_Dan_consequence_pre. apply hl_dan_assign.
    unfold wp, aimp, aupdate; intros. eapply H. apply Dan_assign. assumption. 
  - eapply Hoare_Dan_consequence_pre. apply hl_dan_seq with (wp c2 Q fenv); eauto.
    unfold wp, aimp; intros. eapply H.
    apply Dan_seq with (i1:= c1) (i2 := c2) (nenv := s) (nenv' := s') (nenv'' := s'0);
      assumption.
Qed.

Theorem Hoare_Dan_complete :
  forall P c Q db fenv,
    {{P}} c {{Q}} fenv -> hl_Dan P c Q db fenv.
Proof.
  intros. apply Hoare_Dan_consequence_pre with (wp c Q fenv).
  - apply Hoare_Dan_wp.
  - apply wp_weakest; auto.
Qed.

Lemma triple_Dan_conj :
  forall c P1 Q1 P2 Q2 fenv,
    {{P1}} c {{Q1}} fenv -> {{P2}} c {{Q2}} fenv -> {{P1 //\\ P2}} c {{Q1 //\\ Q2}} fenv.
Proof.
  intros; red; intros. destruct H2 as [PRE1 PRE2].
  split; eauto.
Qed.

Lemma triple_Dan_disj :
  forall c P1 Q1 P2 Q2 fenv,
    {{P1}} c {{Q1}} fenv -> {{P2}} c {{Q2}} fenv -> {{P1 \\// P2}} c {{Q1 \\// Q2}} fenv.
Proof.
  intros; red; intros. destruct H2 as [PRE1|PRE2]; [left|right]; eauto.
Qed.

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (db: list nat) (s: nat_env) => exists (a: A), P a db s.

Lemma triple_Dan_assign_fwd :
  forall x a P fenv,
    {{ P }} ASSIGN_Dan x a {{ 
      aexists 
        (fun (m: nat) => 
         aexists 
          (fun (n: nat) => 
           (aequal (VAR_Dan x) n fenv) //\\ 
           (aupdate x (CONST_Dan m) fenv (P //\\
           aequal a n fenv)))) }} fenv.
Proof.
  intros. unfold triple_Dan, aequal, aupdate; intros.
  inversion H; subst.
  exists (s x).  exists (n); cbn.
  split. f_equal. apply Dan_var. apply update_same.
  intros.
  unfold aand; split; inversion H1; subst;
    (replace (update x (s x) (update x n s)) with s;
     [| unfold update; apply functional_extensionality; intros y; destruct (string_dec x y);
        [f_equal|]; auto]);
    auto.
Qed.

Fixpoint modified_by (c: imp_Dan) (x: ident) : Prop :=
  match c with
  | SKIP_Dan => False
  | ASSIGN_Dan y a => x = y
  | SEQ_Dan c1 c2 => modified_by c1 x \/ modified_by c2 x
  | IF_Dan b c1 c2 => modified_by c1 x \/ modified_by c2 x
  | WHILE_Dan b c1 => modified_by c1 x
  end.

Lemma i_Dan_modified :
  forall  c x db fenv nenv nenv',
    i_Dan c db fenv nenv nenv' -> ~modified_by c x -> nenv' x = nenv x.
Proof.
  induction 1; cbn; intros MB.
  - auto.
  - apply IHi_Dan. unfold not in MB.
    unfold not. intros. assert (modified_by i1 x \/ modified_by i2 x) as Hdisj by (left; assumption).
    apply MB in Hdisj. assumption.
  - apply IHi_Dan. unfold not in MB. unfold not. intros. assert (modified_by i1 x \/ modified_by i2 x) as Hdisj by (right; assumption).
    apply MB in Hdisj. assumption.
  - apply update_other. unfold not. intros Hx0x. unfold not in MB. symmetry in Hx0x. apply MB in Hx0x.
    assumption.
  - auto.
  - rewrite IHi_Dan2, IHi_Dan1 by tauto. auto.
  - rewrite IHi_Dan2, IHi_Dan1 by tauto. auto.
Qed.


Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall db s1 s2,
  (forall x, ~ vars x -> s1 x = s2 x) ->
  (P db s1 <-> P db s2).

(** In the end, we obtain the following frame rule. *)

Lemma triple_frame:
  forall c P Q R fenv,
  {{P}} c {{Q}} fenv ->
  independent_of R (modified_by c) ->
  {{P //\\ R}} c {{Q //\\ R}} fenv.
Proof.
  intros; red; intros. destruct H2 as [PRE1 PRE2]. split.
  - eapply H; eauto.
  - apply (H0 dbenv s' s).
    + intros. eapply i_Dan_modified with c dbenv fenv; auto.
    + auto.
Qed.
