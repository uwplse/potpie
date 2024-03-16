From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick.Stack Require Import StackLanguage StackLogicBase StackFrame StackExprWellFormed.

Require Import Imp_LangTrick.LogicProp.LogicProp.
Require Export Imp_LangTrick.Stack.StackPurestBase.


Definition P_preserves_purity (n: nat) (a a': aexp_stack): Prop :=
  forall fenv,
    aexp_stack_pure_rel a fenv ->
    aexp_stack_pure_rel a' fenv.

Definition P0_preserves_purity (n: nat) (l l': list aexp_stack): Prop :=
  forall fenv,
    args_stack_pure_rel l fenv ->
    args_stack_pure_rel l' fenv.

Lemma aexp_args_size_inc_preserves_purity :
  aexp_args_size_inc_rel_mut_ind_theorem P_preserves_purity P0_preserves_purity.
Proof.
  aexp_args_size_inc_rel_mutual_induction P P0 P_preserves_purity P0_preserves_purity; intros.
  - assumption.
  - invs H. constructor. intuition.
  - invs H1. constructor.
    + apply H. assumption.
    + apply H0. assumption.
  - invs H1. constructor.
    + apply H. assumption.
    + apply H0. assumption.
  - inversion H0.
    revert H3. subst.
    econstructor.
    + eassumption.
    + apply H. assumption.
    + assumption.
    + assumption.
    + assumption.
  - assumption.
  - invs H1.
    constructor.
    + apply H. assumption.
    + apply H0. assumption.
Qed.

Lemma expr_purity_implies_well_formed :
  (forall (a : aexp_stack) (fenv: fun_env_stk),
      aexp_stack_pure_rel a fenv ->
      aexp_well_formed a)
  /\ (forall (b: bexp_stack) (fenv: fun_env_stk),
        bexp_stack_pure_rel b fenv ->
        bexp_well_formed b)
  /\ (forall (args: list aexp_stack) (fenv: fun_env_stk),
        args_stack_pure_rel args fenv ->
        args_well_formed args).
Proof.
  pose (fun (a: aexp_stack) (fenv: fun_env_stk) =>
        fun (_: aexp_stack_pure_rel a fenv) =>
          aexp_well_formed a) as P.
  pose (fun (b: bexp_stack) (fenv: fun_env_stk) =>
        fun (_: bexp_stack_pure_rel b fenv) =>
          bexp_well_formed b) as P0.
  pose (fun (args: list aexp_stack) (fenv: fun_env_stk) =>
        fun (_: args_stack_pure_rel args fenv) =>
          args_well_formed args) as P1.
  apply (pure_stack_mut_ind P P0 P1); intros; unfold P, P0, P1 in *.
  - econstructor.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor. eassumption.
  - econstructor.
  - econstructor.
  - econstructor. assumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor.
  - econstructor; eassumption.
Qed.

Lemma aexp_purity_implies_well_formed :
  (forall (a : aexp_stack) (fenv: fun_env_stk),
      aexp_stack_pure_rel a fenv ->
      aexp_well_formed a).
Proof.
  pose proof (expr_purity_implies_well_formed) as H.
  destruct H as (AEXP & _).
  eapply AEXP.
Qed.

Lemma bexp_purity_implies_well_formed :
  forall (b: bexp_stack) (fenv: fun_env_stk),
        bexp_stack_pure_rel b fenv ->
        bexp_well_formed b.
Proof.
  pose proof (expr_purity_implies_well_formed) as H.
  destruct H as (_ & BEXP & _).
  apply BEXP.
Qed.

Lemma args_purity_implies_well_formed :
  forall (args: list aexp_stack) (fenv: fun_env_stk),
    args_stack_pure_rel args fenv ->
    args_well_formed args.
Proof.
  pose proof (expr_purity_implies_well_formed) as H.
  destruct H as (_ & _ & ARGS).
  apply ARGS.
Qed.


Definition P_preserves_purity' (n: nat) (a a': aexp_stack): Prop :=
  aexp_well_formed a ->
  forall fenv,
    aexp_stack_pure_rel a' fenv ->
    aexp_stack_pure_rel a fenv.

Definition P0_preserves_purity' (n: nat) (l l': list aexp_stack): Prop :=
  args_well_formed l ->
  forall fenv,
    args_stack_pure_rel l' fenv ->
    args_stack_pure_rel l fenv.

Lemma aexp_args_size_inc_preserves_purity' :
  aexp_args_size_inc_rel_mut_ind_theorem P_preserves_purity' P0_preserves_purity'.
Proof.
  aexp_args_size_inc_rel_mutual_induction P P0 P_preserves_purity' P0_preserves_purity'; intros.
  - assumption.
  - invs H. constructor. assumption.
  - invs H2. constructor.
    + eapply H.
      * invs H1. assumption.
      * assumption.
    + invs H1. apply H0; assumption.
  - invs H1. invs H2. constructor; [eapply H | eapply H0]; assumption.
  - invs H0. inversion H1.
    econstructor; try eassumption; try eapply H; eassumption.
  - assumption.
  - invc H1. invc H2.
    econstructor; [eapply H | eapply H0]; assumption.
Qed.



Lemma aexp_size_inc_preserves_purity :
  forall a a' n fenv,
    aexp_stk_size_inc_rel n a a' ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_pure_rel a' fenv.
Proof.
  pose proof (aexp_args_size_inc_preserves_purity).
  unfold aexp_args_size_inc_rel_mut_ind_theorem, P_preserves_purity, P0_preserves_purity in H.
  destruct H as (AEXP & _).
  intros.
  eapply AEXP; eassumption.
Qed.

Lemma aexp_size_inc_preserves_purity' :
  forall a a' n fenv,
    aexp_stk_size_inc_rel n a a' ->
    aexp_well_formed a ->
    aexp_stack_pure_rel a' fenv ->
    aexp_stack_pure_rel a fenv.
Proof.
  pose proof (aexp_args_size_inc_preserves_purity').
  unfold aexp_args_size_inc_rel_mut_ind_theorem, P_preserves_purity', P0_preserves_purity' in H.
  destruct H as (AEXP & _).
  intros.
  eapply AEXP; eassumption.
Qed.


Lemma args_size_inc_preserves_purity :
  forall args args' n fenv,
    args_stk_size_inc_rel n args args' ->
    args_stack_pure_rel args fenv ->
    args_stack_pure_rel args' fenv.
Proof.
  pose proof (aexp_args_size_inc_preserves_purity).
  unfold aexp_args_size_inc_rel_mut_ind_theorem, P_preserves_purity, P0_preserves_purity in H.
  destruct H as (_ & ARGS).
  intros. eapply ARGS; eassumption.
Qed.

Lemma args_size_inc_preserves_purity' :
  forall args args' n fenv,
    args_stk_size_inc_rel n args args' ->
    args_well_formed args ->
    args_stack_pure_rel args' fenv ->
    args_stack_pure_rel args fenv.
Proof.
  pose proof (aexp_args_size_inc_preserves_purity').
  unfold aexp_args_size_inc_rel_mut_ind_theorem, P_preserves_purity', P0_preserves_purity' in H.
  destruct H as (_ & ARGS).
  intros. eapply ARGS; eassumption.
Qed.




Lemma bexp_size_inc_preserves_purity :
  forall b b' n fenv,
    bexp_stk_size_inc_rel n b b' ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_pure_rel b' fenv.
Proof.
  induction 1; intros;
    match goal with
    | [ H : bexp_stack_pure_rel ?b _ |- _ ] =>
        invs H
    end; try assumption; econstructor.
  - eapply IHbexp_stk_size_inc_rel. assumption.
  - eapply IHbexp_stk_size_inc_rel1; assumption.
  - eapply IHbexp_stk_size_inc_rel2; assumption.
  - eapply IHbexp_stk_size_inc_rel1; assumption.
  - apply IHbexp_stk_size_inc_rel2; assumption.
  - eapply aexp_size_inc_preserves_purity; eassumption.
  - eapply aexp_size_inc_preserves_purity; eassumption.
  - eapply aexp_size_inc_preserves_purity; eassumption.
  - eapply aexp_size_inc_preserves_purity; eassumption.
Qed.

Lemma bexp_size_inc_preserves_purity' :
  forall b b' n fenv,
    bexp_stk_size_inc_rel n b b' ->
    bexp_well_formed b ->
    bexp_stack_pure_rel b' fenv ->
    bexp_stack_pure_rel b fenv.
Proof.
  induction 1; intros;
    match goal with
    | [ H : bexp_stack_pure_rel ?b _ |- _ ] =>
        invs H
    end;
    match goal with
    | [ H : bexp_well_formed ?b |- _ ] =>
        invs H
    end;
    try assumption; econstructor;
    try (eapply aexp_size_inc_preserves_purity'; eassumption).
  - eapply IHbexp_stk_size_inc_rel; eassumption.
  - eapply IHbexp_stk_size_inc_rel1; eassumption.
  - eapply IHbexp_stk_size_inc_rel2; eassumption.
  - eapply IHbexp_stk_size_inc_rel1; eassumption.
  - eapply IHbexp_stk_size_inc_rel2; eassumption.
Qed.


Definition bexp_pure_rel (fenv: fun_env_stk): bexp_unary_rel :=
  fun boolexpr : bexp_stack =>
    bexp_stack_pure_rel boolexpr fenv.

Definition aexp_pure_rel (fenv: fun_env_stk): aexp_unary_rel :=
  fun natexpr : aexp_stack =>
    aexp_stack_pure_rel natexpr fenv.

Definition bool_prop_pure (fenv: fun_env_stk): StkBoolProp -> Prop :=
  prop_rel (V := bool) (bexp_pure_rel fenv).

Definition nat_prop_pure (fenv: fun_env_stk): StkNatProp -> Prop :=
  prop_rel (V := nat) (aexp_pure_rel fenv).

Definition bool_prop_stk_size_inc (n: nat): StkBoolProp -> StkBoolProp -> Prop :=
  bool_binary_prop_rel (bexp_stk_size_inc_rel n).

Definition nat_prop_stk_size_inc (n: nat): StkNatProp -> StkNatProp -> Prop :=
  nat_binary_prop_rel (aexp_stk_size_inc_rel n).

Definition nat_prop_wf: StkNatProp -> Prop :=
  nat_prop_rel aexp_well_formed.

Definition bool_prop_wf: StkBoolProp -> Prop :=
  bool_prop_rel bexp_well_formed.

Definition bool_prop_args_wf: list bexp_stack -> Prop :=
  bool_prop_args_rel bexp_well_formed.

Definition nat_prop_args_wf: list aexp_stack -> Prop :=
  nat_prop_args_rel aexp_well_formed.

Lemma bool_prop_args_rel_prop_stk_inc_preserves_purity :
  forall args args' fenv n,
    prop_args_rel (V := bool) (fun boolexpr: bexp_stack => bexp_stack_pure_rel boolexpr fenv) args ->
    transformed_prop_exprs_args (V := bool) (bexp_stk_size_inc_rel n) args args' ->
    prop_args_rel (V := bool) (fun boolexpr: bexp_stack => bexp_stack_pure_rel boolexpr fenv) args'.
Proof.
  induction args; intros ? ? ? PURE INC; invs INC; try invs PURE.
  - assumption.
  - constructor.
    eapply bexp_size_inc_preserves_purity; eassumption.
    eapply IHargs; eassumption.
Qed.

Lemma bool_prop_args_rel_prop_stk_inc_preserves_purity'_folded :
  forall args' args fenv n,
    prop_args_rel (V := bool) (fun boolexpr: bexp_stack => bexp_stack_pure_rel boolexpr fenv) args' ->
    bool_prop_args_wf args ->
    transformed_prop_exprs_args (V := bool) (bexp_stk_size_inc_rel n) args args' ->
    prop_args_rel (V := bool) (fun boolexpr: bexp_stack => bexp_stack_pure_rel boolexpr fenv) args.
Proof.
  unfold bool_prop_args_wf. unfold_prop_helpers.
  induction args'; intros ? ? ? PURE WF INC; invs INC; try invs PURE.
  - assumption.
  - constructor.
    invs WF.
    eapply bexp_size_inc_preserves_purity'; eassumption.
    eapply IHargs'.
    assumption.
    invs WF. assumption. eassumption.
Qed.

Lemma anon_function_implies_well_formed :
  forall args,
    bool_prop_args_wf args <-> prop_args_rel (V := bool) (fun b: bexp_stack => bexp_well_formed b) args.
Proof.
  induction args; split; intros.
  - constructor.
  - constructor.
  - destruct IHargs.
    constructor.
    invs H.
    assumption.
    eapply H0.
    invs H.
    assumption.
  - destruct IHargs.
    constructor.
    invs H. assumption.
    eapply H1.
    invs H. assumption.
Qed.


Lemma bool_prop_args_rel_prop_stk_inc_preserves_purity':
   forall (args' args : list bexp_stack) (fenv : fun_env_stk) (n : nat),
     prop_args_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) args' ->
     prop_args_rel (V := bool) (fun b : bexp_stack => bexp_well_formed b) args ->
     transformed_prop_exprs_args (V := bool) (bexp_stk_size_inc_rel n) args args' ->
     prop_args_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) args.
Proof.
  pose proof bool_prop_args_rel_prop_stk_inc_preserves_purity'_folded.
  unfold bool_prop_args_wf in H.
  unfold bool_prop_args_rel in H.
  intros.
  eapply H.
  - eassumption.
  - eapply anon_function_implies_well_formed. assumption.
  - eassumption.
Qed.

Lemma nat_prop_args_rel_prop_stk_inc_preserves_purity_folded :
  forall args args' fenv n,
    nat_prop_args_rel (aexp_pure_rel fenv) args ->
    nat_prop_args_binary_rel (aexp_stk_size_inc_rel n) args args' ->
    nat_prop_args_rel (aexp_pure_rel fenv) args'.
Proof.
  unfold_prop_helpers.
  unfold aexp_pure_rel.
  induction args; intros ? ? ? PURE INC; invs INC; invs PURE.
  - econstructor.
  - econstructor.
    eapply aexp_args_size_inc_preserves_purity; eassumption.
    eapply IHargs; eassumption.
Qed.

Lemma nat_prop_args_rel_prop_stk_inc_preserves_purity_folded' :
  forall args' args fenv n,
    nat_prop_args_rel (aexp_pure_rel fenv) args' ->
    nat_prop_args_wf args ->
    nat_prop_args_binary_rel (aexp_stk_size_inc_rel n) args args' ->
    nat_prop_args_rel (aexp_pure_rel fenv) args.
Proof.
  unfold_prop_helpers.
  unfold aexp_pure_rel, nat_prop_args_wf.
  unfold_prop_helpers.
  induction args'; intros ? ? ? PURE WF INC; invs INC; invs PURE; invs WF.
  - econstructor.
  - econstructor.
    eapply aexp_args_size_inc_preserves_purity'; eassumption.
    eapply IHargs'; eassumption.
Qed.

(* Literally just the unfolded version of the above.... I include these for searching purposes, essentially *)
Lemma nat_prop_args_rel_prop_stk_inc_preserves_purity :
  forall (args args' : list aexp_stack) (fenv : fun_env_stk) (n : nat),
    prop_args_rel (V := nat)
      (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv) args ->
    transformed_prop_exprs_args  (V := nat) (aexp_stk_size_inc_rel n) args args' ->
    prop_args_rel (V := nat)
      (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv) args'.
Proof.
  eapply nat_prop_args_rel_prop_stk_inc_preserves_purity_folded.
Qed.

Lemma nat_anon_function_implies_well_formed :
  forall args,
    nat_prop_args_wf args <-> prop_args_rel (V := nat) (fun b: aexp_stack => aexp_well_formed b) args.
Proof.
  induction args; split; intros.
  - constructor.
  - constructor.
  - destruct IHargs.
    constructor.
    invs H.
    assumption.
    eapply H0.
    invs H.
    assumption.
  - destruct IHargs.
    constructor.
    invs H. assumption.
    eapply H1.
    invs H. assumption.
Qed.

Lemma nat_prop_args_rel_prop_stk_inc_preserves_purity' :
  forall (args args' : list aexp_stack) (fenv : fun_env_stk) (n : nat),
    prop_args_rel (V := nat) (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv) args' ->
    prop_args_rel (V := nat) (fun a : aexp_stack => aexp_well_formed a) args ->
    transformed_prop_exprs_args (V := nat) (aexp_stk_size_inc_rel n) args args' ->
    prop_args_rel (V := nat) (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv) args.
Proof.
  intros.
  eapply nat_anon_function_implies_well_formed in H0.
  eapply nat_prop_args_rel_prop_stk_inc_preserves_purity_folded'; eassumption.
Qed.


  
    


Lemma bool_prop_rel_prop_stk_inc_preserves_purity :
  forall p1 p1' fenv n,
    prop_rel (V := bool) (fun boolexpr: bexp_stack => bexp_stack_pure_rel boolexpr fenv)
             p1 ->
    transformed_prop_exprs (bexp_stk_size_inc_rel n) p1 p1' ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) p1'.
Proof.
  induction p1; intros ? ? ? PURE INC; invs INC; try invs PURE.
  - constructor.
  - econstructor.
  - econstructor.
    eapply bexp_size_inc_preserves_purity; eassumption.
  - econstructor; eapply bexp_size_inc_preserves_purity; eassumption.
  - constructor.
    eapply IHp1_1; eassumption.
    eapply IHp1_2; eassumption.
  - constructor.
    + eapply IHp1_1; eassumption.
    + eapply IHp1_2; eassumption.
  - econstructor; eapply bexp_size_inc_preserves_purity; eassumption.
  - constructor.
    eapply bool_prop_args_rel_prop_stk_inc_preserves_purity; eassumption.
Qed.

Lemma bool_prop_rel_prop_stk_inc_preserves_purity' :
  forall p1' p1 fenv n,
    prop_rel (V := bool) (fun boolexpr: bexp_stack => bexp_stack_pure_rel boolexpr fenv)
             p1' ->
    bool_prop_wf p1 ->
    transformed_prop_exprs (bexp_stk_size_inc_rel n) p1 p1' ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) p1.
Proof.
  induction p1'; intros ? ? ? PURE WF INC; invs INC; invs PURE; invs WF.
  - assumption.
  - assumption.
  - constructor. eapply bexp_size_inc_preserves_purity'; eassumption.
  - constructor; eapply bexp_size_inc_preserves_purity'; eassumption.
  - constructor.
    + eapply IHp1'1; eassumption.
    + eapply IHp1'2; eassumption.
  - constructor.
    + eapply IHp1'1; eassumption.
    + eapply IHp1'2; eassumption.
  - constructor; eapply bexp_size_inc_preserves_purity'; eassumption.
  - constructor.
    eapply bool_prop_args_rel_prop_stk_inc_preserves_purity'; eassumption.
Qed.

Lemma nat_prop_rel_prop_stk_inc_preserves_purity_folded :
  forall p p' fenv n,
    nat_prop_pure fenv p ->
    nat_prop_stk_size_inc n p p' ->
    nat_prop_pure fenv p'.
Proof.
  induction p; intros ? ? ? PURE INC; invs INC; try invs PURE; try constructor; try assumption; try eapply aexp_size_inc_preserves_purity; try eassumption; unfold nat_prop_pure in *.
  - eapply IHp1; eassumption.
  - eapply IHp2; eassumption.
  - eapply IHp1; eassumption.
  - eapply IHp2; eassumption.
  - eapply nat_prop_args_rel_prop_stk_inc_preserves_purity; eassumption.
Qed.

(* Literally just the unfolded verison of the ' version *)
Lemma nat_prop_rel_prop_stk_inc_preserves_purity :
  forall (p p' : StkNatProp) (fenv : fun_env_stk) (n : nat),
  prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
    p ->
  transformed_prop_exprs (aexp_stk_size_inc_rel n) p p' ->
  prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
           p'.
Proof.
  eapply nat_prop_rel_prop_stk_inc_preserves_purity_folded.
Qed.

Lemma nat_prop_rel_prop_stk_inc_preserves_purity' :
  forall (p p' : StkNatProp) (fenv : fun_env_stk) (n : nat),
  prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
           p' ->
  nat_prop_wf p ->
  transformed_prop_exprs (aexp_stk_size_inc_rel n) p p' ->
  prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
           p.
Proof.
  induction p; intros ? ? ? PURE WF INC; invs INC; invs WF; invs PURE; try constructor; try eapply aexp_size_inc_preserves_purity'; try eassumption; unfold nat_prop_wf in *.
  - eapply IHp1.
    + eapply H6.
    + eassumption.
    + eassumption.
  - eapply IHp2; [ eapply H7 | ..]; eassumption.
  - eapply IHp1; [eapply H6 | ..]; eassumption.
  - eapply IHp2; [eapply H7 | .. ]; eassumption.
  - eapply nat_prop_args_rel_prop_stk_inc_preserves_purity'; eassumption.
Qed.

    

    
Lemma meta_bool_stk_size_inc_preserves_purity :
  forall l l' fenv n,
    meta_stk_size_inc n (MetaBool l) (MetaBool l') ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l'.
Proof.
  intros.
  invs H.
  eapply bool_prop_rel_prop_stk_inc_preserves_purity; eassumption.
Qed.

Lemma meta_bool_stk_size_inc_preserves_purity' :
  forall l l' fenv n,
    meta_stk_size_inc n (MetaBool l) (MetaBool l') ->
    bool_prop_wf l ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l' ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l.
Proof.
  intros. invs H.
  eapply bool_prop_rel_prop_stk_inc_preserves_purity'; eassumption.
Qed.


Lemma meta_nat_stk_size_inc_preserves_purity_folded :
  forall l l' fenv n,
    meta_stk_size_inc n (MetaNat l) (MetaNat l') ->
    nat_prop_pure fenv l ->
    nat_prop_pure fenv l'.
Proof.
  intros. invs H.
  eapply nat_prop_rel_prop_stk_inc_preserves_purity; eassumption.
Qed.


(* Literally just unfolded from above... *)
Lemma meta_nat_stk_size_inc_preserves_purity :
  forall (l l' : LogicProp nat aexp_stack) (fenv : fun_env_stk) (n : nat),
    meta_stk_size_inc n (MetaNat l) (MetaNat l') ->
    prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
             l ->
    prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
           l'.
Proof.
  eapply meta_nat_stk_size_inc_preserves_purity_folded.
Qed.

Lemma meta_nat_stk_size_inc_preserves_purity' :
  forall (l l' : LogicProp nat aexp_stack) (fenv : fun_env_stk) (n : nat),
    meta_stk_size_inc n (MetaNat l) (MetaNat l') ->
    nat_prop_wf l ->
    prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
           l' ->
    prop_rel (fun natexpr : aexp_stack => aexp_stack_pure_rel natexpr fenv)
             l.
Proof.
  intros; invs H.
  eapply nat_prop_rel_prop_stk_inc_preserves_purity'; eassumption.
Qed.


                  


(* above lemma needed for aexp_args_stack_increase_preserves_eval' in StackSubstitution *)

(* below lemma needed for arith_args_substitution_vs_update in StackSubstitution *)
Definition P_update_preserves_purity (s: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack): Prop :=
  forall fenv,
    aexp_stack_pure_rel a fenv ->
    aexp_stack_pure_rel aexp fenv ->
    aexp_stack_pure_rel aexp' fenv.

Definition P0_update_preserves_purity (s: stack_index) (a: aexp_stack) (args args': list aexp_stack): Prop :=
  forall fenv,
    aexp_stack_pure_rel a fenv ->
    args_stack_pure_rel args fenv ->
    args_stack_pure_rel args' fenv.

Theorem expr_update_preserves_purity :
  expr_update_mut_ind_theorem P_update_preserves_purity P0_update_preserves_purity.
Proof.
  expr_update_mutual_induction P P0 P_update_preserves_purity P0_update_preserves_purity; intros.
  - assumption.
  - assumption.
  - assumption.
  - invs H2. econstructor.
    + eapply H; assumption.
    + eapply H0; assumption.
  - invs H2. constructor; [eapply H | eapply H0]; assumption.
  - inversion H1. econstructor.
    + eassumption.
    + eapply H; assumption.
    + assumption.
    + assumption.
    + assumption.
  - assumption.
  - invs H2. constructor; [eapply H | eapply H0]; assumption.
Qed.

Lemma arith_update_preserves_aexp_pure :
  forall (s: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack),
    arith_update_rel s a aexp aexp' ->
    forall fenv,
      aexp_stack_pure_rel a fenv ->
      aexp_stack_pure_rel aexp fenv ->
      aexp_stack_pure_rel aexp' fenv.
Proof.
  pose proof (expr_update_preserves_purity).
  unfold expr_update_mut_ind_theorem, P_update_preserves_purity, P0_update_preserves_purity in H.
  destruct H as (AEXP & _).
  apply AEXP.
Qed.

Lemma args_update_preserves_args_pure :
  forall (s: stack_index) (a: aexp_stack) (args args': list aexp_stack),
    args_update_rel s a args args' ->
    forall fenv,
      aexp_stack_pure_rel a fenv ->
      args_stack_pure_rel args fenv ->
      args_stack_pure_rel args' fenv.
Proof.
  pose proof (expr_update_preserves_purity).
  unfold expr_update_mut_ind_theorem, P_update_preserves_purity, P0_update_preserves_purity in H.
  destruct H as (_ & ARGS).
  apply ARGS.
Qed.

Local Definition bool_update_preserves_bexp_pure_P (s: stack_index) (a: aexp_stack) (bexp bexp': bexp_stack): Prop :=
  forall fenv,
    aexp_stack_pure_rel a fenv ->
    bexp_stack_pure_rel bexp fenv ->
    bexp_stack_pure_rel bexp' fenv.

Lemma bool_update_preserves_bexp_pure_folded :
  forall (s: stack_index) (a: aexp_stack) (bexp bexp': bexp_stack),
    bool_update_rel s a bexp bexp' ->
    bool_update_preserves_bexp_pure_P s a bexp bexp'.
Proof.
  apply (bool_update_rel_ind bool_update_preserves_bexp_pure_P); unfold bool_update_preserves_bexp_pure_P; intros; try assumption;
    match goal with
    | [ H: bexp_stack_pure_rel ?b _ |- _ ] =>
        invs H
    end; econstructor.
  - apply H0; assumption. 
  - apply H0; assumption. 
  - apply H2; assumption.
  - apply H0; assumption.
  - apply H2; assumption.
  - eapply arith_update_preserves_aexp_pure; eassumption.
  - eapply arith_update_preserves_aexp_pure; eassumption.
  - eapply arith_update_preserves_aexp_pure; eassumption.
  - eapply arith_update_preserves_aexp_pure; eassumption.
Qed.

Lemma bool_update_preserves_bexp_pure :
  forall (s: stack_index) (a: aexp_stack) (bexp bexp': bexp_stack),
    bool_update_rel s a bexp bexp' ->
    forall fenv,
      aexp_stack_pure_rel a fenv ->
      bexp_stack_pure_rel bexp fenv ->
      bexp_stack_pure_rel bexp' fenv.
Proof.
  apply bool_update_preserves_bexp_pure_folded.
Qed.

Definition P_update_pure_implies_purity (s: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack): Prop :=
  forall fenv,
    aexp_well_formed aexp ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_pure_rel aexp' fenv ->
    aexp_stack_pure_rel aexp fenv.

Definition P0_update_pure_implies_purity (s: stack_index) (a: aexp_stack) (args args': list aexp_stack): Prop :=
  forall fenv,
    args_well_formed args ->
    aexp_stack_pure_rel a fenv ->
    args_stack_pure_rel args' fenv ->
    args_stack_pure_rel args fenv.

Theorem expr_update_pure_implies_purity :
  expr_update_mut_ind_theorem P_update_pure_implies_purity P0_update_pure_implies_purity.
Proof.
  expr_update_mutual_induction P P0 P_update_pure_implies_purity P0_update_pure_implies_purity; intros.
  - econstructor.
  - econstructor.
    invs H. assumption.
  - assumption.
  - invs H3; invs H1. econstructor.
    + eapply H; eassumption.
    + eapply H0; eassumption.
  - invs H3; invs H1; econstructor; [eapply H | eapply H0]; eassumption.
  - invs H2; invs H0.
    econstructor.
    + assert (fenv f = fenv f) by reflexivity.
      eassumption.
    + eapply H; eassumption.
    + eassumption.
    + assumption.
    + assumption.
  - econstructor.
  - invs H3; invs H1.
    econstructor; [eapply H | eapply H0 ]; eassumption.
Qed.

Lemma arith_update_pure_implies_purity :
   (forall (s : stack_index) (a aexp aexp' : aexp_stack),
   arith_update_rel s a aexp aexp' ->
   forall fenv : fun_env_stk,
     aexp_well_formed aexp -> aexp_stack_pure_rel a fenv -> aexp_stack_pure_rel aexp' fenv -> aexp_stack_pure_rel aexp fenv).
Proof.
  pose proof expr_update_pure_implies_purity. 
  unfold P_update_pure_implies_purity in H.
  unfold P0_update_pure_implies_purity in H.
  unfold expr_update_mut_ind_theorem in H.
  destruct H. apply H.
Qed.

Lemma args_update_pure_implies_purity :
  (forall (s : stack_index) (a : aexp_stack) (args args' : list aexp_stack),
   args_update_rel s a args args' ->
   forall fenv : fun_env_stk,
     args_well_formed args -> aexp_stack_pure_rel a fenv -> args_stack_pure_rel args' fenv -> args_stack_pure_rel args fenv).
Proof.
  pose proof expr_update_pure_implies_purity. 
  unfold P_update_pure_implies_purity in H.
  unfold P0_update_pure_implies_purity in H.
  unfold expr_update_mut_ind_theorem in H.
  destruct H. apply H0.
Qed.

Lemma bool_update_pure_implies_bexp_pure :
  forall (s: stack_index) (a: aexp_stack) (bexp bexp': bexp_stack),
    bool_update_rel s a bexp bexp' ->
    forall fenv,
      bexp_well_formed bexp ->
      aexp_stack_pure_rel a fenv ->
      bexp_stack_pure_rel bexp' fenv ->
      bexp_stack_pure_rel bexp fenv.
Proof.
  intros s a bexp bexp' UPDATE. induction UPDATE; intros; auto.
  - invs H1. invs H. econstructor; eauto.
  - invs H1. invs H. econstructor; eauto.
  - invs H1. invs H. econstructor; eauto.
  - invs H1. invs H3. 
    constructor; eapply arith_update_pure_implies_purity; eauto.
  - invs H1. invs H3. constructor; eapply arith_update_pure_implies_purity; eauto.
Qed.

Lemma pure_aexp_implies_same_stack :
  forall aexp fenv stk stk' aval,
    aexp_stack_sem aexp fenv stk (stk', aval) ->
    aexp_stack_pure_rel aexp fenv ->
    stk = stk'.
Proof.
  intros.
  apply aexp_stack_pure_backwards in H0.
  unfold aexp_stack_pure in H0.
  eapply H0.
  eassumption.
Qed.


