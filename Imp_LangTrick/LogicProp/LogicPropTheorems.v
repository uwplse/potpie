From Coq Require Import Arith Psatz List String.
From Imp_LangTrick Require Import LogicProp StackLangTheorems.

(** Adequacy theorems for the higher-order relations and functions on LogicProps *)

Lemma transform_prop_exprs_args_adequacy_forward :
  forall (V A: Set) (l l': list A) (phi: A -> A) (psi: A -> A -> Prop),
    (forall (a1 a2: A),
        a2 = phi a1 <->
          psi a1 a2) ->
    l' = map phi l ->
    transformed_prop_exprs_args (V := V) psi l l'.
Proof.
  intros V A l.
  induction l; intros.
  - simpl in H0. subst. econstructor.
  - simpl in H0. rewrite H0. econstructor.
    eapply H. reflexivity.
    eapply IHl; eauto.
Defined.

Lemma transform_prop_exprs_args_adequacy_backward :
  forall (V A: Set) (l l': list A) (phi: A -> A) (psi: A -> A -> Prop),
    (forall (a1 a2: A),
        a2 = phi a1 <->
          psi a1 a2) ->
    transformed_prop_exprs_args (V := V) psi l l' ->
    l' = map phi l.
Proof.
  intros V A l.
  induction l; intros.
  - simpl. invs H0. reflexivity.
  - invs H0. simpl. f_equal.
    + eapply H. assumption.
    + eapply IHl; eassumption.
Qed.

Lemma transform_prop_exprs_adequacy_forward :
  forall (V A: Set) (l l': LogicProp V A) (phi: A -> A) (psi: A -> A -> Prop),
    (forall (a1 a2: A),
        a2 = phi a1 <->
          psi a1 a2) ->
    l' = transform_prop_exprs l phi ->
    transformed_prop_exprs psi l l'.
Proof.
  intros V A.
  induction l; intros;
    match goal with
    | [ H : ?l' = transform_prop_exprs ?l ?phi |- _ ] =>
        simpl in H; rewrite H
    end.
  - econstructor.
  - econstructor.
  - econstructor. eapply H. reflexivity.
  - econstructor; eapply H; reflexivity.
  - econstructor; first [ eapply IHl1 | eapply IHl2 ]; eauto.
  - econstructor; first [ eapply IHl1 | eapply IHl2 ]; eauto.
  - econstructor; eapply H; reflexivity.
  - econstructor. eapply transform_prop_exprs_args_adequacy_forward; eauto.
Defined.

Lemma transform_prop_exprs_adequacy_backward :
  forall (V A: Set) (l l': LogicProp V A) (phi: A -> A) (psi: A -> A -> Prop),
    (forall (a1 a2: A),
        a2 = phi a1 <->
          psi a1 a2) ->
    transformed_prop_exprs psi l l' ->
    l' = transform_prop_exprs l phi.
Proof.
  intros V A.
  induction l; intros;
    match goal with
    | [ H : transformed_prop_exprs ?psi ?l ?l' |- _ ] =>
        invs H
    end; simpl; f_equal; try (first [ eapply H | eapply IHl | eapply IHl1 | eapply IHl2 ]; eassumption).
  eapply transform_prop_exprs_args_adequacy_backward; eassumption.
Qed.

Lemma compile_prop_args_adequacy_forward :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B),
    args' = map phi args ->
    compile_prop_args_rel phi args args'.
Proof.
  induction args; intros; simpl in H; rewrite H; econstructor.
  invs H.
  eapply IHargs.
  eauto.
Qed.

Lemma compile_prop_args_adequacy_backward :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B),
    compile_prop_args_rel phi args args' ->
    args' = map phi args.
Proof.
  induction args; intros; invs H; simpl; try eauto.
  f_equal; try eauto.
Qed.


Lemma compile_prop_adequacy_forward :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B),
    l' = compile_prop l phi ->
    compile_prop_rel phi l l'.
Proof.
  induction l; intros; simpl in H; rewrite H; econstructor;
    try (first [eapply IHl | eapply IHl1 | eapply IHl2]; eauto).
  invs H.
  eapply compile_prop_args_adequacy_forward; eauto.
Qed.


Lemma compile_prop_adequacy_backward :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B),
    compile_prop_rel phi l l' ->
    l' = compile_prop l phi.
Proof.
  induction l; intros; invs H; simpl; try eauto; f_equal;
    try (first [eapply IHl | eapply IHl1 | eapply IHl2]; eauto).
  eapply compile_prop_args_adequacy_backward. assumption.
Qed.

Theorem compile_prop_args_adequacy :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B),
    args' = map phi args <->
      compile_prop_args_rel phi args args'.
Proof.
  split; intros;
    first [eapply compile_prop_args_adequacy_backward | eapply compile_prop_args_adequacy_forward];
    eauto.
Qed.

Theorem compile_prop_adequacy :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B),
    l' = compile_prop l phi <->
      compile_prop_rel phi l l'.
Proof.
  split; intros;
    first [eapply compile_prop_adequacy_backward | eapply compile_prop_adequacy_forward];
    eauto.
Qed.

Lemma pcompile_prop_args_rel_adequacy_forward :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    compile_prop_args_rel phi args args' ->
    pcompile_args_rel psi args args'.
Proof.
  induction args; intros; invs H0; econstructor.
  - eapply H. eauto.
  - eapply IHargs; eauto.
Qed.

Lemma pcompile_prop_rel_adequacy_forward :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    compile_prop_rel phi l l' ->
    pcompile_rel psi l l'.
Proof.
  induction l; intros; invs H0; econstructor;
    try (first [eapply IHl | eapply IHl1 | eapply IHl2]; eauto);
    try (eapply H; eauto).
  eapply pcompile_prop_args_rel_adequacy_forward; eauto.
Qed.

Lemma pcompile_prop_args_rel_adequacy_backward :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    pcompile_args_rel psi args args' ->
    compile_prop_args_rel phi args args'.
Proof.
  induction args; intros; invs H0; try econstructor.
  eapply IHargs in H6; [ | eassumption ].
  eapply H in H4. rewrite H4. econstructor.
  assumption.
Qed.

Lemma pcompile_prop_rel_adequacy_backward :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    pcompile_rel psi l l' ->
    compile_prop_rel phi l l'.
Proof.
  induction l; intros; invs H0; try econstructor;
    try repeat match goal with
    | [ psi: ?A -> ?B -> Prop,
        Hpsi : ?psi ?a ?b |- _ ] =>
        eapply H in Hpsi; rewrite Hpsi
               end; try econstructor; try eauto.
  eapply pcompile_prop_args_rel_adequacy_backward; eauto.
Qed.

Theorem pcompile_prop_args_rel_adequacy :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    compile_prop_args_rel phi args args' <->
      pcompile_args_rel psi args args'.
Proof.
  split; intros;
    first [eapply pcompile_prop_args_rel_adequacy_forward | eapply pcompile_prop_args_rel_adequacy_backward];
    eauto.
Qed.

Theorem pcompile_prop_rel_adequacy :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    compile_prop_rel phi l l' <->
    pcompile_rel psi l l'.
Proof.
  split; intros;
    first [eapply pcompile_prop_rel_adequacy_forward | eapply pcompile_prop_rel_adequacy_backward];
    eauto.
Qed.

Theorem pcompile_compile_args_adequacy :
  forall (A B: Set) (args: list A) (args': list B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    args' = map phi args <->
      pcompile_args_rel psi args args'.
Proof.
  split; intros.
  - eapply pcompile_prop_args_rel_adequacy; try eauto.
    eapply compile_prop_args_adequacy.
    assumption.
  - eapply compile_prop_args_adequacy.
    eapply pcompile_prop_args_rel_adequacy; try eauto.
Qed.

Theorem pcompile_compile_adequacy :
  forall (V A B: Set) (l: LogicProp V A) (l': LogicProp V B) (phi: A -> B) (psi: A -> B -> Prop),
    (forall (a: A) (b: B),
        b = phi a <->
          psi a b) ->
    l' = compile_prop l phi <->
      pcompile_rel psi l l'.
Proof.
  split; intros.
  - eapply pcompile_prop_rel_adequacy; try eauto.
    eapply compile_prop_adequacy.
    eassumption.
  - eapply compile_prop_adequacy.
    eapply pcompile_prop_rel_adequacy; try eauto.
Qed.

Lemma eval_prop_args_adequacy_forward :
  forall (V A: Set) (args: list A) (args': list V) (phi: A -> V) (psi: A -> V -> Prop),
    (forall (v: V) (a: A),
        v = phi a <->
          psi a v) ->
    args' = map phi args ->
    eval_prop_args_rel psi args args'.
Proof.
  induction args; intros; simpl in H0; rewrite H0; try econstructor.
  - eapply H. reflexivity.
  - eapply IHargs; try eauto.
Qed.

Definition fun_rel_adequate {A B: Set} (phi: A -> B) (psi: A -> B -> Prop): Prop :=
  forall (a: A) (b: B),
    b = phi a <->
      psi a b.

Lemma eval_prop_adequacy_forward :
  forall (V A: Set) (l: LogicProp V A) (phi: A -> V) (psi: A -> V -> Prop),
    fun_rel_adequate phi psi ->
    eval_prop l phi ->
    eval_prop_rel psi l.
Proof.
  induction l; intros; unfold fun_rel_adequate in *; simpl in H0.
  - econstructor.
  - invs H0.
  - econstructor.
    + eapply H. eauto.
    + eauto.
  - econstructor.
    + eapply H. eauto.
    + eapply H; eauto.
    + eauto.
  - econstructor; destruct H0; eauto.
  - destruct H0; [econstructor | eapply RelOrPropRight]; eauto.
  - econstructor; try eapply H; eauto.
  - econstructor.
    eapply eval_prop_args_adequacy_forward; eauto.
    eauto.
Qed.

Lemma eval_prop_args_adequacy_backward :
  forall (V A: Set) (args: list A) (args': list V) (phi: A -> V) (psi: A -> V -> Prop),
    (forall (v: V) (a: A),
        v = phi a <->
          psi a v) ->
    eval_prop_args_rel psi args args' ->
    args' = map phi args.
Proof.
  induction args; intros; invs H0; try econstructor.
  simpl.
  f_equal.
  - eapply H. assumption.
  - eapply IHargs; eauto.
Qed.

Lemma eval_prop_adequacy_backward :
  forall (V A: Set) (l: LogicProp V A) (phi: A -> V) (psi: A -> V -> Prop),
    fun_rel_adequate phi psi ->
    eval_prop_rel psi l ->
    eval_prop l phi.
Proof.
  induction l; intros; invs H0;
  match goal with
  | [ |- eval_prop (OrProp _ _ _ _) _ ] =>
      idtac
  | _ => try econstructor
            end; simpl; unfold fun_rel_adequate in *;
    try repeat match goal with
               | [ psi: ?A -> ?B -> Prop,
                     Hpsi : ?psi ?a ?b |- _ ] =>
                   eapply H in Hpsi; rewrite Hpsi in *; eauto
               end.
  - eapply IHl1; eauto.
  - eapply IHl2; eauto.
  - left. eapply IHl1; eauto.
  - right. eapply IHl2; eauto.
  - eapply eval_prop_args_adequacy_backward in H4. erewrite <- H4. eassumption. eauto.
Qed.

Theorem eval_prop_args_adequacy :
  forall (V A: Set) (args: list A) (args': list V) (phi: A -> V) (psi: A -> V -> Prop),
    (forall (v: V) (a: A),
        v = phi a <->
          psi a v) ->
    args' = map phi args <->
    eval_prop_args_rel psi args args'.
Proof.
  split; intros;
    first [eapply eval_prop_args_adequacy_forward | eapply eval_prop_args_adequacy_backward];
    eauto.
Qed.


Lemma eval_prop_adequacy :
  forall (V A: Set) (l: LogicProp V A) (phi: A -> V) (psi: A -> V -> Prop),
    fun_rel_adequate phi psi ->
    eval_prop l phi <->
      eval_prop_rel psi l.
Proof.
  split; intros;
    first [eapply eval_prop_adequacy_forward | eapply eval_prop_adequacy_backward];
    eauto.
Qed.

Section fun_rel_implies.
  Variable V A: Set.

  

  Let fun_rel_implies (phi phi': A -> Prop) :=
        forall (a: A),
          phi a -> phi' a.

  Variable phi phi': A -> Prop.
  
  Lemma prop_rel_args_implies :
    forall (alist: list A),
      fun_rel_implies phi phi' ->
      prop_args_rel (V := V) phi alist ->
      prop_args_rel (V := V) phi' alist.
  Proof.
    induction alist; intros.
    - constructor.
    - invs H0. constructor.
      + eapply H. assumption.
      + eapply IHalist; assumption.
  Qed.
  
  Lemma prop_rel_implies :
    forall (a: LogicProp V A),
    forall (IMP: fun_rel_implies phi phi')
      (PROP: prop_rel phi a),
      prop_rel phi' a.
  Proof.
    induction a; intros; invs PROP; try constructor; try (eapply IMP; assumption); eauto.
    - eapply prop_rel_args_implies; assumption.
  Qed.
End fun_rel_implies.
      
      
