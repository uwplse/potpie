(* Automation for proof compilation *)

From Coq Require Import List Arith Psatz String.

From Imp_LangTrick Require Import Base StackLangTheorems LogicTranslationBase StackLanguage Imp_LangTrickLanguage LogicProp Imp_LangLogProp ImpVarMapTheorems ProofCompilerPostHelpers ReflectionMachinery.
Require Imp_LangTrick.Tactics.FunctionWellFormedReflection.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.


Fixpoint not_In {A: Type} (a: A) (l: list A) :=
  match l with
  | nil => True
  | b :: m => ((b <> a) /\ (not_In a m))
  end.

Inductive not_In_ind {A: Type} (a: A) : (list A) -> Prop :=
| not_In_nil : not_In_ind a nil
| not_In_cons :
  forall b m,
    b <> a ->
    not_In_ind a m ->
    not_In_ind a (b :: m).


Lemma not_In_implies_In_implies_False :
  forall (A: Type) (a: A) (l: list A),
    not_In a l ->
    ~ (In a l).
Proof.
  induction l; intros.
  - simpl in H. unfold not. intros. simpl in H0. assumption.
  -  unfold not. intros. simpl in H0. simpl in H. destruct H. destruct H0.
     + contradiction.
     + eapply IHl in H1. contradiction.
Qed.

Lemma not_In_ind_implies_not_In :
  forall (A: Type) (a: A) (l: list A),
    not_In_ind a l ->
    not_In a l.
Proof.
  induction l; intros.
  - simpl. eapply I.
  - simpl. invs H. split.
    + eassumption.
    + eapply IHl in H3. eassumption.
Qed.

                       
Fixpoint construct_not_In {A: Type} {Aeq_dec: forall x y: A, {x = y} + {x <> y}} (a: A) (l: list A) : option (not_In a l) :=
  match l as l' return (option (not_In a l')) with
  | nil => Some (I) (* the constructor for True *)
  | b :: m =>
      match (Aeq_dec b a) with
      | left P => None
      | right P =>
          match (@construct_not_In A Aeq_dec a m) with
          | Some P' =>
              Some (conj P P')
          | None => None
          end
      end
  end.
  
Fixpoint construct_nodup {A: Type} {Aeq_dec: forall x y: A, {x = y} + {x <> y}} (l: list A) : option (NoDup l) :=
  match l as l' return option (NoDup l') with
  | nil => Some (NoDup_nil A)
  | a :: rest =>
      match (@construct_not_In A Aeq_dec a rest) with
      | Some P_not_in =>
          match (@construct_nodup A Aeq_dec rest) with
          | Some P_nodup =>
              Some (@NoDup_cons A a rest (not_In_implies_In_implies_False A a rest P_not_in) P_nodup)
          | None => None
          end
      | None => None
      end
  end.

(* Print or_introl. *)

Fixpoint construct_In {A: Type} (Aeq_dec : forall x y: A, {x = y} + {x <> y}) (a: A) (l: list A) : option (In a l) :=
  match l as l' return (option (In a l')) with
  | nil => None
  | b :: m =>
      match (Aeq_dec b a) with
      | left P_b_eq_a =>
          Some (or_introl P_b_eq_a)
      | right _ =>
          match (construct_In Aeq_dec a m) with
          | Some P_in => Some (or_intror P_in)
          | None => None
          end
      end
  end.


Ltac finite_nodup_reflective :=
  match goal with
  | [ |- @NoDup string ?l ] =>
      exact (optionOut (@NoDup string l) (@construct_nodup string string_dec l))
  | [ |- @NoDup ident ?l ] =>
      exact (optionOut (@NoDup ident l) (@construct_nodup ident string_dec l))
  | [ |- @NoDup fun_Imp_Lang ?l ] =>
      exact (optionOut (@NoDup fun_Imp_Lang l)
                       (@construct_nodup fun_Imp_Lang
                                         FunctionWellFormedReflection.fun_Imp_Lang_dec
                                         l))
  end.

Ltac finite_not_in_reflective :=
  match goal with
  | [ |- ~ @In ?tipe ?l ] =>
      match tipe with
      | string =>
          exact (optionOut (~ @In string l)
                           (@construct_not_In string string_dec l))
      | ident =>
          exact (optionOut (~ @In ident l)
                           (@construct_not_In ident string_dec l))
      | fun_Imp_Lang =>
          exact (optionOut (~ @In fun_Imp_Lang l)
                           (@construct_not_In fun_Imp_Lang
                                              FunctionWellFormedReflection.fun_Imp_Lang_dec
                                              l))
      end
  end.


Ltac finite_not_in_slow :=
  match goal with
  | [ |- ~ In ?x nil ] =>
      intros NOT;
      invs NOT
  | [ |- ~ In ?x (cons ?y ?rest_list) ] =>
      intros NOT;
      invc NOT; finite_not_in_slow
  | [ H: ?a = ?b |- False ] =>
      try invc H
  | [ H: In ?x (cons ?y ?rest_list) |- _ ] =>
      invc H;
      finite_not_in_slow
  | [ H: In ?x nil |- _ ] =>
      invc H
  end.

Ltac finite_not_in :=
  finite_not_in_reflective || finite_not_in_slow.

Ltac finite_nodup_slow :=
  match goal with
  | [ |- NoDup (cons _ _) ] =>
      constructor; [ finite_not_in | try finite_nodup_slow ]
  | [ |- NoDup nil ] =>
      constructor
  end.

Ltac finite_nodup :=
  finite_nodup_reflective || finite_nodup_slow.

Lemma probably_not_true :
  forall (P Q: Prop),
    ~ P /\ ~ Q ->
    ~ (P \/ Q).
Proof.
  intros. destruct H.
  intros PorQ.
  destruct PorQ.
  - contradiction.
  - contradiction.
Qed.

Example nodup_three :
  NoDup (1 :: 2 :: 3 :: nil).
Proof.
  finite_nodup.
Qed.

Example nodup_ten :
  NoDup (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: nil).
Proof.
  finite_nodup.
Qed.
  
From Coq Require Import String.

Local Open Scope string_scope.

Example nodup_abc :
  NoDup ("a" :: "b" :: "c" :: nil).
Proof.
  finite_nodup.
Qed.

(* For easy stuff, we can go faster using the reflection *)
Ltac finite_in :=
  match goal with
  | [ |- @In string ?x ?l ] =>
      exact (optionOut (@In string x l) (construct_In string_dec x l))
  | [ |- @In ident ?x ?l ] =>
      exact (optionOut (@In ident x l) (construct_In string_dec x l))
  | [ |- In ?x (cons ?x _) ] =>
      eapply in_eq
  | [ |- In ?x (cons _ _) ] =>
      eapply in_cons; finite_in
  | [ |- In _ nil ] =>
      idtac "got to nil, failing";
      fail
  | [ |- In _ ?listexpr ] =>
      let listExprId := fresh "listexpr" in
      let listExprEq := fresh "Heq" in
      remember (listexpr) as listExprId eqn:listExprEq;
      simpl in listExprEq;
      subst listExprId;
      finite_in
  end.

Example a_in_abc :
  In "a" ("a" :: "b" :: "c" :: nil).
Proof.
  finite_in.
Qed.

Example c_in_abc :
  In "c" ("a" :: "b" :: "c" :: nil).
Proof.
  finite_in.
Qed.




Require Import Imp_LangTrick.CodeCompiler.EnvToStack.

Ltac AbsEnv_rel_inversion :=
  repeat match goal with
         | [ H: AbsEnv_rel _ _ _ _ |- _ ] =>
             progress invc H
         | [ H: Imp_Lang_lp_rel _ _ _ _ |- _ ] =>
             progress invc H
         | [ H: eval_prop_rel _ _ |- _ ] =>
             progress invc H
         | [ H: b_Imp_Lang _ _ _ _ _ |- _ ] =>
             progress invc H
         | [ H: a_Imp_Lang (PARAM_Imp_Lang _) _ _ _ _ |- _ ] =>
             progress invc H
         end.

Lemma big_enough :
  forall vars nenv dbenv stk n N,
    state_to_stack vars nenv dbenv stk ->
    forall k,
      nth_error dbenv k = Some n ->
      N = Datatypes.length vars + k + 1 ->

    Datatypes.length stk >= N.
Proof.
  intros vars nenv dbenv stk n N.
  intros STATE.
  invs STATE.
  intros k. intros H. intros NEQUAL. subst N. revert H. clear STATE. revert dbenv.
  induction k; intros.
  - destruct dbenv. invs H.
    rewrite app_length. rewrite map_length. simpl.
    rewrite <- Nat.add_assoc.
    replace (0 + 1) with 1.
    unfold ge.
    eapply Plus.plus_le_compat_l_stt.
    eapply le_n_S. lia.
    lia.
  - destruct dbenv. invs H.
    invs H.
    rewrite app_length. rewrite map_length. simpl. rewrite Nat.add_succ_r.
    rewrite <- Nat.add_assoc.
    simpl. rewrite Nat.add_succ_r. eapply le_n_S. rewrite Nat.add_assoc. replace (Datatypes.length vars + k + 1 <=
                                                                                    Datatypes.length vars + Datatypes.length dbenv) with (Datatypes.length vars + Datatypes.length dbenv >= Datatypes.length vars + k + 1).
    Check map_length.
    rewrite <- map_length with (B := nat) (f := nenv) at 1.
    rewrite <- app_length. eapply IHk.
    assumption.
    unfold ge. reflexivity.
Qed.

Ltac get_rid_of_ridiculousness :=
  match goal with
  | [ H: nth_error nil _ = Some ?n' |- _ ] =>
      invs H
  | [ H: nth_error (cons ?n nil) 1 = Some ?n' |- _ ] =>
      invs H
  | [ H2 : state_to_stack (cons _ _) ?nenv ?dbenv nil |- _ ] =>
      invs H2
  | [ H : state_to_stack (cons ?x ?y) _ nil (_ :: _ :: _) |- _ ] =>
      invs H
  | [ H2 : state_to_stack (_ :: nil) _ ?dbenv (_ :: nil),
        H6 : nth_error ?dbenv ?n = Some _ |- _ ] =>
      match n with
      | 0 =>
          invs H2; invs H6
      | 1 =>
              invs H2; invs H6
      end
  | [ H: None = Some _ |- _ ] =>
      invs H
  | [ H: Some _ = None |- _ ] =>
      invs H
  end.

Ltac destruct_stks stk :=
  destruct stk;
  try get_rid_of_ridiculousness;
  match goal with
  | [ |- _ >= _ ] =>
      unfold ge
  | [ |- _ ] =>
      idtac
  end;
  match goal with
  | [ |- None = Some ?n ] =>
      get_rid_of_ridiculousness
      (* match goal with *)
      (* | [ H: nth_error nil 0 = Some ?n' |- _ ] => *)
      (*     invs H *)
      (* | [ H: nth_error (cons ?n nil) 1 = Some ?n' |- _ ] => *)
      (*     invs H *)
      (* | [ H2 : state_to_stack (cons _ _) ?nenv ?dbenv nil |- _ ] => *)
      (*     invs H2 *)
      (* end *)
  | [ |- Some ?n = Some ?n'] =>
      match goal with
      | [ H2 : state_to_stack _ _ _ _ |- _ ] =>
          invs H2;
          match goal with
          | [ H3 : nth_error _ _ = Some n' |- _ ] =>
              invs H3;
              reflexivity
          end
      end
  | [ |- 0 <= Datatypes.length nil ] =>
      simpl; constructor
  | [ |- _ <= Datatypes.length nil ] =>
      get_rid_of_ridiculousness
  | [ |- 1 <= Datatypes.length (_ :: nil ) ] =>
      simpl; lia
  | [ |- 2 <= (Datatypes.length (_ :: _ :: _)) ] =>
      simpl; lia
  | [ |- 2 <= (Datatypes.length (_ :: nil)) ] =>
      get_rid_of_ridiculousness
  | [ |- 3 <= Datatypes.length (_ :: _ :: _ :: _) ] =>
      simpl; lia
  | [ |- _ ] =>
      match goal with
      | [ H2 : state_to_stack _ _ _ _ |- _ ] =>
          try (progress invs H2)
      end
  end.

Ltac repeat_until_matches_le :=
  match goal with
  | [ |- _ <= _ ] =>
      idtac
  | [ |- _ ] =>
      econstructor;
      repeat_until_matches_le
  end.

Lemma nth_error_nil_none :
  forall A n,
    @nth_error A nil n = None.
Proof.
  intros A. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Ltac absstate_match_inversion :=
  match goal with
  | [ H : StackLogicGrammar.absstate_match_rel _ _ _ |- _ ] =>
      invc H; absstate_match_inversion
  | [ H: StackLogicGrammar.absstack_match_rel _ _ |- _ ] =>
      invc H; absstate_match_inversion
  | [ H: StackLogicGrammar.meta_match_rel _ _ _ |- _ ] =>
      idtac "meta"; invc H; absstate_match_inversion
  | [ H: eval_prop_rel _ _ |- _ ] =>
      invc H; absstate_match_inversion
  | [ H: bexp_stack_sem _ _ _ _ |- _ ] =>
      invc H; absstate_match_inversion
  | [ H: aexp_stack_sem _ _ _ _ |- _ ] =>
      invc H; absstate_match_inversion
  | [ |- _ ] =>
      idtac "done"
  end.

Ltac reflect_seq H := rewrite String.eqb_eq in H; subst.
Ltac destruct_seq x y := destruct (string_dec x y).

Ltac invs_exists H i :=
  invs H; try (exists i; reflexivity).


Ltac twice t := t; t.
Ltac thrice t := t; t; t.


Ltac list_finite x :=
  match x with
  | cons _ ?rest =>
      list_finite rest
  | nil =>
      idtac
  | _ =>
      fail
  end.

Ltac var_map_wf_finite :=
  match goal with
  | [ |- var_map_wf ?x ] =>
      list_finite x;
      unfold var_map_wf; repeat split;
      [ finite_nodup | intros .. ];
      [ eapply find_index_rel_implication
      | eapply second_wf_proof
      | eapply in_list_means_exists_index
      | eapply free_vars_in_imp_alternate
      ]; eassumption
  end.

Ltac finite_in_implication :=
  match goal with
  | [ H: In ?x ?listA |- In ?x ?listB ] =>
      list_finite listA;
      list_finite listB;
      simpl in *; destruct H;
      finite_in_implication
  | [ H: ?y = ?x |- ?y = ?x \/ _ ] =>
      left; eassumption
  | [ H: ?y = ?x |- ?z = ?x \/ _ ] =>
      match z with
      | y =>
          left; finite_in_implication
      | _ =>
          right; finite_in_implication
      end
  | [ H: _ = _ \/ _ |- _ ] =>
      destruct H; finite_in_implication
  | [ H: False |- _ ] =>
      invs H; finite_in_implication
  | [ |- _ ] =>
      idtac
  end.

Ltac imp_has_variable_implies_in :=
  match goal with
  | [ H: imp_has_variable ?x _ |- In ?x ?listA ] =>
      list_finite listA;
      invc H;
      imp_has_variable_implies_in
  | [ H: (?x =? ?y) = true |- In ?x ?listA ] =>
      list_finite listA;
      eapply String.eqb_eq in H; rewrite H; finite_in
  | [ H: aexp_has_variable ?x _ |- In ?x ?listA ] =>
      list_finite listA;
      invc H;
      imp_has_variable_implies_in
  | [ H: args_has_variable ?x _ |- In ?x ?listA ] =>
      list_finite listA;
      invc H;
      imp_has_variable_implies_in
  | [ |- _ ] =>
      idtac
  end.


(* This is kind of misnamed, since it's no longer recursive... *)
(* Incidentally, I only needed this to work for lists of length 1, so no recursion needed. But it could be adapted to work for all finite lists *)
Ltac destruct_nth_error_rec :=
  match goal with
  | [ H: nth_error _ 0 = Some _ |- _ ] =>
      simpl in H;
      match goal with
      | [ H: Some _ = Some _ |- _ ] =>
          invc H
      end
  | [ H: nth_error (_ :: nil) (S ?n) = Some _ |- _ ] =>
      simpl in H;
      rewrite nth_error_nil_none in H;
      discriminate
  end.


Ltac destruct_nth_error listName :=
  unfold listName in *;
  match goal with
  | [ H : nth_error (_ :: _) ?n = Some _ |- _ ] =>
      destruct n;
      destruct_nth_error_rec
  end.

Require Import StackExprWellFormed.

Ltac expr_well_formed_slow :=
  match goal with
  | [ |- aexp_well_formed  _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- 1 <= ?k ] =>
      try lia
  | [ |- args_well_formed _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- bexp_well_formed _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- lp_aexp_well_formed _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- lp_bexp_well_formed _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- mv_well_formed  _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- prop_rel _ _ ] =>
      econstructor; expr_well_formed_slow
  | [ |- absstate_well_formed _ ] =>
      econstructor; expr_well_formed_slow
  end.

Ltac expr_well_formed :=
  prove_absstate_well_formed || expr_well_formed_slow.
