From Coq Require Import String Arith Psatz Bool List Program.Equality.
From DanTrick Require Import DanTrickLanguage.


Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Definition ident := string.
Definition a : aexp_Dan := VAR_Dan "a".
Definition b : aexp_Dan := VAR_Dan "b".
Definition max_function_body : imp_Dan := (* a, b are parameters *)
  when (a >d b) then "ret" <- a else "ret" <- b done.
Import ListNotations.

Tactic Notation "a_Dan_eq" constr(n1) constr(n2) :=
  let Heq := fresh "Ha_Dan_eq" in
  assert (Heq: n1 = n2) by (eapply a_Dan_deterministic; eassumption).

Ltac clean H := rewrite H in *; clear H.

Ltac clean_vars n1 n2 :=
  match goal with
  | [ H : n1 = n2 |- _ ] => rewrite H in *; clear H
  | [ H : n2 = n1 |- _ ] => rewrite <- H in *; clear H
  end.

Ltac a_Dan_same :=
  match goal with
  | [ H1 : a_Dan ?a ?dbenv ?fenv ?nenv ?n1, H2 : a_Dan ?a ?dbenv ?fenv ?nenv ?n2 |- _ ] =>
      match goal with
      | [ H3 : n1 = n2 |- _ ] =>
          idtac
      | [ H3 : n2 = n1 |- _ ] =>
          idtac
      | _ =>
          a_Dan_eq n1 n2;
          match goal with
          | [ n1 : _ |- _ ] =>
              clean_vars n1 n2; clear n1; clear H1
          | [ n2 : _ |-  _ ] =>
              clean_vars n2 n1; clear n2; clear H2
          | _ =>
              clean_vars n1 n2; clear H2
          end
      end
  end.

Tactic Notation "b_Dan_eq" constr(b1) constr(b2) :=
  let Heq := fresh "Hb_Dan_eq" in
  assert (Heq : b1 = b2) by (eapply b_Dan_deterministic; eassumption).

Ltac b_Dan_same :=
  match goal with
  | [ H1 : b_Dan ?b ?dbenv ?fenv ?nenv ?n1, H2: b_Dan ?b ?dbenv ?fenv ?nenv ?n2 |- _ ] =>
      match goal with
      | [ H3: n1 = n2 |- _ ] =>
          idtac
      | [ H3 : n2 = n1 |- _ ] =>
          idtac
      | _ =>
          b_Dan_eq n1 n2;
          match goal with
          | [ n1 : _ |- _ ] =>
              clean_vars n1 n2; clear n1; clear H1
          | [ n2 : _ |-  _ ] =>
              clean_vars n2 n1; clear n2; clear H2
          | _ =>
              clean_vars n1 n2; clear H2
          end
      end
  end.

Tactic Notation "inv" hyp(H) :=
  inversion H; subst.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(P) :=
  inversion H as P; subst.


(* Tactics for working with using inversion on the different cases *)

(* Provide meaningful names for the hypotheses for the args_cons case 
 * of args_Dan *)

Tactic Notation "inv_args_Dan" hyp(H) "as" simple_intropattern(Ha_Dan) simple_intropattern(Hargs_Dan) :=
  inversion H as [ (* Dan_const *) |
                   (* Dan_var *)
                   ?aexp ?aexps ?dbenv ?fenv ?nenv ?v ?vals Ha_Dan Hargs_Dan]; subst.

Tactic Notation "inv_args_Dan" hyp(H) :=
  inv_args_Dan H as ?Ha_Dan ?Hargs_Dan.

Tactic Notation "inv_Dan_app" hyp(H) "as" simple_intropattern(ARGS) simple_intropattern(FOLDARGS) simple_intropattern(BODY) simple_intropattern(RET) :=
  inv H as [ (* Dan_const *) | (* Dan_var *)
           | (* Dan_plus *)
           | (* Dan_minus *)
           | (* Dan_app *)
             ?dbenv ?fenv ?nenv ?nenv' ?nenv'' ?func ?aexps ?ns ?ret ?f ?FUNC ARGS FOLDARGS BODY RET].


Tactic Notation "inv_var" hyp(H) "as" simple_intropattern(STORE) :=
  inv H as [ (* CONST *) | ? ? ? ? STORE | (* plus *) | (* minus *) | (* app *)].

Tactic Notation "inv_a_bin" hyp(H) "as" simple_intropattern(A1) simple_intropattern(A2) :=
  inv H as [ (* const *) | (* var *)
           | (* plus *)
             ? ? ? ? ? ? A1 A2
           | (* minus *)
             ? ? ? ? ? ? A1 A2
           | (* app *)].
Tactic Notation "inv_b_bin" hyp(H) "as" simple_intropattern(B1) simple_intropattern(B2) :=
  inv H as [ (* true *) | (* false *)
           | (* neg *)
             ?dbenv ?fenv ?nenv ?bexp ?b B1
           | (* and *)
             ?dbenv ?fenv ?nenv ?bexp1 ?bexp2 ?b1 ?b2 B1 B2
           | (* or *)
             ?dbenv ?fenv ?nenv ?bexp1 ?bexp2 ?b1 ?b2 B1 B2
           | (* leq *)
             ?dbenv ?fenv ?nenv ?a1 ?a2 ?n1 ?n2 B1 B2].

Tactic Notation "inv_Dan_assign" hyp(H) "as" simple_intropattern(EVAL) :=
  inv H as [ (* skip *) | (* if true *) 
           | (* if false *)
           | (* assign *)
             ?dbenv ?fenv ?nenv ?x ?a ?n EVAL
           | (* while done *)
           | (* while step *)
           | (* seq *) ].

Tactic Notation "inv_Dan_if" hyp(H) "as" simple_intropattern(BTRUE) simple_intropattern(I1) simple_intropattern(BFALSE) simple_intropattern(I2) :=
  inv H as [ (* skip *) | (* if true *) ?dbenv ?fenv ?nenv ?nenv' ?bexp ?i1 ?i2 BTRUE I1
           | (* if false *)
             ?dbenv ?fenv ?nenv ?nenv' ?bexp ?i1 ?i2 BFALSE I2
           | (* assign *)
           | (* while done *)
           | (* while step *)
           | (* seq *) ].

Tactic Notation "inv_Dan_while" hyp(H) "as" simple_intropattern(BFALSE) simple_intropattern(BTRUE) simple_intropattern(WHILE_BODY) simple_intropattern(INNER_LOOP) :=
  inv H as [ (* skip *) | (* if true *) 
           | (* if false *)
           | (* assign *)
           | (* while done *)
             ?dbenv ?fenv ?nenv ?bexp ?i BFALSE
           | (* while step *)
             ?dbenv ?fenv ?nenv ?nenv' ?nenv'' ?bexp ?i BTRUE WHILE_BODY INNER_LOOP
           | (* seq *) ].

Tactic Notation "inv_Dan_seq" hyp(H) "as" simple_intropattern(I1) simple_intropattern(I2) :=
  inv H as [ (* skip *) | (* if true *) 
           | (* if false *)
           | (* assign *)
           | (* while done *)
           | (* while step *)
           | (* seq *)
             ?dbenv ?fenv ?nenv ?nenv' ?nenv'' ?i1 ?i2 I1 I2].
Ltac invc H :=
  inv H; clear H.




Tactic Notation "clean" "<-" hyp(H) := (symmetry in H; clean H).

Ltac falsify :=
  match goal with
  | [ H : ?x = ?y, H': ?x <> ?y |- _ ] =>
      unfold not in H';
      apply H' in H;
      inversion H
  | [ H: ?y = ?x, H' : ?x <> ?y |- _ ] =>
      unfold not in H';
      symmetry in H;
      apply H' in H;
      inversion H
  end.




(* These tactics are from SF *)
Tactic Notation "false_goal" :=
  elimtype False.

Ltac false_post :=
  solve [ assumption
        | discriminate
        | congruence ].

Tactic Notation "false" :=
  false_goal; try false_post.

Tactic Notation "tryfalse" :=
  try solve [ false ].

Ltac destruct_if_post := tryfalse.
(* End of tactics from SF *)

Ltac discrim_neq :=
  match goal with
  | [ H: ?x <> ?x |- _ ] =>
      assert (x = x) by reflexivity;
      match goal with
      | [ H' : x = x |- _ ] =>
          unfold not in H; apply H in H'; inversion H'
      end
  end.

Tactic Notation "destruct_discrim" constr(x) "as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
  destruct x as [Eq1 | Eq2]; try discriminate; try discrim_neq.

Tactic Notation "destruct_discrim" constr(x) :=
  destruct_discrim x as ? ?.

(* This is a tactic from SF that I modified *)
Tactic Notation "destruct_if" "as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
  match goal with
  | |- context [ if ?B then _ else _ ] =>
      destruct_discrim B as Eq1 Eq2
      || destruct B as [Eq1 | Eq2]
  | K: context [ if ?B then _ else _ ] |- _ =>
      destruct_discrim B as Eq1 Eq2
      || destruct B as [Eq1 | Eq2]
  end;
  tryfalse.

Ltac resolve_inequalities :=
  repeat match goal with
         | [ H: ?n <=? ?n' = true |- _ ] => apply leb_complete in H
         | [ H: ?n <=? ?n' = false |- _ ] => apply leb_complete_conv in H
         end.


Ltac fancy_unfold_update :=
  unfold update; simpl;
  (auto ||
     let eq1 := fresh "eq1" in
     let eq2 := fresh "eq2" in
     try destruct_if as eq1 eq2;
     try discrim_neq; resolve_inequalities; auto).
Ltac introv :=
  hnf; match goal with
       | |- ?P -> ?Q => idtac
       | |- forall _, _ => intro; introv
       end.

(* Occassionally when you use inversion on b_Dan, you also get an additional hypothesis
 * of the form H: _ && _ = _. This allows you to automatically rename that hypothesis
 * to something meaningful. *)
Ltac rename_andb_term H H' NEWNAME :=
  match type of H with
  | b_Dan _ _ _ ?b1 =>
      match type of H' with
      | b_Dan _ _ _ ?b2 =>
          match goal with
          | [ H'' : b1 && b2 = ?b3 |- _ ] =>
              pose proof H'' as NEWNAME; clear H''
          | [ H'': b2 && b1 = ?b3 |- _ ] =>
              pose proof H'' as NEWNAME; clear H''
          | _ => idtac
          end
      | _ => idtac
      end
  | _ =>  idtac
  end.

Tactic Notation "inv_b_bin" hyp(H) "as" simple_intropattern(B1) simple_intropattern(B2) simple_intropattern(B3) :=
  inv_b_bin H as B1 B2; rename_andb_term B1 B2 B3.

Tactic Notation "capply" hyp(H) :=
  apply H; clear H.

Tactic Notation "capply" hyp(H) "in" hyp(H1) :=
  apply H in H1; clear H.

Tactic Notation "ceapply" hyp(H) :=
  eapply H; clear H.

Tactic Notation "ceapply" hyp(H) "in" hyp(H1) :=
  eapply H in H1; clear H.

Lemma destruct_andb :
  forall b1 b2,
    b1 && b2 = true ->
    (b1 = true /\ b2 = true).
Proof.
  introv. destruct b1, b2; intros; try discriminate.
  split; reflexivity.
Qed.

Tactic Notation "destruct_andb" hyp(H) :=
  apply destruct_andb in H.

Tactic Notation "destruct_andb" hyp(H) "as" simple_intropattern(P) :=
  destruct_andb H; destruct H as P.



Tactic Notation "a_Dan_elim" := repeat a_Dan_same.

Tactic Notation "b_Dan_elim" := repeat b_Dan_same.
