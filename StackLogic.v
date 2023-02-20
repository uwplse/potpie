From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangEval DanTrick.LogicProp DanTrick.StackSubstitution DanTrick.StackPurest DanTrick.StackExprWellFormed.

From DanTrick Require Export StackLogicBase.

Scheme Equality for list.



                           


Definition triple_stk (P: AbsState) (i: imp_stack) (Q: AbsState) (fenv: fun_env_stk): Prop :=
  forall (stk stk': stack),
    imp_stack_sem i fenv stk stk' ->
    (absstate_match_rel P fenv stk) ->
    (absstate_match_rel Q fenv stk').

Notation "{{{ P }}} i {{{ Q }}} @ f" := (triple_stk P i Q f) (at level 90, i at next level).
    



Definition atruestk (b: bexp_stack) (P: AbsState): AbsState :=
  (AbsAnd P (BaseState (AbsStkTrue)
                       (MetaBool (UnaryProp _ _
                                            (fun bval => bval = true)
                                            b)))).

Definition afalsestk (b: bexp_stack) (P: AbsState) : AbsState :=
  (AbsAnd P (BaseState (AbsStkTrue)
                       (MetaBool (UnaryProp _ _
                                            (fun bval => bval = false)
                                            b)))).

Definition aimpstk (P Q: AbsState) (fenv: fun_env_stk) : Prop :=
  forall stk,
    absstate_match_rel P fenv stk -> absstate_match_rel Q fenv stk.

Definition aandstk (P Q: assertion): assertion :=
  fun stk => P stk /\ Q stk.

Lemma self_implication :
  forall (s: AbsState) (fenv: fun_env_stk),
    (aimpstk s s fenv).
Proof.
  unfold aimpstk. intros. auto.  
Qed. 

Check (aandstk silly silly).

Lemma anding_silly :
  forall stk,
    ~ (aandstk silly silly stk).
Proof.
  intros. unfold aandstk, not. intros.
  destruct H.
  apply silly_theorem in H.
  assumption.
Qed.



Notation "P --->>> Q" := (aimpstk P Q) (at level 95, no associativity).


Inductive hl_stk : AbsState -> imp_stack -> AbsState -> fun_env_stk -> Type :=
| hl_stk_skip :
  forall P fenv,
    hl_stk P Skip_Stk P fenv
| hl_stk_assign :
  forall P fenv k a P',
    aexp_stack_pure_rel a fenv ->
    state_update_rel k a P P' ->
    hl_stk P' (Assign_Stk k a) P fenv
| hl_stk_push :
  forall P fenv P',
    state_stk_size_inc 1 P P' ->
    hl_stk P (Push_Stk) P' fenv
| hl_stk_pop :
  forall P fenv P' Q,
    state_stk_size_inc 1 P' P ->
    hl_stk (AbsAnd P Q) (Pop_Stk) P' fenv 
| hl_stk_seq :
  forall P Q R i1 i2 fenv,
    hl_stk P i1 R fenv ->
    hl_stk R i2 Q fenv ->
    hl_stk P (Seq_Stk i1 i2) Q fenv
| hl_stk_if :
  forall P Q b i1 i2 fenv,
    bexp_stack_pure_rel b fenv ->
    hl_stk (atruestk b P) i1 Q fenv ->
    hl_stk (afalsestk b P) i2 Q fenv ->
    hl_stk P (If_Stk b i1 i2) Q fenv
| hl_stk_while :
  forall P b i fenv,
    bexp_stack_pure_rel b fenv ->
    hl_stk (atruestk b P) i P fenv ->
    hl_stk P (While_Stk b i) (afalsestk b P) fenv
| hl_stk_consequence :
  forall P Q P' Q' c fenv,
    hl_stk P c Q fenv ->
    (P' --->>> P) fenv ->
    (Q --->>> Q') fenv ->
    hl_stk P' c Q' fenv.

Check hl_stk_ind.






Lemma Hoare_Stk_consequence_pre :
  forall P P' Q i fenv,
    hl_stk P i Q fenv ->
    (P' --->>> P) fenv ->
    hl_stk P' i Q fenv.
Proof.
  intros.
  apply hl_stk_consequence with (P := P) (Q := Q); unfold aimpstk; auto.
Qed.


Lemma Hoare_Stk_consequence_post :
  forall P Q Q' i fenv,
    hl_stk P i Q fenv ->
    (Q --->>> Q') fenv ->
    hl_stk P i Q' fenv.
Proof.
  intros.
  apply hl_stk_consequence with (P := P) (Q := Q); unfold aimpstk; auto.
Qed.


Lemma Hoare_Stk_ifthen :
  forall b i P Q fenv,
    bexp_stack_pure_rel b fenv ->
    hl_stk (atruestk b P) i Q fenv ->
    ((afalsestk b P) --->>> Q) fenv ->
    hl_stk P (If_Stk b i Skip_Stk) Q fenv.
Proof.
  intros. apply (hl_stk_if P Q b i Skip_Stk fenv); auto.
  apply Hoare_Stk_consequence_pre with Q.
  - auto using hl_stk_skip.
  - assumption.
Qed.

Ltac invs H := inversion H; subst.

Lemma triple_stk_skip :
  forall P fenv,
    {{{P}}} Skip_Stk {{{P}}} @ fenv.
Proof.
  unfold triple_stk; intros. invs H. assumption.
Qed.

Lemma triple_stk_assign :
  forall P P' (k: stack_index) (a: aexp_stack) fenv,
    aexp_stack_pure_rel a fenv ->
    state_update_rel k a P P' ->
    {{{P'}}} Assign_Stk k a {{{P}}} @ fenv.
Proof.
  unfold triple_stk, stk_update. intros P P' k a fenv PURE STATE_UP.
  intros.
  invs H.

  pose proof (PURE' := PURE).
  eapply aexp_stack_pure_backwards in PURE.
  unfold aexp_stack_pure in PURE.
  specialize (PURE stk stk'0 c).

  pose proof (H10 := H5).
  apply PURE in H5.
  symmetry in H5.
  subst.
  invs STATE_UP.
  - assert (absstate_well_formed (BaseState s m)).
    econstructor.
    assumption.
    
    eapply state_update_same_as_eval_under_different_state with (k := k) (a := a) (aval := c) (stk := stk) (stk' := stk'); eassumption.
  - assert (absstate_well_formed (AbsAnd s1 s2)) by (econstructor; eassumption).
    eapply state_update_same_as_eval_under_different_state with (k := k) (a := a) (aval := c) (stk := stk) (stk' := stk'); eassumption.
  - assert (absstate_well_formed (AbsOr s1 s2)) by (econstructor; eassumption).
    eapply state_update_same_as_eval_under_different_state with (k := k) (a := a) (aval := c) (stk := stk) (stk' := stk'); eassumption.
Qed.


Ltac absstack_size :=
  match goal with
  | [ |- absstack_match_rel (AbsStkSize 1) (?v :: ?vs) ] =>
      econstructor; simpl; intuition
  end.

Ltac match_inversion :=
  match goal with
  | [ H: absstate_match_rel (BaseState ?s ?Meta) ?fenv ?stk |- _ ] =>
      invs H;
      match goal with
      | [ H': meta_match_rel Meta fenv stk |- _ ] =>
          invs H';
          match goal with
          | [ H'' : eval_prop_rel ?func ?LogProp |- _ ] =>
              invs H''
          end;
          match goal with
          | [ H''' : prop_rel ?func ?LogProp |- _ ] =>
              invs H'''
          end
      end
  end;
  match goal with
  | [ H : absstate_well_formed (BaseState ?s ?Meta) |- _ ] =>
      invs H;
      match goal with
      | [ H' : mv_well_formed Meta |- _ ] =>
          invs H'
      | [ |- _ ] =>
          idtac
      end
  | [ |- _ ] =>
      idtac
  end.


Ltac meta_match_elimination_helper p1 p2 p1' p2' :=
  match goal with
  | [ H': transformed_prop_exprs _ p1 p1' |- _ ] =>
      econstructor
  | [ H': transformed_prop_exprs _ p2 p2' |- _ ] =>
      eapply RelOrPropRight
  end.

Ltac meta_match_elimination :=
  match goal with
  | [  |- meta_match_rel (_ (OrProp ?ValType ?ExprType ?p1' ?p2')) ?fenv ?stk ] =>
      econstructor;
      match goal with
      | [ H: eval_prop_rel _ (OrProp ValType ExprType ?p1 ?p2)  |- _ ] =>
          match goal with
          | [ H': eval_prop_rel _ p1 |- _ ] =>
              econstructor
          | [ H': eval_prop_rel _ p2 |- _ ] =>
              eapply RelOrPropRight
          end
      | [ |- _ ] =>
          idtac
      end
  | [ |- meta_match_rel _ _ _ ] =>
      econstructor;
      econstructor
  end.

Ltac smart_pure_helper :=
  match goal with
  | [  H0 : transformed_prop_exprs (bexp_stk_size_inc_rel 1) ?p1 ?p1', H13 : prop_rel
          (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr ?fenv)
          ?p1
       |- prop_rel
           (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr ?fenv) ?p1' ] =>
      eapply bool_prop_rel_prop_stk_inc_preserves_purity; [ eapply H13 | eassumption]
  | [ H0: transformed_prop_exprs_args (bexp_stk_size_inc_rel 1) ?args ?args',
        H1: prop_args_rel (fun boolexpr : bexp_stack =>
                             bexp_stack_pure_rel boolexpr ?fenv)
                          ?args |-
        prop_args_rel (fun boolexpr : bexp_stack =>
                         bexp_stack_pure_rel boolexpr ?fenv)
                      ?args' ] =>
      eapply bool_prop_args_rel_prop_stk_inc_preserves_purity; eassumption
  | [ H0: bexp_stk_size_inc_rel 1 ?a ?a',
        H1: bexp_stack_pure_rel ?a ?fenv |-
        bexp_stack_pure_rel ?a' ?fenv ] =>
      eapply bexp_size_inc_preserves_purity; eassumption
                                                            
  | [  H0 : transformed_prop_exprs (aexp_stk_size_inc_rel 1) ?p1 ?p1',
       H13 : prop_rel
               (fun natexpr : aexp_stack =>
                  aexp_stack_pure_rel natexpr ?fenv)
               ?p1
       |- prop_rel
           (fun natexpr : aexp_stack =>
              aexp_stack_pure_rel natexpr ?fenv)
           ?p1' ] =>
      eapply nat_prop_rel_prop_stk_inc_preserves_purity; [ eapply H13 | eassumption]
  | [ H0: aexp_stk_size_inc_rel 1 ?a ?a',
        H1: aexp_stack_pure_rel ?a ?fenv |-
        aexp_stack_pure_rel ?a' ?fenv ] =>
      eapply aexp_size_inc_preserves_purity; eassumption
  | [ H0: transformed_prop_exprs_args (aexp_stk_size_inc_rel 1) ?args ?args',
        H1: prop_args_rel (fun natexpr : aexp_stack =>
                             aexp_stack_pure_rel natexpr ?fenv)
                          ?args |-
        prop_args_rel (fun natexpr : aexp_stack =>
                         aexp_stack_pure_rel natexpr ?fenv)
                      ?args' ] =>
      eapply nat_prop_args_rel_prop_stk_inc_preserves_purity; eassumption
        
  end.



Lemma triple_stk_push :
  forall P Q fenv,
    state_stk_size_inc 1 P Q ->
    {{{P}}} Push_Stk {{{Q}}} @ fenv.
Proof.
  unfold triple_stk.
  induction P; intros Q fenv INC stk stk' IMP MATCH.
  - invs INC.
    invs H2; invs IMP.
    + econstructor; [absstack_size | ].
      invs H4.
      * invs H; match_inversion; meta_match_elimination; try smart_pure_helper.
        1,3,4,10-12: eapply bexp_stack_increase_preserves_eval; eassumption.
        3-6: eapply logic_stack_increase_preserves_eval; eassumption.
        4: eapply bool_args_stack_increase_preserves_eval; eassumption.
        all: try eassumption; try eapply bexp_size_inc_preserves_purity; try eassumption; try smart_pure_helper.
      * invs H; match_inversion; meta_match_elimination; try smart_pure_helper.
        1,3,4,10-12: eapply aexp_stack_increase_preserves_eval; eassumption.
        3-6: eapply nat_logic_stack_increase_preserves_eval; eassumption.
        4: eapply nat_args_stack_increase_preserves_eval; eassumption.
        all: try assumption.        
    + econstructor.
      * invs MATCH.
        invs H1.
        econstructor.
        simpl.
        intuition.
      * invs H4.
        -- invs H; match_inversion; meta_match_elimination; try smart_pure_helper;
             try eapply bexp_stack_increase_preserves_eval; try eapply logic_stack_increase_preserves_eval; try eapply bool_args_stack_increase_preserves_eval; eassumption.
        -- invs H; match_inversion; meta_match_elimination; try smart_pure_helper; try eapply aexp_stack_increase_preserves_eval; try eapply nat_logic_stack_increase_preserves_eval; try eapply nat_args_stack_increase_preserves_eval; eassumption.
  - invs INC. invs MATCH.
    econstructor.
    + eapply IHP1; eassumption.
    + eapply IHP2; eassumption.
  - invs INC. invs MATCH.
    + econstructor. eapply IHP1.
      * eassumption.
      * eassumption.
      * assumption.
    + eapply RelAbsOrRight. eapply IHP2; eassumption.
Qed.

Ltac smart_pure_helper' :=
  match goal with
  | [  H0 : transformed_prop_exprs (bexp_stk_size_inc_rel 1) ?p1 ?p1', H13 : prop_rel
          (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr ?fenv)
          ?p1',
          H14: prop_rel bexp_well_formed ?p1
       |- prop_rel
           (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr ?fenv) ?p1 ] =>
      eapply bool_prop_rel_prop_stk_inc_preserves_purity';
      [eapply H13 | unfold bool_prop_wf; unfold_prop_helpers | eapply H0 ];
      eassumption
  | [ H0: transformed_prop_exprs_args (bexp_stk_size_inc_rel 1) ?args ?args',
        H1: prop_args_rel (fun boolexpr : bexp_stack =>
                             bexp_stack_pure_rel boolexpr ?fenv)
                          ?args',
          H2: prop_args_rel bexp_well_formed ?args |-
        
        prop_args_rel (fun boolexpr : bexp_stack =>
                         bexp_stack_pure_rel boolexpr ?fenv)
                      ?args ] =>
      eapply bool_prop_args_rel_prop_stk_inc_preserves_purity'; eassumption
  | [ H0: bexp_stk_size_inc_rel 1 ?a ?a',
        H1: bexp_stack_pure_rel ?a' ?fenv,
          H2: bexp_well_formed ?a
      |-
        bexp_stack_pure_rel ?a ?fenv ] =>
      eapply bexp_size_inc_preserves_purity'; eassumption
                                                            
  | [  H0 : transformed_prop_exprs (aexp_stk_size_inc_rel 1) ?p1 ?p1',
       H13 : prop_rel
               (fun natexpr : aexp_stack =>
                  aexp_stack_pure_rel natexpr ?fenv)
               ?p1',
          H14 : prop_rel aexp_well_formed ?p1
       |- prop_rel
           (fun natexpr : aexp_stack =>
              aexp_stack_pure_rel natexpr ?fenv)
           ?p1 ] =>
      eapply nat_prop_rel_prop_stk_inc_preserves_purity';
      [ eapply H13 | unfold nat_prop_wf; unfold_prop_helpers | eapply H0];
      eassumption
  | [ H0: aexp_stk_size_inc_rel 1 ?a ?a',
        H1: aexp_stack_pure_rel ?a' ?fenv |-
        aexp_stack_pure_rel ?a ?fenv ] =>
      eapply aexp_size_inc_preserves_purity'; eassumption
  | [ H0: transformed_prop_exprs_args (aexp_stk_size_inc_rel 1) ?args ?args',
        H1: prop_args_rel (fun natexpr : aexp_stack =>
                             aexp_stack_pure_rel natexpr ?fenv)
                          ?args' |-
        prop_args_rel (fun natexpr : aexp_stack =>
                         aexp_stack_pure_rel natexpr ?fenv)
                      ?args ] =>
      eapply nat_prop_args_rel_prop_stk_inc_preserves_purity'; eassumption
        
  end.

Ltac match_inversion' :=
  match goal with
  | [ H: absstate_match_rel (AbsAnd (BaseState ?s ?Meta) ?Q) ?fenv ?stk |- _ ] =>
      invs H;
      match goal with
      | [ META: absstate_match_rel (BaseState s Meta) fenv stk |- _ ] =>
          invs META;
          match goal with
          | [ H': meta_match_rel Meta fenv stk |- _ ] =>
              invs H';
             match goal with
              | [ H'' : eval_prop_rel ?func ?LogProp |- _ ] =>
                  invs H''
                        
              end;
              match goal with
              | [ H''' : prop_rel ?func ?LogProp |- _ ] =>
                  invs H''';
                  try (match goal with
                       | [ H''': prop_rel func LogProp,
                           H2 : prop_rel ?func2 ?LogProp2 |- _ ] =>
                      invs H2
                       end)
                  
              end
          end
      end
  end;
  match goal with
  | [ H : absstate_well_formed (BaseState ?s ?Meta) |- _ ] =>
      invs H;
      match goal with
      | [ H' : mv_well_formed Meta |- _ ] =>
          invs H'
      | [ |- _ ] =>
          idtac
      end
  | [ |- _ ] =>
      idtac
  end;
  match goal with
  | [ H : meta_stk_size_inc ?inc (_ ?l1) (_ ?l2) |- _ ] =>
      invs H;
      match goal with
      | [ H' : transformed_prop_exprs (?func inc) l1 l2 |- _ ] =>
          invs H'
      end
  end.

Ltac smart_wf_helper :=
  match goal with
  | [ H : prop_rel bexp_well_formed ?p |- _ ] =>
      invs H
  | [ H: prop_rel aexp_well_formed ?p |- _ ] =>
      invs H
  end.


Ltac smart_expr_stack_increase_preserves_eval' inc_rel pure_rel wf_rel stack_sem :=
  match goal with
  | [ H1 : inc_rel 1 ?a ?a',
        H2 : pure_rel ?a' ?fenv,
          
          H3: wf_rel ?a,
      H4 : stack_sem ?a' ?fenv (?v :: ?stk) (?v :: ?stk, ?aval) |-
        stack_sem ?a ?fenv ?stk (?stk, ?val) ] =>
      let INC := fresh "INC" in
      pose proof (INC := H1);
      match inc_rel with
      | bexp_stk_size_inc_rel =>
          (eapply bexp_size_inc_preserves_purity' in INC ; [ | eassumption .. ]);
          eapply bexp_stack_increase_preserves_eval'; eassumption
      | aexp_stk_size_inc_rel =>
          (eapply aexp_size_inc_preserves_purity' in INC; [ | eassumption .. ]);
          eapply aexp_stack_increase_preserves_eval'; eassumption
      end
  end.

Ltac smart_bexp_stack_increase_preserves_eval' :=
  (smart_expr_stack_increase_preserves_eval'
     aexp_stk_size_inc_rel
     aexp_stack_pure_rel
     aexp_well_formed
     aexp_stack_sem)
  ||
  (smart_expr_stack_increase_preserves_eval'
     bexp_stk_size_inc_rel
     bexp_stack_pure_rel
     bexp_well_formed
     bexp_stack_sem).

Ltac match_logic_prop H p1 m tac :=
  match m with
  | AndProp _ _ p1 _ =>
      invs H;
      tac
  | OrProp _ _ p1 _ =>
      invs H; tac
  | AndProp _ _ _ p1 =>
      invs H; tac
  | OrProp _ _ _ p1 =>
      invs H; tac
  end.

Ltac smart_transformed_prop_exprs inc_rel p1 tac tac1 tac2 :=
  match goal with
  | [ H : transformed_prop_exprs (inc_rel 1) p1 ?p1' |- _ ] =>
      tac1 H
  | [ H : transformed_prop_exprs (inc_rel 1) ?p1' p1 |- _ ] =>
      tac2 H
  | [ H : transformed_prop_exprs (inc_rel 1) ?m ?n |- _ ] =>
      match_logic_prop H p1 m tac
  end.


Ltac smart_logic_stack_increase_preserves_eval'_bool_prop_wf prop_rel_prop p1 tac tac1 :=
   match goal with
   | [ H : prop_rel prop_rel_prop p1 |- _ ] =>
       tac1 H
   | [ H : prop_rel prop_rel_prop ?m |- _ ] =>
       match_logic_prop H p1 m tac
   end.

Ltac smart_logic_stack_increase_preserves_eval' :=
  match goal with
  | [ |- transformed_prop_exprs (?inc_rel 1) ?p1 ?[?p'] ] =>
      smart_transformed_prop_exprs inc_rel p1 ltac:(eassumption) ltac:(fun H => eapply H) ltac:(idtac)
  | [ |- bool_prop_wf ?p1 ] =>
      unfold bool_prop_wf;
      smart_logic_stack_increase_preserves_eval'_bool_prop_wf bexp_well_formed p1 ltac:(eassumption) ltac:(fun H => eapply H)
  | [ |- nat_prop_wf ?p1 ] =>
      unfold nat_prop_wf;
      smart_logic_stack_increase_preserves_eval'_bool_prop_wf aexp_well_formed p1 ltac:(eassumption) ltac:(fun H => eapply H)
  | [ |- prop_rel (fun boolexpr : ?expr_type => ?pure_rel boolexpr ?fenv) ?p1 ] =>
      match pure_rel with
      | bexp_stack_pure_rel =>
          smart_pure_helper'
      | aexp_stack_pure_rel =>
          smart_pure_helper'
      end
  | [ |- _ ] =>
      eassumption
  end.





Ltac small_smart_pure_helper inc_rel tac1 tac3 :=
  match inc_rel with
  | bexp_stk_size_inc_rel =>
      eapply bool_prop_rel_prop_stk_inc_preserves_purity';
      [
        tac1
      | smart_wf_helper
      | tac3 ]
  | aexp_stk_size_inc_rel =>
      eapply nat_prop_rel_prop_stk_inc_preserves_purity';
      [
        tac1
      | smart_wf_helper
      | tac3 ]
  end.

Lemma triple_stk_pop :
  forall P' P Q fenv,
    state_stk_size_inc 1 P' P ->
    {{{(AbsAnd P Q)}}} Pop_Stk {{{ P' }}} @ fenv.
Proof.
  unfold triple_stk.
  induction P'; intros P Q fenv INC stk stk' IMP MATCH.
  - invs IMP.
    invs INC.
    invs H2.
    + econstructor; [ econstructor | ].
      invs H4.
      * invs H; match_inversion'; meta_match_elimination; try smart_wf_helper; try smart_pure_helper'.
        all: try smart_bexp_stack_increase_preserves_eval'.
        all: try (eapply logic_stack_increase_preserves_eval'; smart_logic_stack_increase_preserves_eval').
        4: eapply bool_args_stack_increase_preserves_eval'; try eassumption; try smart_pure_helper'.
        all: eassumption.
      * invs H; match_inversion'; meta_match_elimination; try smart_wf_helper; try smart_pure_helper'.
        all: try (smart_bexp_stack_increase_preserves_eval').
        all: try (eapply nat_logic_stack_increase_preserves_eval'; smart_logic_stack_increase_preserves_eval').
        4: eapply nat_args_stack_increase_preserves_eval'; try eassumption; try smart_pure_helper'.
        all: assumption.
    + econstructor.
      * invs MATCH.
        invs H1.
        invs H3.
        constructor.
        simpl in H0.
        intuition.
      * invs H4.
        -- invs H; match_inversion'; meta_match_elimination; try smart_wf_helper; try smart_pure_helper'.
           all: try (smart_bexp_stack_increase_preserves_eval').
           all: try (eapply logic_stack_increase_preserves_eval'; smart_logic_stack_increase_preserves_eval').
           4: eapply bool_args_stack_increase_preserves_eval'; try eassumption; try smart_pure_helper'.
           all: assumption.
        -- invs H; match_inversion'; meta_match_elimination; try smart_wf_helper; try smart_pure_helper'.
           all: try smart_bexp_stack_increase_preserves_eval'.
           all: try (eapply nat_logic_stack_increase_preserves_eval'; smart_logic_stack_increase_preserves_eval').
           all: try (eapply aexp_stack_increase_preserves_eval'; [ | | eapply aexp_size_inc_preserves_purity' | ]; eassumption).
           4: eapply nat_args_stack_increase_preserves_eval'; try eassumption; try smart_pure_helper'.
           all: assumption.
  - invs MATCH. invs INC.
    econstructor.
    + eapply IHP'1; eassumption.
    + eapply IHP'2.
      eassumption.
      eassumption.
      invs MATCH.
      assert (absstate_match_rel (AbsAnd s2' Q) fenv stk).
      * invs H2.
        constructor; assumption.
      * eassumption.
  - invs MATCH. invs INC.
    invs H1.
    + econstructor. eapply IHP'1.
      eassumption.
      eassumption.
      assert (absstate_match_rel (AbsAnd s1' Q) fenv stk).
      * constructor; assumption.
      * eassumption.
    + eapply RelAbsOrRight. eapply IHP'2.
      eassumption.
      eassumption.
      assert (absstate_match_rel (AbsAnd s2' Q) fenv stk).
      * constructor; assumption.
      * eassumption.
Qed.


Local Open Scope stack_scope.

Lemma triple_stk_seq :
  forall P Q R i1 i2 fenv,
    {{{P}}} i1 {{{Q}}} @ fenv ->
    {{{Q}}} i2 {{{R}}} @ fenv ->
    {{{P}}} i1 ;;; i2 {{{R}}} @ fenv.
Proof.
  unfold triple_stk; intros.
  invs H1.
  apply H in H5.
  - apply H0 in H9.
    + assumption.
    + assumption.
  - assumption.
Qed.


Lemma triple_stk_ifthenelse :
  forall P Q b i1 i2 fenv,
    bexp_stack_pure_rel b fenv ->
    {{{(atruestk b P)}}} i1 {{{Q}}} @ fenv ->
    {{{(afalsestk b P)}}} i2 {{{Q}}} @ fenv ->
    {{{P}}} ifs b thens i1 elses i2 dones {{{Q}}} @ fenv.
Proof.
  unfold triple_stk, atruestk, afalsestk, bexp_stack_pure; intros.
  invs H2.
  - apply H0 in H11.
    + assumption.
    + pose proof (PURE := H).
      eapply (bexp_stack_pure_implication) in PURE.
      unfold bexp_stack_pure in PURE.
      pose proof (H12 := H10).
      apply PURE in H10.
      subst.
      econstructor.
      * assumption.
      * econstructor.
        -- econstructor.
        -- econstructor.
           econstructor.
           eassumption.
           reflexivity.
           econstructor.
           eassumption.
  - apply H1 in H11.
    + assumption.
    + pose proof (PURE := H).
      eapply (bexp_stack_pure_implication) in H.
      specialize (H stk stk'0 false).
      pose proof (H12 := H10).
      apply H in H10; subst.
      econstructor.
      * assumption.
      * econstructor.
        -- econstructor.
        -- econstructor.
           ++ econstructor.
              ** eassumption.
              ** reflexivity.
           ++ econstructor. assumption.
Qed.

Lemma triple_stk_while :
  forall P b l fenv,
    bexp_stack_pure_rel b fenv ->
    {{{atruestk b P}}} l {{{P}}} @ fenv ->
    {{{P}}} whiles b loops l dones {{{afalsestk b P}}} @ fenv.
Proof.
  unfold triple_stk, afalsestk, bexp_stack_pure; intros P b l fenv PURE TRUE_LOOP stk stk' SEM.
  dependent induction SEM; intros.
  - pose proof (PURE' := PURE).
    eapply bexp_stack_pure_implication in PURE.
    specialize (PURE stk stk' false).
    pose proof (H1 := H).
    apply PURE in H. subst.

    econstructor; [assumption | ].
    econstructor; [econstructor | ].
    econstructor; [ |  econstructor; eassumption].
    econstructor; [eassumption | reflexivity].
  - pose proof (PURE' := PURE).
    eapply bexp_stack_pure_implication in PURE'.
    specialize (PURE' stk stk1 true).

    pose proof (H1 := H).
    apply PURE' in H.
    subst.
    eapply IHSEM2; eauto.
    specialize (TRUE_LOOP stk1 stk2).
    apply TRUE_LOOP in SEM1.
    + assumption.
    + unfold atruestk. econstructor; [assumption |].
      econstructor; [econstructor|].
      econstructor. econstructor.
      * eassumption.
      * reflexivity.
      * econstructor; eassumption.
Qed.

Lemma triple_stk_consequence :
  forall P Q P' Q' i fenv,
    {{{P}}} i {{{Q}}} @ fenv ->
    (P' --->>> P) fenv ->
    (Q --->>> Q') fenv ->
    {{{P'}}} i {{{Q'}}} @ fenv.
Proof.
  unfold triple_stk, aimpstk; intros. eauto.
Qed.

Theorem Hoare_stk_sound :
  forall P i Q fenv,
    hl_stk P i Q fenv ->
    {{{P}}} i {{{Q}}} @ fenv.
Proof.
  induction 1;
    eauto using triple_stk_skip, triple_stk_assign, triple_stk_seq, triple_stk_ifthenelse, triple_stk_while, triple_stk_consequence, triple_stk_push, triple_stk_pop.
Qed.

  


      


