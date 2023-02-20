From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet ZArith.
From DanTrick Require Import DanTrickLanguage DanLogicHelpers StackLanguage StackLangEval StackLangTheorems.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Fixpoint free_vars_aexp_src exp := 
match exp with
| CONST_Dan n => (empty_set string)
| VAR_Dan x => set_add string_dec x (empty_set string)
| PARAM_Dan n => (empty_set string)
| PLUS_Dan a1 a2 => 
  set_union string_dec (free_vars_aexp_src a1) (free_vars_aexp_src a2)
| MINUS_Dan a1 a2 => 
  set_union string_dec (free_vars_aexp_src a1) (free_vars_aexp_src a2)
| APP_Dan f aexps => 
  fold_left 
  (fun x y => set_union  string_dec x (free_vars_aexp_src y)) 
  aexps 
  (empty_set string)
end
.

Fixpoint free_vars_bexp_src exp := 
match exp with
| TRUE_Dan => (empty_set string)
| FALSE_Dan => (empty_set string)
| NEG_Dan b => free_vars_bexp_src b
| AND_Dan b1 b2 => 
  set_union string_dec (free_vars_bexp_src b1) (free_vars_bexp_src b2)
| OR_Dan  b1 b2 =>
  set_union string_dec (free_vars_bexp_src b1) (free_vars_bexp_src b2)
| LEQ_Dan a1 a2 => 
  set_union string_dec (free_vars_aexp_src a1) (free_vars_aexp_src a2)
end
.

Fixpoint free_vars_imp_src (imp: imp_Dan): set string :=
  match imp with
  |IF_Dan b i1 i2 => 
     let i_vars :=   
       set_union string_dec (free_vars_imp_src i1) (free_vars_imp_src i2) in
     set_union string_dec (free_vars_bexp_src b) i_vars
  |SKIP_Dan => (empty_set string)
  |WHILE_Dan b i => 
     set_union string_dec (free_vars_imp_src i) (free_vars_bexp_src b)
  |ASSIGN_Dan x a => set_add string_dec x (free_vars_aexp_src a)
  |SEQ_Dan i1 i2 => 
     set_union string_dec (free_vars_imp_src i1) (free_vars_imp_src i2)
  end
.


(* one indexes a list, returns 1 + length if element not a thing *)
Fixpoint one_index_opt elt lst :=
  match lst with
  |nil => 1
  |x::t => if string_dec x elt then 1 else (1 + (one_index_opt elt t))
  end
.

Definition ident_list_to_map (ident_list: list ident): ident -> nat :=
  fun x => one_index_opt x ident_list.

Fixpoint find_index (local_vars: list ident) (x: ident): option nat :=
  match local_vars with
  | nil => None
  | var :: vars =>
      if string_dec x var
      then Some 0
      else match (find_index vars x) with
           | None =>
               None
           | Some n =>
               Some (n + 1)
           end
  end.



Definition construct_trans (imp: imp_Dan): (list ident) := 
  let free_vars := 
    free_vars_imp_src imp in
  let stk := 
    set_fold_left (fun acc x => x :: acc) free_vars nil in
  stk.


(* Given a stack of variables in terms of a list, returns a mapping from those
variables to their index in the list *)
Definition stack_mapping (imp: imp_Dan): ident -> nat := 
  fun x => one_index_opt x (construct_trans imp).

Local Definition no_other_index_has_same (index: nat) (x: ident) (vars: list ident): Prop :=
  forall k,
    k <> index ->
    nth_error vars k <> Some x.


Inductive find_index_rel: list ident -> ident -> option nat -> Prop :=
| FindIndexNil :
  forall (x: ident),
    find_index_rel nil x None
| FindIndexFirstFound :
  forall (vars: list ident) (x: ident) (var: ident),
    x = var ->
    find_index_rel (var :: vars) x (Some 0)
| FindIndexRestFound :
  forall (vars: list ident) (x: ident) (var: ident) (n: nat),
    x <> var ->
    find_index_rel vars x (Some n) ->
    find_index_rel (var :: vars) x (Some (S n))
| FindIndexNotFound :
  forall (vars: list ident) (x: ident) (var: ident),
    x <> var ->
    find_index_rel vars x None ->
    find_index_rel (var :: vars) x None.

Inductive aexp_has_variable : ident -> aexp_Dan -> Prop :=
| AexpHasVarVar :
  forall (id x: ident),
    String.eqb id x = true ->
    aexp_has_variable id (VAR_Dan x)
| AexpHasVarPlus__left :
  forall (id: ident) (a1 a2: aexp_Dan),
    aexp_has_variable id a1 ->
    aexp_has_variable id (PLUS_Dan a1 a2)
| AexpHasVarPlus__right :
  forall (id: ident) (a1 a2: aexp_Dan),
    aexp_has_variable id a2 ->
    aexp_has_variable id (PLUS_Dan a1 a2)
| AexpHasVarMinus__left :
  forall (id: ident) (a1 a2: aexp_Dan),
    aexp_has_variable id a1 ->
    aexp_has_variable id (MINUS_Dan a1 a2)
| AexpHasVarMinus__right :
  forall (id: ident) (a1 a2: aexp_Dan),
    aexp_has_variable id a2 ->
    aexp_has_variable id (MINUS_Dan a1 a2)
| AexpHasVarApp :
  forall (id: ident) (f: ident) (args: list aexp_Dan),
    args_has_variable id args ->
    aexp_has_variable id (APP_Dan f args)
with args_has_variable : ident -> list aexp_Dan -> Prop :=
| ArgsHasVarFirst :
  forall (id: ident) (arg: aexp_Dan) (args: list aexp_Dan),
    aexp_has_variable id arg ->
    args_has_variable id (arg :: args)
| ArgsHasVarRest :
  forall (id: ident) (arg: aexp_Dan) (args: list aexp_Dan),
    args_has_variable id args ->
    args_has_variable id (arg :: args).

Inductive bexp_has_variable: ident -> bexp_Dan -> Prop :=
| BexpHasVarNeg :
  forall (id: ident) (b: bexp_Dan),
    bexp_has_variable id b ->
    bexp_has_variable id (NEG_Dan b)
| BexpHasVarAnd__left :
  forall (id: ident) (b1 b2: bexp_Dan),
    bexp_has_variable id b1 ->
    bexp_has_variable id (AND_Dan b1 b2)
| BexpHasVarAnd__right :
  forall (id: ident) (b1 b2: bexp_Dan),
    bexp_has_variable id b2 ->
    bexp_has_variable id (AND_Dan b1 b2)
| BexpHasVarOr__left :
  forall (id: ident) (b1 b2: bexp_Dan),
    bexp_has_variable id b1 ->
    bexp_has_variable id (OR_Dan b1 b2)
| BexpHasVarOr__right :
  forall (id: ident) (b1 b2: bexp_Dan),
    bexp_has_variable id b2 ->
    bexp_has_variable id (OR_Dan b1 b2)                      
| BexpHasVarLeq__left :
  forall (id: ident) (a1 a2: aexp_Dan),
    aexp_has_variable id a1 ->
    bexp_has_variable id (LEQ_Dan a1 a2)
| BexpHasVarLeq__right :
  forall (id: ident) (a1 a2: aexp_Dan),
    aexp_has_variable id a2 ->
    bexp_has_variable id (LEQ_Dan a1 a2).
    

Inductive imp_has_variable : ident -> imp_Dan -> Prop :=
| ImpHasVarAssignee :
  forall (id: ident) (x: ident) (a: aexp_Dan),
    String.eqb id x = true ->
    imp_has_variable id (ASSIGN_Dan x a)
| ImpHasVarAssigned :
  forall (id: ident) (x: ident) (a: aexp_Dan),
    aexp_has_variable id a ->
    imp_has_variable id (ASSIGN_Dan x a)
| ImpHasVarSeq__left :
  forall (id: ident) (i1 i2: imp_Dan),
    imp_has_variable id i1 ->
    imp_has_variable id (SEQ_Dan i1 i2)
| ImpHasVarSeq__right :
  forall (id: ident) (i1 i2: imp_Dan),
    imp_has_variable id i2 ->
    imp_has_variable id (SEQ_Dan i1 i2)
| ImpHasVarIf__cond :
  forall (id: ident) (b: bexp_Dan) (i__then i__else : imp_Dan),
    bexp_has_variable id b ->
    imp_has_variable id (IF_Dan b i__then i__else)
| ImpHasVarIf__then :
  forall (id: ident) (b: bexp_Dan) (i__then i__else : imp_Dan),
    imp_has_variable id i__then ->
    imp_has_variable id (IF_Dan b i__then i__else)
| ImpHasVarIf__else :
  forall (id: ident) (b: bexp_Dan) (i__then i__else : imp_Dan),
    imp_has_variable id i__else ->
    imp_has_variable id (IF_Dan b i__then i__else)
| ImpHasVarWhile__cond :
  forall (id: ident) (b: bexp_Dan) (i__body : imp_Dan),
    bexp_has_variable id b ->
    imp_has_variable id (WHILE_Dan b i__body)
| ImpHasVarWhile__body :
  forall (id: ident) (b: bexp_Dan) (i__body : imp_Dan),
    imp_has_variable id i__body ->
    imp_has_variable id (WHILE_Dan b i__body).

Ltac find_right_branch_of_disjunction H2 :=
  let typeH2 := type of H2 in
  match goal with
  | [ |- typeH2 ] =>
      eassumption
  | [ |- typeH2 \/ _ ] =>
      left; eassumption
  | _ =>
      right;
      find_right_branch_of_disjunction H2
  end.



Lemma imp_has_variable_assign_iff :
  forall (assignee: ident) (a: aexp_Dan) (x: ident),
    imp_has_variable x (ASSIGN_Dan assignee a) <->
      String.eqb x assignee = true \/ aexp_has_variable x a.
Proof.
  split; intros.
  - invs H; find_right_branch_of_disjunction H2.
  - destruct H.
    + eapply ImpHasVarAssignee. eassumption.
    + eapply ImpHasVarAssigned. eassumption.
Qed.

Lemma imp_has_variable_seq_iff :
  forall (i1 i2: imp_Dan) (x: ident),
    imp_has_variable x (SEQ_Dan i1 i2) <->
      imp_has_variable x i1 \/ imp_has_variable x i2.
Proof.
  split; intros.
  - invs H; find_right_branch_of_disjunction H2.
  - destruct H.
    + eapply ImpHasVarSeq__left. eassumption.
    + eapply ImpHasVarSeq__right. eassumption.
Qed.

Lemma imp_has_variable_if_iff :
  forall (b: bexp_Dan) (i1 i2: imp_Dan) (x: ident),
    imp_has_variable x (IF_Dan b i1 i2) <->
      (bexp_has_variable x b) \/ (imp_has_variable x i1) \/ (imp_has_variable x i2).
Proof.
  split; intros.
  - invs H; find_right_branch_of_disjunction H2.
  - destruct H as [ H | [H | H]].
    + eapply ImpHasVarIf__cond. eassumption.
    + eapply ImpHasVarIf__then. eassumption.
    + eapply ImpHasVarIf__else. eassumption.
Qed.

Lemma imp_has_variable_while_iff :
  forall (b: bexp_Dan) (i__body : imp_Dan) (x: ident),
    imp_has_variable x (WHILE_Dan b i__body) <->
      bexp_has_variable x b \/ imp_has_variable x i__body.
Proof.
  split; intros.
  - invs H; find_right_branch_of_disjunction H2.
  - destruct H.
    + eapply ImpHasVarWhile__cond. eassumption.
    + eapply ImpHasVarWhile__body. eassumption.
Qed.

Inductive imp_existence_relation_on_aexps_bexps : (aexp_Dan -> Prop) -> (bexp_Dan -> Prop) -> imp_Dan -> Prop :=
| ImpExistenceVar :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (x: ident) (a: aexp_Dan),
    p__a a ->
    imp_existence_relation_on_aexps_bexps p__a p__b (ASSIGN_Dan x a)
| ImpExistenceSeq__left :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (i1 i2: imp_Dan),
    imp_existence_relation_on_aexps_bexps p__a p__b i1 ->
    imp_existence_relation_on_aexps_bexps p__a p__b (SEQ_Dan i1 i2)
| ImpExistenceSeq__right :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (i1 i2: imp_Dan),
    imp_existence_relation_on_aexps_bexps p__a p__b i2 ->
    imp_existence_relation_on_aexps_bexps p__a p__b (SEQ_Dan i1 i2)
| ImpExistenceIf__cond :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i__then i__else : imp_Dan),
    p__b b ->
    imp_existence_relation_on_aexps_bexps p__a p__b (IF_Dan b i__then i__else)
| ImpExistenceIf__then :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i__then i__else : imp_Dan),
    imp_existence_relation_on_aexps_bexps p__a p__b i__then ->
    imp_existence_relation_on_aexps_bexps p__a p__b (IF_Dan b i__then i__else)
| ImpExistenceIf__else :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i__then i__else : imp_Dan),
    imp_existence_relation_on_aexps_bexps p__a p__b i__else ->
    imp_existence_relation_on_aexps_bexps p__a p__b (IF_Dan b i__then i__else)
| ImpExistenceWhile__cond :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i__body : imp_Dan),
    p__b b ->
    imp_existence_relation_on_aexps_bexps p__a p__b (WHILE_Dan b i__body)
| ImpExistenceWhile__body :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i__body : imp_Dan),
    imp_existence_relation_on_aexps_bexps p__a p__b i__body ->
    imp_existence_relation_on_aexps_bexps p__a p__b (WHILE_Dan b i__body).

Inductive imp_forall_relation_on_aexps_bexps : (aexp_Dan -> Prop) -> (bexp_Dan -> Prop) -> imp_Dan -> Prop :=
| ImpForallSkip :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop),
    imp_forall_relation_on_aexps_bexps p__a p__b SKIP_Dan
| ImpForallAssign :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (x: ident) (a: aexp_Dan),
    p__a a ->
    imp_forall_relation_on_aexps_bexps p__a p__b (ASSIGN_Dan x a)
| ImpForallSeq :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (i1 i2: imp_Dan),
    imp_forall_relation_on_aexps_bexps p__a p__b i1 ->
    imp_forall_relation_on_aexps_bexps p__a p__b i2 ->
    imp_forall_relation_on_aexps_bexps p__a p__b (SEQ_Dan i1 i2)
| ImpForallIf :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i1 i2: imp_Dan),
    p__b b ->
    imp_forall_relation_on_aexps_bexps p__a p__b i1 ->
    imp_forall_relation_on_aexps_bexps p__a p__b i2 ->
    imp_forall_relation_on_aexps_bexps p__a p__b (IF_Dan b i1 i2)
| ImpForallWhile :
  forall (p__a: aexp_Dan -> Prop) (p__b: bexp_Dan -> Prop) (b: bexp_Dan) (i__loop : imp_Dan),
    p__b b ->
    imp_forall_relation_on_aexps_bexps p__a p__b i__loop ->
    imp_forall_relation_on_aexps_bexps p__a p__b (WHILE_Dan b i__loop).

  
Definition var_map_wf (var_map_list: list ident) : Prop :=
  NoDup var_map_list
  /\ (forall (x: ident) (index: nat),
        0 <= index < Datatypes.length var_map_list ->
        (find_index_rel var_map_list x (Some index) <->
           one_index_opt x var_map_list = S index))
  /\ (forall (x: ident),
        In x var_map_list ->
        exists (index: nat),
          one_index_opt x var_map_list = S index)
  /\ (forall (x: ident) (imp: imp_Dan),
        In x var_map_list ->
        var_map_list = construct_trans imp ->
        imp_has_variable x imp).

Definition var_map_wf_wrt_aexp (var_map_list: list ident) (aexp: aexp_Dan): Prop :=
  var_map_wf var_map_list
  /\ (forall x (aexp_var_map: set ident),
        aexp_var_map = free_vars_aexp_src aexp ->
        In x aexp_var_map ->
        In x var_map_list)
  /\ (forall x (aexp_var_map: set ident),
        aexp_var_map = free_vars_aexp_src aexp ->
        In x aexp_var_map ->
        aexp_has_variable x aexp)
  /\ (forall x (aexp_var_map: set ident),
        aexp_var_map = free_vars_aexp_src aexp ->
        In x aexp_var_map ->
        exists index,
          find_index_rel var_map_list x (Some index))
  /\ (forall x (f: ident) (args: list aexp_Dan) (aexp_var_map: set ident),
        aexp = APP_Dan f args ->
        aexp_var_map = free_vars_aexp_src aexp ->
        In x aexp_var_map ->
        args_has_variable x args).

Definition var_map_wf_wrt_bexp (var_map_list: list ident) (bexp: bexp_Dan): Prop :=
  var_map_wf var_map_list
  /\ (forall x (bexp_var_map: set ident),
        bexp_var_map = free_vars_bexp_src bexp ->
        In x bexp_var_map ->
        In x var_map_list)
  /\ (forall x (bexp_var_map: set ident),
        bexp_var_map = free_vars_bexp_src bexp ->
        In x bexp_var_map ->
        bexp_has_variable x bexp)
  /\ (forall x (bexp_var_map: set ident),
        bexp_var_map = free_vars_bexp_src bexp ->
        In x bexp_var_map ->
        exists index,
          find_index_rel var_map_list x (Some index)).
        
Definition var_map_wf_wrt_imp (var_map_list: list ident) (imp: imp_Dan): Prop :=
  var_map_wf var_map_list
  /\ imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp var_map_list)
                                       (var_map_wf_wrt_bexp var_map_list)
                                       imp
  /\ (forall (x: ident),
        imp_has_variable x imp ->
        In x var_map_list).
                                          

Local Example test_one_index_opt :
  one_index_opt "z" ("z" :: "a" :: nil) = 1.
Proof.
  simpl. reflexivity.
Qed.

Local Example test_one_index_opt1 :
  one_index_opt "z" ("a" :: "b" :: "c" :: "z" :: nil) = 4.
Proof.
  simpl. reflexivity.
Qed.

Local Example test_one_index_opt2 :
  one_index_opt "z" ("a" :: "b" :: "c" :: nil) = 4.
Proof.
  simpl. reflexivity.
Qed.

Local Definition my_list := "a" :: "b" :: "c" :: nil.
Local Example test_one_index_opt3 :
  forall (x: ident),
    one_index_opt x my_list = Datatypes.length my_list + 1 ->
    find_index_rel my_list x None.
Proof.
  intros.
  econstructor.
  unfold not.
  intros.
  rewrite H0 in H. simpl in H. discriminate.
  econstructor.
  unfold not. intros.
  rewrite H0 in H. simpl in H. discriminate.
  econstructor.
  unfold not. intros.
  rewrite H0 in H. simpl in H. discriminate.
  econstructor.
Qed.

Lemma one_index_opt_vs_nth_error :
  forall (n: nat) (vars: list ident) (x: ident),
    one_index_opt x vars = S n ->
    S n <= Datatypes.length vars ->
    n < Datatypes.length vars ->
    nth_error vars n = Some x.
Proof.
  induction n; intros.
  - destruct vars; [ inversion H0 | ].
    simpl in H. destruct (string_dec i x) eqn:?; subst; inversion H.
    + reflexivity.
    + destruct vars; inversion H3.
      destruct (string_dec i0 x) eqn:?; inversion H4.
  - destruct vars.
    + simpl in H1. inversion H1.
    + simpl. apply IHn.
      * simpl in H.
        destruct (string_dec i x) eqn:?; inversion H.
        reflexivity.
      * simpl in H0. lia.
      * simpl in H1. lia.
Qed.

Lemma nth_error_vs_find_index_rel :
  forall (n: nat) (vars: list ident) (x: ident),
    (nth_error vars n = Some x /\
       forall k,
         k < n ->
         nth_error vars k <> Some x) <->
      find_index_rel vars x (Some n).
Proof.
  intros n vars x; split; revert x n; induction vars; intros; [ destruct H | destruct H | ..].
  - revert H0 H. revert x. induction n; intros.
    + simpl in H. discriminate.
    + simpl in H. discriminate.
  - induction n.
    + simpl in H. inversion H. econstructor. reflexivity.
    + simpl in H.
      assert (forall k: nat, k < n -> nth_error vars k <> Some x).
      intros.
      assert (S k < S n) by (intuition).
      eapply H0 in H2. unfold not in *. intros.
      simpl in H2. apply H2 in H3. assumption.
      assert (nth_error vars n = Some x /\ forall k, k < n -> nth_error vars k <> Some x) by (split; assumption).
      eapply IHvars in H2.
      econstructor.
      specialize (H0 0).
      assert (0 < S n) by intuition.
      apply H0 in H3. simpl in H3. unfold not in *.
      intros. assert (Some x = Some a) by (f_equal; assumption).
      symmetry in H5; apply H3 in H5. assumption.
      assumption.
  - inversion H.
  - destruct n.
    + invs H.  split.
      * reflexivity.
      * intros. inversion H0.
    + invs H. eapply IHvars in H5. destruct H5. split.
      * simpl. eassumption.
      * intros.
        unfold not. intros.
        destruct k.
        -- simpl in H3. unfold not in *. inversion H3. symmetry in H6. apply H4 in H6. assumption.
        -- inversion H2. assert (k < n) by intuition.
           eapply H1 in H5.
           simpl in H3. apply H5 in H3. assumption.
           assert (k < n) by intuition.
           apply H1 in H7.
           unfold not in *. simpl in H3. apply H7 in H3. assumption.
Qed.


Lemma one_index_opt_vs_find_index_rel :
  forall (n: nat) (vars: list ident) (x: ident),
    (nth_error vars n = Some x ->
     forall k,
       k < n ->
       nth_error vars k <> Some x) ->
    (one_index_opt x vars = S n ->
     S n <= Datatypes.length vars ->
     find_index_rel vars x (Some n)) \/
      (one_index_opt x vars = n ->
       n = Datatypes.length vars + 1 ->
       find_index_rel vars x None).
Proof.
  induction n, vars; intros.
  - left; intros.
    simpl in H. simpl in H0. inversion H1.
  - left. intros.
    simpl in H0. destruct (string_dec i x) eqn:eq.
    rewrite e. econstructor. reflexivity.
    inversion H0.
    unfold one_index_opt in H3.
    destruct vars.
    discriminate.
    destruct (string_dec i0 x) eqn:eq1.
    inversion H3.
    inversion H3.
  - right. intros. simpl in H0. inversion H1.
    econstructor.
  - left. intros. simpl in H0.
    destruct (string_dec i x) eqn:eq; try discriminate.
    econstructor.
    unfold not; intros.
    symmetry in H2. apply n0 in H2. assumption.
    specialize (IHn vars x). destruct IHn. simpl in H. intros.
    eapply H with (k := S k) in H2.
    simpl in H2. assumption.
    intuition.
    + eapply H2.
      intuition.
      simpl in H1. intuition.
    + remember (i :: vars) as vars'.
      rewrite Heqvars' in H1. simpl in H1.
      inversion H0.
      
      eapply one_index_opt_vs_nth_error in H4; [ | intuition .. ].
      eapply nth_error_vs_find_index_rel. split.
      * eassumption.
      * intros.
        unfold not. intros.
        rewrite Heqvars' in H.
        simpl in H. apply H with (k := S k) in H4.
        simpl in H4. apply H4 in H5. assumption.
        intuition.
Qed.

Require Import DanTrick.DanLogProp.

Section TryingOutThings.
  Local Open Scope dantrick_scope.

  Definition my_program :=
    "x" <- ((CONST_Dan 3) +d (CONST_Dan 2)) ;;
    "y" <- ((VAR_Dan "x") +d (CONST_Dan 3)) ;;
    "z" <- ((VAR_Dan "x") +d (CONST_Dan 3)).

  
  Fixpoint remove_var (var: ident) (i: imp_Dan): imp_Dan :=
    match i with
    | ASSIGN_Dan x a => if String.eqb x var then SKIP_Dan else ASSIGN_Dan x (dan_aexp_update var (CONST_Dan 1) a)
    | IF_Dan b i1 i2 =>
        IF_Dan (dan_bexp_update var (CONST_Dan 1) b) (remove_var var i1) (remove_var var i2)     
    | WHILE_Dan b i =>
        WHILE_Dan (dan_bexp_update var (CONST_Dan 1) b) (remove_var var i)
    | SEQ_Dan i1 i2 =>
        SEQ_Dan (remove_var var i1) (remove_var var i2)
    | SKIP_Dan => SKIP_Dan
    end.


  Definition another_program :=
    "x" <- ((VAR_Dan "y") +d (VAR_Dan "z")) ;;
    "x" <- ((VAR_Dan "z") -d (VAR_Dan "y")) ;;
    "y" <- (PARAM_Dan 0).

  Definition another_program' :=
    "x" <- ((VAR_Dan "y") +d (VAR_Dan "z")) ;;
    "z" <- ((VAR_Dan "z") -d (VAR_Dan "y")).

  Definition another_program'' :=
    "x" <- ((VAR_Dan "y") +d (VAR_Dan "z")) ;;
    "z" <- ((VAR_Dan "y") -d (VAR_Dan "z")).


  Definition list_to_set (idents: list ident): set ident :=
    List.fold_left (fun acc x => set_add string_dec x acc) idents (empty_set ident).

  Definition union_idents := set_union string_dec.

  Local Open Scope list_scope.


  Definition set1 := (list_to_set ("z" :: "x" :: "y" :: "a" :: nil)).
  Definition set2 := (list_to_set ("a" :: "b" :: "c" :: "d" :: nil)).

  Definition diff_idents := set_diff string_dec.

  Definition add_idents := set_add string_dec.

End TryingOutThings.




