From Coq Require Import String List Psatz Peano Program.Equality.
From DanTrick Require Import DanTrickLanguage StackLanguage EnvToStack StackLangTheorems.
From DanTrick Require Import DanTrickSemanticsMutInd ImpVarMap ImpVarMapTheorems.
From DanTrick Require Import LogicTranslationBase DanImpHigherOrderRel DanImpHigherOrderRelTheorems.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

From DanTrick Require Import StackFrame.

Locate successor_minus_one_same.


Lemma stack_mutated_at_index_of_update :
  forall x n idents nenv,
    In x idents ->
    NoDup idents ->
    stack_mutated_at_index
      (map (update x n nenv) idents)
      (one_index_opt x idents)
      n
      (map nenv idents).
Proof.
  induction idents; intros.
  - invs H.
  - invs H.
    + simpl. unfold update. destruct (string_dec x x) eqn:?.
      * constructor. apply nodup_idents_means_maps_are_same. assumption.
      * assert (x = x) by reflexivity. congruence.
    + eapply cannot_be_in_both in H1; [ | eassumption .. ].
      invs H; [ congruence | ].
      simpl.
      simpl. rewrite if_string_dec_diff; [ | unfold not; intros EQ; symmetry in EQ; congruence ].
      eapply stk_mut_rest.
      * pose proof (one_index_opt_always_geq_1).
        specialize (H3 x idents). lia.
      * rewrite map_length. eapply inside_implies_within_range' in H2; [ | ereflexivity ]. eapply le_n_S. assumption.
      * repeat rewrite map_length. reflexivity.
      * rewrite successor_minus_one_same. eapply IHidents. assumption. invs H0. assumption.
      * unfold update. rewrite if_string_dec_diff. reflexivity. assumption.
Qed.


Lemma args_Dan_preserves_length :
  forall (args: list aexp_Dan) dbenv fenv nenv vals,
    args_Dan args dbenv fenv nenv vals ->
    Datatypes.length args = Datatypes.length vals.
Proof.
  induction args; intros; invs H.
  - reflexivity.
  - simpl. f_equal.
    eapply IHargs. eassumption.
Qed.

Lemma prepend_push_commutes :
  forall (n: nat) (i: imp_stack),
    prepend_push (Seq_Stk Push_Stk i) n = Seq_Stk Push_Stk (prepend_push i n).
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - simpl. erewrite <- IHn. reflexivity.
Qed.

Lemma remove_prepend_push :
  forall (n: nat) (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack),
    imp_stack_sem i fenv ((repeat 0 n) ++ stk) stk' ->
    imp_stack_sem (prepend_push i n) fenv
                  stk stk'.
Proof.
  induction n; intros.
  + simpl. simpl in H. assumption.
  + simpl in *. assert (imp_stack_sem Push_Stk fenv (repeat 0 n ++ stk) (0 :: repeat 0 n ++ stk)).
    constructor. reflexivity.
    assert (imp_stack_sem (Seq_Stk Push_Stk i) fenv (repeat 0 n ++ stk) stk').
    econstructor. eassumption. assumption.
    eapply IHn. assumption.
Qed.

Lemma repeat_add_last :
  forall (A: Type) (a: A) (n: nat),
    repeat a n ++ a :: nil = repeat a (S n).
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHn. simpl. reflexivity.
Qed.

Lemma init_fenv_map_is_repeat_0 :
  forall (idents: list ident),
    map init_nenv idents = repeat 0 (Datatypes.length idents).
Proof.
  induction idents; intros.
  - reflexivity.
  - simpl. unfold init_nenv. f_equal. fold init_nenv. assumption.
Qed.

Lemma nodup_free_vars_bexp :
  forall (b: bexp_Dan),
    NoDup(free_vars_bexp_src b).
Proof.
  induction b; intros.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. assumption.
  - simpl. apply set_union_no_dups.
    assumption.
  - simpl. apply set_union_no_dups. assumption.
  - simpl. apply set_union_no_dups. apply nodup_free_vars_aexp.
Qed.

Lemma nodup_free_vars_imp :
  forall (i: imp_Dan),
    NoDup (free_vars_imp_src i).
Proof.
  induction i; intros; simpl; try constructor.
  - apply set_union_no_dups. apply nodup_free_vars_bexp.
  - apply set_union_no_dups. assumption.
  - apply ListSet.set_add_nodup.
    apply nodup_free_vars_aexp.
  - apply set_union_no_dups. assumption.
Qed.

Lemma set_add_nil :
  forall (s0: string) (s: ListSet.set string),
    ListSet.set_add string_dec s0
                    s = nil ->
    s = nil.
Proof.
  destruct s; intros.
  - reflexivity.
  - simpl in H. destruct (string_dec s0 s) eqn:?.
    + invs H.
    + invs H.
Qed.

Lemma set_add_nil' :
  forall (P: Prop) (s0: string) (s: ListSet.set string),
    ListSet.set_add string_dec s0
                    s = nil ->
    P.
Proof.
  intros.
  rewrite set_add_nil with (s := s) (s0 := s0) in H. simpl in H. invs H. assumption.
Qed.

Lemma set_union_nil :
  forall (s1 s2: ListSet.set string),
    NoDup s2 ->
    ListSet.set_union string_dec s1 s2 = nil ->
    s1 = nil /\ s2 = nil.
Proof.
  destruct s1, s2; intros; split; try reflexivity.
  - simpl in H0. rewrite set_union_is_append in H0. simpl in H0. rewrite set_add_nil with (s := rev s2) (s0 := s) in H0. simpl in H0. invs H0.
    assumption.
    invs H. simpl. assumption.
  - simpl in H0. assumption.
  - simpl in H0. eapply set_add_nil'. eassumption.
  - simpl in H0. eapply set_add_nil'. eassumption.
Qed.

Lemma list_set_fold_left_other_set_nil' :
  forall (l other_set: ListSet.set string) (s: string),
    ListSet.set_fold_left
            (fun (acc : list string) (x: string) => x :: acc)
            l
            (s :: other_set) = nil ->
    (s :: other_set) = nil.
Proof.
  induction l; intros.
  - simpl in H. invs H.
  - remember (fun (acc : list string) (x: string) => x :: acc) as func. unfold ListSet.set_fold_left in H.
    cbv delta in H. cbv beta in H. cbv fix in H.
    cbv beta in H.
    (* put progress there just so that the indentation wouldn't get messed up lol *)
    progress (cbv match in H).
    change ((fix fold_left (l a0 : list string) {struct l} : list string :=
         match l with
         | nil => a0
         | b :: t => fold_left t (func a0 b)
         end) (a :: l) (func other_set s)) with (fold_left func (a :: l) (func other_set s)) in H.
    change (fold_left func (a :: l) (func other_set s)) with (ListSet.set_fold_left func (a :: l) (func other_set s)) in H.
    rewrite Heqfunc in *.
    apply IHl in H. invs H.
Qed.

Lemma list_set_fold_left_other_set_nil :
  forall (P: Prop) (l other_set: ListSet.set string) (s: string),
      ListSet.set_fold_left
        (fun (acc : list string) (x : string) => x :: acc) l 
        (s :: other_set) = nil ->
    P.
Proof.
  induction other_set; intros.
  - simpl in H. apply list_set_fold_left_other_set_nil' in H. invs H.
  - apply list_set_fold_left_other_set_nil' in H. invs H.
Qed.

Lemma list_set_fold_left_other_is_nil :
  forall (l: ListSet.set string),
    ListSet.set_fold_left (fun (acc : list string) (x: string) => x :: acc)
                                l nil = nil ->
    l = nil.
Proof.
  destruct l; intros.
  - reflexivity.
  - simpl in H. eapply list_set_fold_left_other_set_nil. eassumption.
Qed.

Lemma construct_trans_nil :
  forall i,
    free_vars_imp_src i = nil ->
    construct_trans i = nil.
Proof.
  destruct i; intros.
  - simpl in H. unfold construct_trans. simpl.
    apply set_union_nil in H. destruct H. apply set_union_nil in H0. destruct H0. rewrite H, H0, H1. reflexivity.
    apply nodup_free_vars_imp.
    apply set_union_no_dups. apply nodup_free_vars_imp.
  - reflexivity.
  - unfold construct_trans. simpl in *.
    apply set_union_nil in H. destruct H.
    rewrite H, H0. reflexivity.
    apply nodup_free_vars_bexp.
  - simpl in H. eapply set_add_nil'. eassumption.
  - simpl in H.  eapply set_union_nil in H. destruct H. unfold construct_trans. simpl. rewrite H, H0. reflexivity.
    apply nodup_free_vars_imp.
Qed.

Ltac destruct_set_unions H :=
  let tipe := type of H in
  match tipe with
  | ?a = nil =>
      match a with
      | ListSet.set_union string_dec _ _ =>
          apply set_union_nil in H;
          let H' := fresh "Ho" in
          destruct H as [H H'];
          try destruct_set_unions H'
      end
  end.

Lemma nodup_fold_left :
  forall (s other: ListSet.set string),
    NoDup (s ++ other) ->
    NoDup (ListSet.set_fold_left (fun (acc: list string) (x: string) => x :: acc) s other).
Proof.
  induction s; intros.
  - simpl. simpl in H. assumption.
  - simpl in *. invs H. apply nodup_switch in H. eapply IHs in H. assumption.
Qed.

Lemma nodup_construct_trans :
  forall (i: imp_Dan),
    NoDup (construct_trans i).
Proof.
  intros.
  unfold construct_trans.
  apply nodup_fold_left. rewrite <- app_nil_end. apply nodup_free_vars_imp.
Qed.

Lemma in_idents_one_index_opt :
  forall (x: ident) (idents: list ident),
    NoDup idents ->
    In x idents ->
    (exists k, one_index_opt x idents = k).
Proof.
  induction idents; intros.
  - exists 1. simpl. reflexivity.
  - invs H0.
    + exists 1. simpl. eapply if_string_dec_same.
    + pose proof (H2 := H1). eapply cannot_be_in_both with (a := a) in H2; [ | assumption .. ].
      apply IHidents in H1. destruct H1. eexists (S x0).
      simpl. rewrite if_string_dec_diff. rewrite H1. reflexivity.
      unfold not. intros. symmetry in H3. congruence.
      invs H. assumption.
Qed.
      
Lemma one_index_opt_not_0 :
  forall (idents: list ident) (x: ident),
    one_index_opt x idents = 0 ->
    False.
Proof.
  induction idents; intros; unfold one_index_opt in *.
  - invs H.
  - destruct (string_dec a x) eqn:?.
    + invs H.
    + invs H.
Qed.

Lemma find_index_rel_and_one_index_opt :
  forall (idents: list ident) (x: ident) (index: nat),
    NoDup idents ->
    0 <= index < Datatypes.length idents ->
    find_index_rel idents x (Some index) <-> one_index_opt x idents = S index.
Proof.
  split; intros.
  - eapply find_index_rel_implication. assumption.
  - eapply find_index_rel_help in H1; assumption.
Qed.

Lemma in_idents_exists_one_index_opt (idents : list ident)
      (H : NoDup idents)
      (x : ident)
      (H0 : In x idents):
  exists index : nat, one_index_opt x idents = S index.
Proof.
  apply in_idents_one_index_opt in H0; [ | assumption ].
  destruct H0. destruct x0.
  - apply one_index_opt_not_0 in H0. invs H0.
  - exists x0. assumption.
Qed.

Lemma prove_var_map_wf :
  forall (idents: list ident),
    NoDup idents ->
    NoDup idents /\
      (forall (x : ident) (index : nat),
          0 <= index < Datatypes.length idents -> find_index_rel idents x (Some index) <-> one_index_opt x idents = S index) /\
      (forall x : ident, In x idents -> exists index : nat, one_index_opt x idents = S index) /\
      (forall (x : ident) (imp : imp_Dan), In x idents -> idents = construct_trans imp -> imp_has_variable x imp).
Proof.
  intros. split; [ | split; [ | split ]]; intros.
  - assumption.
  - apply find_index_rel_and_one_index_opt; assumption.
  - apply in_idents_exists_one_index_opt; assumption.
  - rewrite H1 in H0. unfold construct_trans in H0.
    pose proof (fold_left_containment_helper). specialize (H2 (free_vars_imp_src imp) x).
    destruct H2. apply H2 in H0. eapply free_vars_in_imp_has_variable. ereflexivity. assumption.
Qed.

Lemma const_dan_always_well_formed :
  forall (idents: list ident) (n: nat),
    NoDup idents ->
    var_map_wf_wrt_aexp idents (CONST_Dan n).
Proof.
  intros.
  unfold_wf_aexp; intros.
  - apply prove_var_map_wf. assumption.
  - simpl in H0. subst. invs H1.
  - subst. simpl in *. invs H1.
  - subst. invs H1.
  - subst. invs H2.
Qed.

Lemma param_dan_always_well_formed :
  forall (idents: list ident) (n: nat),
    NoDup idents ->
    var_map_wf_wrt_aexp idents (PARAM_Dan n).
Proof.
  intros.
  unfold_wf_aexp; intros.
  - apply prove_var_map_wf. assumption.
  - simpl in H0. subst. invs H1.
  - subst. simpl in *. invs H1.
  - subst. invs H1.
  - subst. invs H2.
Qed.

Lemma true_dan_always_well_formed :
  forall (idents: list ident),
    NoDup idents ->
    var_map_wf_wrt_bexp idents TRUE_Dan.
Proof.
  intros. unfold_wf_bexp; intros; subst.
  - apply prove_var_map_wf; assumption.
  - invs H1.
  - invs H1.
  - invs H1.
Qed.

Lemma false_dan_always_well_formed :
  forall (idents: list ident),
    NoDup idents ->
    var_map_wf_wrt_bexp idents FALSE_Dan.
Proof.
  intros. unfold_wf_bexp; intros; subst.
  - apply prove_var_map_wf; assumption.
  - invs H1.
  - invs H1.
  - invs H1.
Qed.
                           

Lemma var_map_wf_wrt_aexp_self :
  forall (idents: list ident) (a: aexp_Dan),
    idents = free_vars_aexp_src a ->
    var_map_wf_wrt_aexp idents a.
Proof.
  intros.
  unfold_wf_aexp; intros.
  - apply prove_var_map_wf. rewrite H. apply nodup_free_vars_aexp.
  - rewrite H0 in H1. rewrite H. assumption.
  - rewrite H0 in H1. apply free_vars_in_aexp_has_variable with (idents := idents). assumption. rewrite <- H in H1. assumption.
  - eapply find_index_rel_in_stronger. rewrite H. rewrite H0 in H1. assumption.
    rewrite H. apply nodup_free_vars_aexp.
  - invs H0.
    eapply free_vars_in_args_has_variable. reflexivity. eassumption.
Qed.





Lemma var_map_wf_wrt_aexp_subset_stronger :
  forall (a: aexp_Dan) (idents idents': list ident),
    (forall x,
        In x idents ->
        In x idents') ->
    NoDup idents' -> NoDup idents ->
    var_map_wf_wrt_aexp idents a ->
    var_map_wf_wrt_aexp idents' a.
Proof.
  induction a using aexp_Dan_ind2; intros.
  - eapply const_dan_always_well_formed. assumption.
  - eapply var_map_wf_var_dan. eapply H. simpl. unfold_wf_aexp_in H2. eapply A. reflexivity. simpl. left. reflexivity.
    assumption.
  - eapply param_dan_always_well_formed. assumption.
  - eapply var_map_wf_plus_dan_forwards in H2. destruct H2. eapply var_map_wf_plus_dan_backwards.
    + eapply IHa1; eassumption.
    + eapply IHa2; eassumption.
  - eapply var_map_wf_minus_dan_forwards in H2. destruct H2. eapply var_map_wf_minus_dan_backwards.
    + eapply IHa1; eassumption.
    + eapply IHa2; eassumption.
  - induction H; intros.
    + unfold_wf_aexp_in H3. unfold_wf_aexp; intros; subst.
      * apply prove_var_map_wf. assumption.
      * eapply H0. eapply A. reflexivity. assumption.
      * eapply free_vars_in_aexp_has_variable. reflexivity. assumption.
      * eapply find_index_rel_in_stronger. eapply H0. eapply A. reflexivity. assumption. assumption.
      * invs H. simpl in H4. invs H4.
    + eapply var_map_wf_app_dan_backwards.
      * eapply H. intros. eapply H0. eassumption. eassumption. eassumption. eapply var_map_wf_app_dan_first in H3. eassumption. reflexivity.
      * eapply IHForall. eapply var_map_wf_app_dan_forwards in H3. assumption.
Qed.

Lemma var_map_wf_wrt_aexp_subset :
  forall (a: aexp_Dan) (idents: list ident),
    (forall x,
        In x (free_vars_aexp_src a) ->
        In x idents) ->
    NoDup idents ->
    var_map_wf_wrt_aexp idents a.
Proof.
  intros. eapply var_map_wf_wrt_aexp_subset_stronger; try eassumption.
  eapply nodup_free_vars_aexp. eapply var_map_wf_wrt_aexp_self. reflexivity.
Qed.


Lemma var_map_wf_wrt_bexp_self :
  forall (idents: list ident) (b: bexp_Dan),
    idents = free_vars_bexp_src b ->
    var_map_wf_wrt_bexp idents b.
Proof.
  intros.
  unfold_wf_bexp; intros.
  - apply prove_var_map_wf. rewrite H. apply nodup_free_vars_bexp.
  - rewrite H0 in H1. rewrite H. assumption.
  - rewrite H0 in H1. apply free_vars_in_bexp_has_variable with (idents := idents). assumption. rewrite <- H in H1. assumption.
  - eapply find_index_rel_in_stronger. rewrite H. rewrite H0 in H1. assumption.
    rewrite H. apply nodup_free_vars_bexp.
Qed.



