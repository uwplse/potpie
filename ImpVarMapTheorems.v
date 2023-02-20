From Coq Require Import Peano List String Arith.
From DanTrick Require Import ImpVarMap StackLangTheorems DanTrickLanguage StackLanguage EnvToStack.
Require Import Coq.Program.Equality Coq.micromega.Lia.


(** Tactics and theorems for dealing with reasoning about the var map and its
  * well-formed-ness *)


Definition comp_code (i: imp_Dan) (idents: list ident) (num_args: nat): imp_stack :=
  compile_imp i (ident_list_to_map idents) (List.length idents).

Tactic Notation "refold" constr(sth) := unfold sth; fold sth.
Tactic Notation (at level 1) "refold_in" constr(sth) hyp(H) := unfold sth in H; fold sth in H.

Ltac unfold_wf_aexp :=
  unfold var_map_wf_wrt_aexp, var_map_wf;
  split; [ | split; [ | split; [ | split ]]].

Ltac unfold_wf_aexp_in H :=
  unfold var_map_wf_wrt_aexp in H; unfold var_map_wf in H;
  let WF := fresh "WF" in
  let WF' := fresh "WF'" in
  destruct H as (WF & WF');
  let A := fresh "A" in
  let B := fresh "B" in
  let C := fresh "C" in
  let D := fresh "D" in
  destruct WF' as (A & B & C & D).

Ltac unfold_wf_bexp :=
  unfold var_map_wf_wrt_bexp, var_map_wf;
  split; [ | split; [ | split ]].

Ltac unfold_wf_bexp_in H :=
  unfold var_map_wf_wrt_bexp in H; unfold var_map_wf in H;
  let WF := fresh "WF" in
  let WF' := fresh "WF'" in
  destruct H as (WF & WF');
  let A := fresh "A" in
  let B := fresh "B" in
  let C := fresh "C" in
  destruct WF' as (A & B & C).

Ltac unfold_wf_imp :=
  unfold var_map_wf_wrt_imp, var_map_wf;
  split; [ | split].

Ltac unfold_wf_imp_in H :=
  unfold var_map_wf_wrt_imp in H; unfold var_map_wf in H;
  let WF := fresh "WF" in
  let WF' := fresh "WF'" in
  let WF'' := fresh "WF''" in
  destruct H as (WF & WF' & WF'').

Ltac crewrite H :=
  rewrite H in *; clear H.

Ltac ereflexivity :=
  eapply eq_refl.

Ltac remember_all_helper rest_hyp rest_arg :=
  let handle_rest rest rh ra :=
    (let rh_name := fresh "REST_HYP" in
     let ra_name := fresh "REST_ARG" in
     rewrite rh in *;
     clear rh;
     match goal with
     | [ H : context [ra] |- _ ] =>
         idtac
     | [ H := context [ra] |- _ ] =>
         idtac
     | [ |- context [ra] ] =>
         idtac
     | _ => idtac
     end;
     let ra_type := type of ra in
     match goal with
     | [ arg: ra_type |- _ ] =>
         match arg with
         | ra => clear ra
         | _ => idtac
         end
     | _ =>
         idtac
     end;
     try (remember rest as ra_name eqn:rh_name;
          remember_all_helper rh_name ra_name)) in
  match goal with
  | [ H : rest_arg = ?rest ?current_arg |- _ ] =>
      let current_arg_type := type of current_arg in
      idtac;
      match goal with
      | [ arg: current_arg_type |- _ ] =>
          match arg with
          | current_arg =>
              let other_current_arg_type := type of arg in
              handle_rest rest rest_hyp rest_arg
          end
      | [ arg := current_arg : current_arg_type |- _ ] =>
          idtac
      | [ |- _ ] =>
          let arg_name := fresh "ARG" in
          remember current_arg as arg_name
          ;
          handle_rest rest rest_hyp rest_arg
      end
  end.

Ltac remember_all :=
  match goal with
  | [ |- ?rest ?current_arg ] =>
      let current_arg_type := type of current_arg in
      idtac;
      match goal with
      | [ arg: current_arg_type |- _ ] =>
          match arg with
          | current_arg =>
              idtac
          end
      | [ arg := current_arg : current_arg_type |- _ ] =>
          idtac
      | [ |- _ ] =>
          let arg_name := fresh "ARG" in
          remember current_arg as arg_name;
          let rest_hyp := fresh "REST_HYP" in
          let rest_arg := fresh "REST_ARG" in
          remember rest as rest_arg eqn:rest_hyp;
          remember_all_helper rest_hyp rest_arg
      end
  end.

Ltac remember_all_in H :=
  match goal with
  | [ H' : ?rest ?current_arg |- _ ] =>
      match H' with
      | H =>
          let current_arg_type := type of current_arg in
          idtac;
          match goal with
          | [ arg: current_arg_type |- _ ] =>
              match arg with
              | current_arg =>
                  let other_current_arg_type := type of arg in
                  let rest_hyp := fresh "REST_HYP" in
                  let rest_arg := fresh "REST_ARG" in
                  remember rest as rest_arg eqn:rest_hyp;
                  remember_all_helper rest_hyp rest_arg
              end
          | [ arg := current_arg : current_arg_type |- _ ] =>
              idtac
          | [ |- _ ] =>
              let arg_name := fresh "ARG" in
              remember current_arg as arg_name;
              let rest_hyp := fresh "REST_HYP" in
              let rest_arg := fresh "REST_ARG" in
              remember rest as rest_arg eqn:rest_hyp;
              remember_all_helper rest_hyp rest_arg
          end
      end
  end.

Lemma find_index_rel_deterministic :
  forall (idents: list ident) (x x': ident) (n: nat),
    find_index_rel idents x (Some n) ->
    find_index_rel idents x' (Some n) ->
    x = x'.
Proof.
  induction idents; intros.
  - inversion H.
  - invs H; invs H0.
    + reflexivity.
    + eapply IHidents; eassumption.
Qed.

Lemma find_index_rel_within_range :
  forall (idents: list ident) (x: ident) (n: nat),
    find_index_rel idents x (Some n) ->
    0 <= n < Datatypes.length idents.
Proof.
  intros. dependent induction H.
  - simpl. constructor; auto with arith.
  - simpl. constructor; auto with arith.
    specialize (IHfind_index_rel n0 eq_refl). inversion H0; subst.
    + simpl in *. auto with arith.
    + simpl in *. destruct IHfind_index_rel. auto with arith.
Qed.

Lemma find_index_rel_implication :
  forall (map: list ident) (x: ident) (index: nat),
    find_index_rel (map) x (Some index) -> one_index_opt x (map) = S index.
Proof.
  intros. 
  dependent induction H; simpl; 
  destruct (string_dec var x) eqn:?; auto; subst;
  unfold not in *; apply False_ind; auto.
Qed.

Lemma find_index_rel_in_stronger :
  forall (idents: list ident) (x: ident),
    In x idents ->
    NoDup idents ->
    exists (index: nat),
      find_index_rel idents x (Some index).
Proof.
  induction idents; intros.
  - invs H.
  - invs H0. invs H.
    + exists 0. econstructor. reflexivity.
    + pose proof (IN := H1). eapply IHidents in H1; [ | eassumption ].
      destruct H1.
      exists (S x0).
      econstructor.
      * unfold not; intros.
        rewrite H2 in IN. apply H3 in IN. assumption.
      * assumption.
Qed.


Lemma set_union_no_dups :
  forall (s1 s2 : ListSet.set string),
    NoDup s1 ->
    NoDup (ListSet.set_union string_dec s1 s2).
Proof.
  induction s1; intros.
  - induction s2.
    + simpl. econstructor.
    + simpl. eapply ListSet.set_add_nodup. assumption.
  - revert H. revert IHs1. revert s1. induction s2; intros.
    + simpl. assumption.
    + simpl. pose proof (H' := H). eapply NoDup_cons_iff in H'. destruct H'.
      pose proof (H2 := H1). eapply ListSet.set_add_nodup.
      eapply IHs2.
      assumption.
      assumption.
Qed.

Lemma nodup_fold_left :
  forall (aexps: list aexp_Dan)
    (other_set: ListSet.set string),
    NoDup other_set ->
    NoDup
    (fold_left
       (fun (x0 : ListSet.set string) (y : aexp_Dan) =>
        ListSet.set_union string_dec x0 (free_vars_aexp_src y)) aexps
       other_set).
Proof.
  induction aexps; intros.
  - simpl. assumption.
  - simpl. eapply IHaexps. apply set_union_no_dups with (s2 := free_vars_aexp_src a) in H.
    assumption.
Qed.

Lemma no_dups_in_free_vars_aexp_src :
  forall (a: aexp_Dan),
    NoDup (free_vars_aexp_src a).
Proof.
  induction a using aexp_Dan_ind2.
  - simpl. constructor.
  - constructor. unfold not; intros. inversion H.
    constructor.
  - constructor.
  - simpl. apply ListSet.set_union_nodup; assumption.
  - simpl. apply ListSet.set_union_nodup; assumption.
  - induction H.
    + simpl. constructor.
    + simpl. simpl in IHForall.
      apply nodup_fold_left.
      apply set_union_no_dups.
      constructor.
Qed.

Lemma find_index_rel_in :
  forall (a1: aexp_Dan) (aexp_var_map: ListSet.set string) (x: DanTrickLanguage.ident) (idents: list DanTrickLanguage.ident),
    aexp_var_map = free_vars_aexp_src a1 ->
    In x aexp_var_map ->
    (forall y,
        In y aexp_var_map ->
        In y idents) ->
    NoDup idents ->
    exists index : nat, find_index_rel idents x (Some index).
Proof.
  intros.
  apply find_index_rel_in_stronger.
  + apply H1. assumption.
  + assumption.
Qed.

Lemma one_index_opt_always_geq_1 :
  forall x idents,
    1 <= one_index_opt x idents.
Proof.
  intros. destruct idents.
  + simpl. auto.
  + simpl. destruct (string_dec s x).
    * auto.
    * lia.
Qed.

Require Import Coq.Logic.Eqdep_dec.

Lemma UIP_string :
  forall (a: string)
    (p1 p2: a = a),
    p1 = p2.
Proof.
  intros. eapply UIP_dec. eapply string_dec.
Qed.

Lemma UIP_string_refl :
  forall (a: string)
    (p1: a = a),
    p1 = eq_refl.
Proof.
  intros. eapply UIP_string.
Qed.

Lemma string_dec_self :
  forall a,
  forall (e: a = a),
    string_dec a a = left e.
Proof.
  intros.
  destruct (string_dec a a).
  pose proof (UIP_string a e e0).
  rewrite H. reflexivity.
  congruence.
Qed.

Lemma if_string_dec_same :
  forall (A: Type)
    (a_then a_else: A)
    (x: string),
    (if string_dec x x
     then a_then
     else a_else) = a_then.
Proof.
  intros.
  destruct (string_dec x x).
  reflexivity.
  assert (x = x) by reflexivity. congruence.
Qed.
  
Lemma if_string_dec_diff :
  forall (A: Type)
    (a_then a_else: A)
    (a x: string),
    a <> x ->
    (if string_dec a x then a_then else a_else) = a_else.
Proof.
  intros.
  destruct (string_dec a x); [ congruence | ].
  reflexivity.
Qed.

Lemma cannot_be_in_both :
  forall (idents: list ident) (x a: ident),
    In x (a :: idents) ->
    NoDup (a :: idents) ->
    In x idents ->
    x <> a.
Proof.
  intros. apply ListSet.set_remove_2 with (Aeq_dec := string_dec) (l := (a :: idents)).
  assumption.
  simpl. rewrite if_string_dec_same. assumption.
Qed.


Lemma inside_implies_within_range' :
  forall (map: list ident) (x: ident) (index: nat),
    In x map ->
    one_index_opt x map = index ->
    index <= Datatypes.length map.
Proof.
  induction map; intros.
  - invs H.
  - invs H.
    + unfold one_index_opt. destruct (string_dec).
      --enough (Datatypes.length (x :: map) > 0).
        ++lia.
        ++pose proof (length_zero_iff_nil (x::map)).
          simpl. lia.  
      --destruct n. reflexivity.
    + pose proof (IHmap x (one_index_opt x map) H1 eq_refl).
      unfold one_index_opt in *. destruct string_dec.
      --enough (Datatypes.length (x :: map) > 0).
        ++pose proof (length_zero_iff_nil (x::map)).
        simpl. lia.  
        ++pose proof (length_zero_iff_nil (x::map)).
          simpl. lia.
      --enough (1 + Datatypes.length map =  Datatypes.length (a :: map)).
        ++rewrite <- H2. lia.
        ++auto.
Qed.

Lemma inside_implies_within_range :
  forall (map: list ident) (x: ident) (index: nat),
    In x map ->
    one_index_opt x map = S index ->
    0 <= index < Datatypes.length map.
Proof.
  intros. pose proof (inside_implies_within_range' map x (S index) H H0).
  lia.  
Qed. 

Lemma bad_comparison :
  forall (n1 n2 n3: nat),
    n1 <= n2 ->
    n1 <> S (n2 + n3).
Proof.
  intros. lia.
Qed.

Lemma find_index_rel_help :
  forall (index: nat) (idents: list ident) (x0: ident),
    0 <= index < Datatypes.length idents ->
    one_index_opt x0 idents = S index ->
    find_index_rel idents x0 (Some index).
Proof.
  intros index idents. revert index. induction idents; intros.
  - inversion H0. subst. destruct H. inversion H1.
  - simpl in *. destruct (string_dec a x0) eqn:?; subst; inversion H0.
    + constructor; auto.
    + destruct index.
      *  unfold one_index_opt in H2. destruct idents. inversion H2.
         simpl. destruct (string_dec i x0) eqn:?; subst; inversion H2.
      * rewrite H2. constructor.
        unfold not; intros. symmetry in H1. apply n in H1. assumption.
        apply IHidents. lia.
        assumption.
Qed.

Lemma args_has_variable_elim :
  forall (x: ident) (a: aexp_Dan) (aexps: list aexp_Dan),
  args_has_variable x (a :: aexps) <->
  (aexp_has_variable x a \/ args_has_variable x aexps).
Proof.
  intros; split; intros.
  - invs H; [left | right]; assumption.
  - destruct H; [eapply ArgsHasVarFirst | eapply ArgsHasVarRest]; eassumption.
Qed.

Lemma in_fold_nil_case :
  forall (aexps: list aexp_Dan) (other_set: ListSet.set string) (x: ident),
    In x other_set ->
    In x
       (fold_left
          (fun (x0 : ListSet.set string) (y : aexp_Dan) =>
             ListSet.set_union string_dec x0 (free_vars_aexp_src y)) aexps
          other_set).
Proof.
  induction aexps; intros.
  - simpl. eassumption.
  - simpl.
    eapply IHaexps.
    eapply ListSet.set_union_iff.
    left. eassumption.
Qed.



Lemma variable_in_elim' :
  forall (x: ident) (a: aexp_Dan) (aexps: list aexp_Dan) (other_set: ListSet.set ident),
    In x
       (fold_left
          (fun (x : ListSet.set string) (y : aexp_Dan) => ListSet.set_union string_dec x (free_vars_aexp_src y)) 
          (a :: aexps)
          other_set) <->
      (In x
          (ListSet.set_union
             string_dec
             (ListSet.set_union
                string_dec
                (free_vars_aexp_src a)
                other_set)
             (fold_left
                (fun (x : ListSet.set string) (y : aexp_Dan) =>
                   ListSet.set_union string_dec x (free_vars_aexp_src y)) 
                aexps (ListSet.empty_set string)))).
Proof.
  intros x a aexps; revert x a; induction aexps; intros; split; intros.
  - simpl in H. simpl. eapply ListSet.set_union_iff in H. eapply ListSet.set_union_iff. destruct H; [ right | left ]; eassumption.
  - simpl in H. simpl. eapply ListSet.set_union_iff in H; eapply ListSet.set_union_iff; destruct H; [ right | left ]; eassumption.
  - remember (a :: aexps) as aexps'.
    simpl in H. subst. eapply IHaexps in H.
    eapply ListSet.set_union_iff in H. eapply ListSet.set_union_iff. destruct H.
    + eapply ListSet.set_union_iff in H. destruct H.
      * right. eapply IHaexps. eapply ListSet.set_union_iff. left. eapply ListSet.set_union_iff. left. assumption.
      * left. eapply ListSet.set_union_iff in H. eapply ListSet.set_union_iff. destruct H; [ right | left ]; eassumption.
    + right. eapply IHaexps. eapply ListSet.set_union_iff. right. assumption.
  - remember (a :: aexps) as aexps'. simpl. subst. eapply IHaexps.
    eapply ListSet.set_union_iff in H. eapply ListSet.set_union_iff. destruct H.
    + left. eapply ListSet.set_union_iff. right. eapply ListSet.set_union_iff in H. eapply ListSet.set_union_iff.
      destruct H; [ right | left ] ; assumption.
    + eapply IHaexps in H. eapply ListSet.set_union_iff in H. destruct H.
      * left. eapply ListSet.set_union_iff. left. apply ListSet.set_union_emptyR in H. assumption.
      * right. assumption.
Qed.

Lemma in_fold_left_rest :
  forall (aexps: list aexp_Dan) (other_set: ListSet.set string) (x: ident),
    In x
       (fold_left
          (fun (x0 : ListSet.set string) (y : aexp_Dan) =>
             ListSet.set_union string_dec x0 (free_vars_aexp_src y)) aexps
          nil) ->
    In x
       (fold_left
          (fun (x0 : ListSet.set string) (y : aexp_Dan) =>
             ListSet.set_union string_dec x0 (free_vars_aexp_src y)) aexps
          other_set).
Proof.
  induction aexps; intros.
  - invs H.
  - eapply variable_in_elim' in H.
    eapply ListSet.set_union_iff in H.
    simpl in H. destruct H.
    + eapply variable_in_elim'. eapply ListSet.set_union_iff.
      left. eapply ListSet.set_union_iff. left. eassumption.
    + eapply variable_in_elim'. eapply ListSet.set_union_iff. right. eassumption.
Qed.

Lemma in_fold_left_iff :
  forall (aexps: list aexp_Dan) (other_set: ListSet.set string) (x: ident),
    In x
       (fold_left
          (fun (x0 : ListSet.set string) (y : aexp_Dan) =>
             ListSet.set_union string_dec x0 (free_vars_aexp_src y)) aexps
          nil) \/ In x other_set <->
    In x
       (fold_left
          (fun (x0 : ListSet.set string) (y : aexp_Dan) =>
             ListSet.set_union string_dec x0 (free_vars_aexp_src y)) aexps
          other_set).
Proof.
  induction aexps; intros; split; intros.
  - invs H.
    + simpl in H0. invs H0.
    + eapply in_fold_nil_case. eassumption.
  - right. simpl in H. eassumption.
  - destruct H.
    + eapply variable_in_elim' in H.
      simpl. eapply IHaexps.
      eapply ListSet.set_union_iff in H.
      destruct H.
      * right. eapply ListSet.set_union_iff. simpl in H. right. eassumption.
      * left. eassumption.
    + eapply in_fold_nil_case. eassumption.
  - eapply variable_in_elim' in H. eapply ListSet.set_union_iff in H.
    destruct H.
    + eapply ListSet.set_union_iff in H. destruct H.
      * left. eapply variable_in_elim'. eapply ListSet.set_union_iff. left. simpl. eassumption.
      * right. eassumption.
    + left. simpl. eapply IHaexps.
      left. eassumption.
Qed.


Ltac set_fold_destruct H :=
  try eapply variable_in_elim' in H;
  try eapply ListSet.set_union_iff in H;
  try destruct H.


Lemma variable_in_elim :
  forall (x: ident) (a: aexp_Dan) (aexps: list aexp_Dan) (other_set: ListSet.set ident),
    In x
         (fold_left (fun (x : ListSet.set string) (y : aexp_Dan) => ListSet.set_union string_dec x (free_vars_aexp_src y)) 
                    (a :: aexps) other_set) <->
    (In x (free_vars_aexp_src a)) \/ (In x (fold_left (fun (x : ListSet.set string) (y : aexp_Dan) => ListSet.set_union string_dec x (free_vars_aexp_src y)) 
                                                     aexps other_set)).
                                     
Proof.
  intros; split; intros.
  - eapply variable_in_elim' in H. eapply ListSet.set_union_iff in H.
    destruct H.
    + eapply ListSet.set_union_iff in H. destruct H.
      * left. eassumption.
      * right. eapply in_fold_nil_case with (aexps := aexps) in H.
        eassumption.
    + right. eapply in_fold_left_rest in H. eassumption.
  - destruct H.
    + eapply variable_in_elim'. eapply ListSet.set_union_iff. left. eapply ListSet.set_union_iff.
      left. eassumption.
    + eapply in_fold_left_iff. eapply in_fold_left_iff in H.
      destruct H.
      * left. simpl. eapply in_fold_left_iff. left. eassumption.
      * right. eassumption.
Qed.

Lemma free_vars_in_aexp_has_variable_forwards :
   forall (a: aexp_Dan) (x : ident) (aexp_var_map : ListSet.set ident),
     aexp_var_map = free_vars_aexp_src a ->
     In x aexp_var_map ->
     aexp_has_variable x a.
Proof.
  apply (aexp_Dan_ind2
           (fun a =>
              forall (x : ident) (aexp_var_map : ListSet.set ident),
              aexp_var_map = free_vars_aexp_src a ->
              In x aexp_var_map ->
              aexp_has_variable x a)); intros.
  - simpl in H. rewrite H in H0. inversion H0.
  - simpl in H. rewrite H in H0. inversion H0.
    + rewrite H1. econstructor. eapply String.eqb_refl.
    + invs H1.
  - simpl in H. rewrite H in H0. invs H0.
  - unfold free_vars_aexp_src in H1. fold free_vars_aexp_src in H1.
    rewrite H1 in H2.
    eapply ListSet.set_union_elim in H2. destruct H2.
    + econstructor. eapply H. ereflexivity. eassumption.
    + eapply AexpHasVarPlus__right. eapply H0. ereflexivity. eassumption.
  - unfold free_vars_aexp_src in H1. fold free_vars_aexp_src in H1.
    rewrite H1 in H2.
    eapply ListSet.set_union_elim in H2. destruct H2.
    + econstructor. eapply H. ereflexivity. eassumption.
    + eapply AexpHasVarMinus__right. eapply H0. ereflexivity. eassumption.
  - simpl in H0. subst.
    econstructor.
    revert H1. revert x.
    induction H; intros.
    
    + simpl in H1. inversion H1.
    + eapply args_has_variable_elim.
      eapply variable_in_elim' in H1.
      eapply ListSet.set_union_iff in H1. destruct H1.
      * apply ListSet.set_union_emptyR in H1. left. eapply H.
        ereflexivity.
        assumption.
      * right. eapply IHForall. assumption.
Qed.

Lemma free_vars_in_aexp_has_variable :
  forall (aexp: aexp_Dan) (idents: ListSet.set ident) (x0: ident),
    idents = free_vars_aexp_src aexp ->
    (In x0 idents <->
       aexp_has_variable x0 aexp).
Proof.
  split; intros; [ eapply free_vars_in_aexp_has_variable_forwards; eassumption | ].
  revert idents x0 H H0.
  eapply (aexp_Dan_ind2
            (fun aexp =>
               forall (idents: ListSet.set ident) (x0: ident),
                 idents = free_vars_aexp_src aexp ->
                 aexp_has_variable x0 aexp ->
                 In x0 idents)). 
  - intros. invs H0.
  - intros. invs H0. constructor. symmetry. apply eqb_eq. apply H3.  
  - intros. invs H0.
  - intros. invs H1. unfold free_vars_aexp_src. pose proof (ListSet.set_union_iff
    string_dec x0
     ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
         match exp with
         | VAR_Dan x =>
             ListSet.set_add string_dec x (ListSet.empty_set string)
         | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
             ListSet.set_union string_dec (free_vars_aexp_src a0)
               (free_vars_aexp_src a3)
         | APP_Dan _ aexps =>
             fold_left
               (fun (x : ListSet.set string) (y : aexp_Dan) =>
                ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
               (ListSet.empty_set string)
         | _ => ListSet.empty_set string
         end) a1)
         ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
         match exp with
         | VAR_Dan x =>
             ListSet.set_add string_dec x (ListSet.empty_set string)
         | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
             ListSet.set_union string_dec (free_vars_aexp_src a0)
               (free_vars_aexp_src a3)
         | APP_Dan _ aexps =>
             fold_left
               (fun (x : ListSet.set string) (y : aexp_Dan) =>
                ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
               (ListSet.empty_set string)
         | _ => ListSet.empty_set string
         end) a2)). 
      destruct H1. apply H4.
      invs H2. 
      + left. eapply H. apply eq_refl. assumption.
      + right. eapply H0. apply eq_refl. assumption.    
    - intros. invs H1. unfold free_vars_aexp_src. pose proof (ListSet.set_union_iff
      string_dec x0
      ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
          match exp with
          | VAR_Dan x =>
              ListSet.set_add string_dec x (ListSet.empty_set string)
          | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
              ListSet.set_union string_dec (free_vars_aexp_src a0)
                (free_vars_aexp_src a3)
          | APP_Dan _ aexps =>
              fold_left
                (fun (x : ListSet.set string) (y : aexp_Dan) =>
                  ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
                (ListSet.empty_set string)
          | _ => ListSet.empty_set string
          end) a1)
          ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
          match exp with
          | VAR_Dan x =>
              ListSet.set_add string_dec x (ListSet.empty_set string)
          | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
              ListSet.set_union string_dec (free_vars_aexp_src a0)
                (free_vars_aexp_src a3)
          | APP_Dan _ aexps =>
              fold_left
                (fun (x : ListSet.set string) (y : aexp_Dan) =>
                  ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
                (ListSet.empty_set string)
          | _ => ListSet.empty_set string
          end) a2)). 
        destruct H1. apply H4.
        invs H2. 
      + left. eapply H. apply eq_refl. assumption.
      + right. eapply H0. apply eq_refl. assumption.
    - intros f aexps H. induction H; intros. 
      + invs H0. invs H3.
      + invs H2. invs H5.
        --pose proof (H (free_vars_aexp_src x) x0 eq_refl H4).
          simpl. 
          apply (in_fold_nil_case l 
          ((ListSet.set_union string_dec (ListSet.empty_set string)
          (free_vars_aexp_src x))) x0). 
          apply ListSet.set_union_intro2. assumption.  
        --pose proof (IHForall (free_vars_aexp_src (APP_Dan f l)) x0 eq_refl)
          (AexpHasVarApp x0 f l H4). 
          simpl.           
          apply (in_fold_left_rest l 
          ((ListSet.set_union string_dec (ListSet.empty_set string)
          (free_vars_aexp_src x))) x0).
          apply H1.   
Qed. 

Lemma bool_wf_help :
  forall (b: bexp_Dan) (x : ident) (bexp_var_map : ListSet.set ident),
    bexp_var_map = free_vars_bexp_src b ->
    In x bexp_var_map ->
    bexp_has_variable x b.
Proof.
  induction b; intros.
  - simpl in H. rewrite H in H0. inversion H0.
  - simpl in H. rewrite H in H0. inversion H0.
  - simpl in H. rewrite H in H0.
    econstructor.
    eapply IHb; try eassumption; try ereflexivity.
    rewrite <- H in H0. eassumption.
  - unfold free_vars_bexp_src in H. fold free_vars_bexp_src in H.
    rewrite H in H0.
    eapply ListSet.set_union_elim in H0. destruct H0.
    + econstructor. eapply IHb1. ereflexivity. eassumption.
    + eapply BexpHasVarAnd__right. eapply IHb2. ereflexivity. eassumption.
  - unfold free_vars_bexp_src in H. fold free_vars_bexp_src in H.
    rewrite H in H0.
    eapply ListSet.set_union_elim in H0. destruct H0.
    + econstructor. eapply IHb1. ereflexivity. eassumption.
    + eapply BexpHasVarOr__right. eapply IHb2. ereflexivity. eassumption.
  - simpl in H. subst.
    eapply ListSet.set_union_elim in H0. destruct H0.
    + econstructor.
      eapply free_vars_in_aexp_has_variable_forwards; try ereflexivity; try eassumption.
    + eapply BexpHasVarLeq__right. eapply free_vars_in_aexp_has_variable_forwards; try ereflexivity; try eassumption.
Qed.

Lemma free_vars_in_bexp_has_variable :
  forall (bexp: bexp_Dan) (idents: ListSet.set ident) (x0: ident),
    idents = free_vars_bexp_src bexp ->
    (In x0 idents <->
       bexp_has_variable x0 bexp).
Proof.
  split; intros; [ eapply bool_wf_help; eassumption | ].
  revert idents x0 H H0. induction bexp; intros.
  - invs H0.
  - invs H0.
  - invs H0. apply IHbexp.
    + cbn. reflexivity.
    + assumption.
  - invs H0.
    + pose proof (IHbexp1 (free_vars_bexp_src bexp1) x0 eq_refl H3).
      unfold free_vars_bexp_src in *.    
      pose proof (ListSet.set_union_iff
      string_dec x0         
     ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
         match exp with
         | NEG_Dan b => free_vars_bexp_src b
         | AND_Dan b1 b2 | OR_Dan b1 b2 =>
             ListSet.set_union string_dec (free_vars_bexp_src b1)
               (free_vars_bexp_src b2)
         | LEQ_Dan a1 a2 =>
             ListSet.set_union string_dec (free_vars_aexp_src a1)
               (free_vars_aexp_src a2)
         | _ => ListSet.empty_set string
         end) bexp1)
     ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
         match exp with
         | NEG_Dan b => free_vars_bexp_src b
         | AND_Dan b1 b2 | OR_Dan b1 b2 =>
             ListSet.set_union string_dec (free_vars_bexp_src b1)
               (free_vars_bexp_src b2)
         | LEQ_Dan a1 a2 =>
             ListSet.set_union string_dec (free_vars_aexp_src a1)
               (free_vars_aexp_src a2)
         | _ => ListSet.empty_set string
         end) bexp2)).
         destruct H1. apply H2. left. apply H.
    + pose proof (IHbexp2 (free_vars_bexp_src bexp2) x0 eq_refl H3).
      unfold free_vars_bexp_src in *.    
      pose proof (ListSet.set_union_iff
      string_dec x0         
    ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
        match exp with
        | NEG_Dan b => free_vars_bexp_src b
        | AND_Dan b1 b2 | OR_Dan b1 b2 =>
            ListSet.set_union string_dec (free_vars_bexp_src b1)
              (free_vars_bexp_src b2)
        | LEQ_Dan a1 a2 =>
            ListSet.set_union string_dec (free_vars_aexp_src a1)
              (free_vars_aexp_src a2)
        | _ => ListSet.empty_set string
        end) bexp1)
    ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
        match exp with
        | NEG_Dan b => free_vars_bexp_src b
        | AND_Dan b1 b2 | OR_Dan b1 b2 =>
            ListSet.set_union string_dec (free_vars_bexp_src b1)
              (free_vars_bexp_src b2)
        | LEQ_Dan a1 a2 =>
            ListSet.set_union string_dec (free_vars_aexp_src a1)
              (free_vars_aexp_src a2)
        | _ => ListSet.empty_set string
        end) bexp2)).
        destruct H1. apply H2. right. apply H.
  - invs H0.
    + pose proof (IHbexp1 (free_vars_bexp_src bexp1) x0 eq_refl H3).
      unfold free_vars_bexp_src in *.    
      pose proof (ListSet.set_union_iff
      string_dec x0         
    ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
        match exp with
        | NEG_Dan b => free_vars_bexp_src b
        | AND_Dan b1 b2 | OR_Dan b1 b2 =>
            ListSet.set_union string_dec (free_vars_bexp_src b1)
              (free_vars_bexp_src b2)
        | LEQ_Dan a1 a2 =>
            ListSet.set_union string_dec (free_vars_aexp_src a1)
              (free_vars_aexp_src a2)
        | _ => ListSet.empty_set string
        end) bexp1)
    ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
        match exp with
        | NEG_Dan b => free_vars_bexp_src b
        | AND_Dan b1 b2 | OR_Dan b1 b2 =>
            ListSet.set_union string_dec (free_vars_bexp_src b1)
              (free_vars_bexp_src b2)
        | LEQ_Dan a1 a2 =>
            ListSet.set_union string_dec (free_vars_aexp_src a1)
              (free_vars_aexp_src a2)
        | _ => ListSet.empty_set string
        end) bexp2)).
        destruct H1. apply H2. left. apply H.
    + pose proof (IHbexp2 (free_vars_bexp_src bexp2) x0 eq_refl H3).
      unfold free_vars_bexp_src in *.    
      pose proof (ListSet.set_union_iff
      string_dec x0         
    ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
        match exp with
        | NEG_Dan b => free_vars_bexp_src b
        | AND_Dan b1 b2 | OR_Dan b1 b2 =>
            ListSet.set_union string_dec (free_vars_bexp_src b1)
              (free_vars_bexp_src b2)
        | LEQ_Dan a1 a2 =>
            ListSet.set_union string_dec (free_vars_aexp_src a1)
              (free_vars_aexp_src a2)
        | _ => ListSet.empty_set string
        end) bexp1)
    ((fix free_vars_bexp_src (exp : bexp_Dan) : ListSet.set string :=
        match exp with
        | NEG_Dan b => free_vars_bexp_src b
        | AND_Dan b1 b2 | OR_Dan b1 b2 =>
            ListSet.set_union string_dec (free_vars_bexp_src b1)
              (free_vars_bexp_src b2)
        | LEQ_Dan a1 a2 =>
            ListSet.set_union string_dec (free_vars_aexp_src a1)
              (free_vars_aexp_src a2)
        | _ => ListSet.empty_set string
        end) bexp2)).
        destruct H1. apply H2. right. apply H.
  - invs H0.
    + unfold free_vars_bexp_src. 
      unfold free_vars_aexp_src. pose proof (ListSet.set_union_iff
        string_dec x0
        ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
        match exp with
        | VAR_Dan x =>
            ListSet.set_add string_dec x (ListSet.empty_set string)
        | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
            ListSet.set_union string_dec (free_vars_aexp_src a0)
              (free_vars_aexp_src a3)
        | APP_Dan _ aexps =>
            fold_left
              (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
              (ListSet.empty_set string)
        | _ => ListSet.empty_set string
        end) a1)
    ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
        match exp with
        | VAR_Dan x =>
            ListSet.set_add string_dec x (ListSet.empty_set string)
        | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
            ListSet.set_union string_dec (free_vars_aexp_src a0)
              (free_vars_aexp_src a3)
        | APP_Dan _ aexps =>
            fold_left
              (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
              (ListSet.empty_set string)
        | _ => ListSet.empty_set string
        end) a2)).
          destruct H. apply H1. left. 
          pose proof free_vars_in_aexp_has_variable a1 (free_vars_aexp_src a1) x0 eq_refl.
          apply H2.  
          apply H3.
    + unfold free_vars_bexp_src. 
      unfold free_vars_aexp_src. pose proof (ListSet.set_union_iff
        string_dec x0
        ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
        match exp with
        | VAR_Dan x =>
            ListSet.set_add string_dec x (ListSet.empty_set string)
        | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
            ListSet.set_union string_dec (free_vars_aexp_src a0)
              (free_vars_aexp_src a3)
        | APP_Dan _ aexps =>
            fold_left
              (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
              (ListSet.empty_set string)
        | _ => ListSet.empty_set string
        end) a1)
    ((fix free_vars_aexp_src (exp : aexp_Dan) : ListSet.set string :=
        match exp with
        | VAR_Dan x =>
            ListSet.set_add string_dec x (ListSet.empty_set string)
        | PLUS_Dan a0 a3 | MINUS_Dan a0 a3 =>
            ListSet.set_union string_dec (free_vars_aexp_src a0)
              (free_vars_aexp_src a3)
        | APP_Dan _ aexps =>
            fold_left
              (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y)) aexps
              (ListSet.empty_set string)
        | _ => ListSet.empty_set string
        end) a2)).
          destruct H. apply H1. right. 
          pose proof free_vars_in_aexp_has_variable a2 (free_vars_aexp_src a2) x0 eq_refl.
          apply H2.  
          apply H3.   
Qed. 

Lemma free_vars_in_imp_has_variable :
  forall (imp: imp_Dan) (idents : ListSet.set ident) (x0: ident),
    idents = free_vars_imp_src imp ->
    (In x0 idents <->
       imp_has_variable x0 imp).
Proof.
  induction imp; intros idents x0 FREE; (split; [ intros IN | intros HAS ]).
  - simpl in FREE. rewrite FREE in IN.
    eapply ListSet.set_union_iff in IN. destruct IN; match goal with
                                                     | [ H : In _ (ListSet.set_union _ _ _) |- _ ] =>
                                                         eapply ListSet.set_union_iff in H; destruct H
                                                     | _ =>
                                                         idtac
                                                     end.
    + econstructor. eapply free_vars_in_bexp_has_variable in H.
      eassumption. reflexivity.
    + eapply ImpHasVarIf__then. eapply IHimp1. ereflexivity. assumption.
    + eapply ImpHasVarIf__else. eapply IHimp2. ereflexivity. assumption.
  - invs HAS; simpl; eapply ListSet.set_union_iff.
    + left. eapply free_vars_in_bexp_has_variable. ereflexivity. eassumption.
    + right. eapply ListSet.set_union_iff. left. eapply IHimp1; auto.
    + right. eapply ListSet.set_union_iff. right. eapply IHimp2; auto.
  - invs FREE. simpl in IN. invs IN.
  - invs HAS.
  - simpl in FREE. rewrite FREE in IN. eapply ListSet.set_union_iff in IN. destruct IN.
    + eapply ImpHasVarWhile__body. eapply IHimp; eauto.
    + eapply ImpHasVarWhile__cond. eapply free_vars_in_bexp_has_variable; eauto.
  - invs HAS; simpl; eapply ListSet.set_union_iff.
    + right. eapply free_vars_in_bexp_has_variable; eauto.
    + left. eapply IHimp; eauto.
  - rewrite FREE in IN. simpl in IN. eapply ListSet.set_add_iff in IN.
    destruct IN.
    + econstructor. rewrite H. destruct (x =? x)%string eqn:EQ.
      * reflexivity.
      * eapply String.eqb_neq in EQ.
        assert (x = x) by auto. eapply EQ in H0. invs H0.
    + eapply ImpHasVarAssigned. eapply free_vars_in_aexp_has_variable; eauto.
  - invs HAS.
    + eapply String.eqb_eq in H1. simpl. eapply ListSet.set_add_iff. left. auto.
    + simpl. eapply ListSet.set_add_iff. right. eapply free_vars_in_aexp_has_variable; eauto.
  - rewrite FREE in IN. simpl in IN. eapply ListSet.set_union_iff in IN. destruct IN.
    + econstructor. eapply IHimp1; eauto.
    + eapply ImpHasVarSeq__right. eapply IHimp2; eauto.
  - invs HAS; simpl; eapply ListSet.set_union_iff; [ left; eapply IHimp1 | right; eapply IHimp2 ]; eauto.
Qed.

Lemma free_vars_in_args_has_variable :
  forall (args: list aexp_Dan) (idents: ListSet.set ident) (f: ident) (x0: ident),
    idents = free_vars_aexp_src (APP_Dan f args) ->
    (In x0 idents <->
       args_has_variable x0 args).
Proof.
  induction args; intros idents f x0 FREE; (split; [ intros IN | intros HAS ]).
  - simpl in FREE. subst. invs IN.
  - simpl in FREE. invs HAS.
  - simpl in FREE. subst. eapply variable_in_elim' in IN. eapply ListSet.set_union_iff in IN. destruct IN.
    + eapply ArgsHasVarFirst.
      eapply ListSet.set_union_emptyR in H.
      eapply free_vars_in_aexp_has_variable; eauto.
    + eapply ArgsHasVarRest.
      eapply IHargs.
      * ereflexivity.
      * simpl. eassumption.
  - simpl in IHargs. simpl in FREE. rewrite FREE. eapply variable_in_elim'. eapply ListSet.set_union_iff. invs HAS.
    + left. eapply ListSet.set_union_iff. left. eapply free_vars_in_aexp_has_variable; eauto.
    + right. eapply IHargs in H1. eassumption. eassumption. ereflexivity.
      Unshelve.
      eassumption.
Qed.

Lemma has_args_app_case :
  forall (args: list aexp_Dan) (f: ident) (aexp_var_map: ListSet.set ident) (x: ident),
    aexp_var_map = free_vars_aexp_src (APP_Dan f args) ->
    In x aexp_var_map ->
    args_has_variable x args.
Proof.
  induction args; intros.
  - simpl in H. rewrite H in H0. invs H0.
  - simpl in H. subst. eapply variable_in_elim' in H0.
    eapply ListSet.set_union_iff in H0. destruct H0.
    + eapply ListSet.set_union_emptyR in H. econstructor. eapply free_vars_in_aexp_has_variable_forwards. ereflexivity. eassumption.
    + eapply ArgsHasVarRest. eapply IHargs. ereflexivity. simpl. assumption.
      Unshelve.
      apply f.
Qed.



Lemma var_map_wf_plus_dan_forwards :
  forall (a1 a2: aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents (PLUS_Dan a1 a2) ->
    var_map_wf_wrt_aexp idents a1 /\ var_map_wf_wrt_aexp idents a2.
Proof.
  intros; unfold_wf_aexp_in H; (split; (unfold_wf_aexp; [eapply WF | .. ]); intros).
  - eapply A. ereflexivity.
    simpl.
    rewrite H in H0.
    eapply ListSet.set_union_intro1.
    eassumption.
  - eapply free_vars_in_aexp_has_variable; eassumption.
  - eapply C.
    ereflexivity.
    eapply ListSet.set_union_intro1.
    fold free_vars_aexp_src. rewrite H in H0. eassumption.
  - eapply has_args_app_case.
    rewrite H in H0. eassumption.
    eassumption.
  - eapply A. ereflexivity.
    simpl. rewrite H in H0. eapply ListSet.set_union_intro2.
    eassumption.
  - eapply free_vars_in_aexp_has_variable; eassumption.
  - eapply C. ereflexivity.
    simpl.
    eapply ListSet.set_union_intro2.
    fold free_vars_aexp_src. rewrite H in H0.
    eassumption.
  - rewrite H in H0. eapply has_args_app_case; eassumption.
Qed.


Lemma var_map_wf_plus_dan_backwards :
  forall (a1 a2: aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents a1 ->
    var_map_wf_wrt_aexp idents a2 ->
    var_map_wf_wrt_aexp idents (PLUS_Dan a1 a2).
Proof.
  intros.
  unfold_wf_aexp_in H; unfold_wf_aexp_in H0; unfold_wf_aexp; [ eapply WF | .. ]; intros;
    match goal with
    | [ H: ?idents = free_vars_aexp_src _ |- _ ] =>
        try simpl in H;
        match goal with
        | [ H' : In _ idents |- _ ] =>
            rewrite H in H'
        end
    end.
  - set_fold_destruct H0.
    + eapply A; eauto.
    + eapply A0; eauto.
  - set_fold_destruct H0; [ eapply AexpHasVarPlus__left | eapply AexpHasVarPlus__right ]; [eapply B | eapply B0 ]; eauto.
  - set_fold_destruct H0; [eapply C | eapply C0]; eauto.
  - invs H.
Qed.

Lemma var_map_wf_minus_dan_forwards :
  forall (a1 a2: aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents (MINUS_Dan a1 a2) ->
    var_map_wf_wrt_aexp idents a1 /\
      var_map_wf_wrt_aexp idents a2.
Proof.
  intros.
  unfold_wf_aexp_in H;
    (split;
     (unfold_wf_aexp;
      [ eapply WF
      | intros; eapply A;
        [ ereflexivity
        | simpl; rewrite H in H0;
          solve [ eapply ListSet.set_union_intro1; eassumption
                | eapply ListSet.set_union_intro2; eassumption]]
      | intros; eapply free_vars_in_aexp_has_variable; eassumption
      | intros; eapply C;
        [ ereflexivity
        | rewrite H in H0;
          solve [eapply ListSet.set_union_intro2; fold free_vars_aexp_src; eassumption | eapply ListSet.set_union_intro1; fold free_vars_aexp_src; eassumption ] ] 
      | intros; rewrite H in H0; eapply has_args_app_case; eassumption ])).
Qed.

Lemma var_map_wf_minus_dan_backwards :
  forall (a1 a2: aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents a1 ->
    var_map_wf_wrt_aexp idents a2 ->
    var_map_wf_wrt_aexp idents (MINUS_Dan a1 a2).
Proof.
  intros.
  unfold_wf_aexp_in H; unfold_wf_aexp_in H0; unfold_wf_aexp; [ eapply WF | .. ]; intros;
    match goal with
    | [ H: ?idents = free_vars_aexp_src _ |- _ ] =>
        try simpl in H;
        match goal with
        | [ H' : In _ idents |- _ ] =>
            rewrite H in H'
        end
    end.
  - set_fold_destruct H0.
    + eapply A; eauto.
    + eapply A0; eauto.
  - set_fold_destruct H0; [ eapply AexpHasVarMinus__left | eapply AexpHasVarMinus__right ]; [eapply B | eapply B0 ]; eauto.
  - set_fold_destruct H0; [eapply C | eapply C0]; eauto.
  - invs H.
Qed.

Lemma var_map_wf_app_dan_forwards :
  forall (arg: aexp_Dan) (args: list aexp_Dan) (f: ident) (idents: list ident),
    var_map_wf_wrt_aexp idents (APP_Dan f (arg :: args)) ->
    var_map_wf_wrt_aexp idents (APP_Dan f args).
Proof.
  intros. unfold_wf_aexp_in H. unfold_wf_aexp; [ eapply WF | intros .. ].
  - simpl in H. rewrite H in H0. eapply A.
    simpl. ereflexivity.
    eapply variable_in_elim'.
    eapply ListSet.set_union_intro2. eassumption.
  - eapply free_vars_in_aexp_has_variable; eauto.
  - eapply C. ereflexivity.
    simpl. eapply variable_in_elim'. simpl in H. rewrite H in H0.
    eapply ListSet.set_union_intro2. eassumption.
  - rewrite H in H0. eapply has_args_app_case; eassumption.
Qed.
  

Lemma var_map_wf_app_dan_backwards :
  forall (arg: aexp_Dan) (args: list aexp_Dan) (f: ident) (idents: list ident),
    var_map_wf_wrt_aexp idents arg ->
    var_map_wf_wrt_aexp idents (APP_Dan f args) ->
    var_map_wf_wrt_aexp idents (APP_Dan f (arg :: args)).
Proof.
  intros.
  unfold_wf_aexp_in H.
  unfold_wf_aexp; [ | intros .. ].
  - eapply WF.
  - simpl in H. rewrite H in H1. eapply variable_in_elim' in H1. eapply ListSet.set_union_iff in H1. destruct H1.
    + eapply A. ereflexivity.
      eapply ListSet.set_union_iff in H1. destruct H1.
      * eassumption.
      * invs H1.
    + unfold_wf_aexp_in H0. eapply A0; eauto.
  - simpl in H. rewrite H in H1. eapply variable_in_elim' in H1. eapply ListSet.set_union_iff in H1. destruct H1.
    + econstructor.
      econstructor.
      simpl in H1.
      eapply free_vars_in_aexp_has_variable; eauto.
    + econstructor. eapply ArgsHasVarRest.
      unfold_wf_aexp_in H0. eapply D0; eauto.
  - simpl in H. rewrite H in H1. eapply variable_in_elim' in H1. eapply ListSet.set_union_iff in H1. destruct H1.
    + eapply C.
      * ereflexivity.
      * simpl in H1. eassumption.
    + unfold_wf_aexp_in H0.
      eapply C0.
      * ereflexivity.
      * simpl. assumption.
  - invs H. simpl in H2. eapply variable_in_elim' in H2. eapply ListSet.set_union_iff in H2. simpl in H2. destruct H2.
    + econstructor. eapply free_vars_in_aexp_has_variable; eauto.
    + eapply ArgsHasVarRest. eapply free_vars_in_args_has_variable; eauto.
      Unshelve.
      eassumption.
Qed.

Lemma var_map_wf_app_dan_first :
  forall (a: aexp_Dan) f (aexp: aexp_Dan) (aexps: list aexp_Dan) (idents: list ident),
    a = APP_Dan f (aexp :: aexps) ->
    var_map_wf_wrt_aexp idents a ->
    var_map_wf_wrt_aexp idents aexp.
Proof.
  intros a f aexp aexps idents APP WF.
  unfold var_map_wf_wrt_aexp, var_map_wf in WF.
  unfold_wf_aexp; intros; [ | unfold_wf_aexp_in WF; clear WF0; subst  .. ].
  - eapply WF.
  - eapply A. ereflexivity. refold free_vars_aexp_src. simpl.
    eapply variable_in_elim'. eapply ListSet.set_union_iff.
    left.
    eapply ListSet.set_union_iff.
    left.
    assumption.
  - eapply free_vars_in_aexp_has_variable_forwards; try ereflexivity; eassumption.
  - eapply C. ereflexivity. refold free_vars_aexp_src. simpl. eapply variable_in_elim'. eapply ListSet.set_union_iff. left.
    eapply ListSet.set_union_iff. left.
    assumption.
  - eapply has_args_app_case. ereflexivity.
    eassumption.
Qed.

Lemma var_map_wf_app_dan_args_all :
  forall (args: list aexp_Dan) (f: ident) (idents: list ident),
    var_map_wf_wrt_aexp idents (APP_Dan f args) ->
    Forall (var_map_wf_wrt_aexp idents) args.
Proof.
induction args; intros.
- constructor. 
- constructor.
  + apply (var_map_wf_app_dan_first  (APP_Dan f (a :: args)) f a args idents eq_refl H). 
  + apply var_map_wf_app_dan_forwards in H. eapply IHargs. eassumption.
Qed. 
  

Lemma var_map_wf_neg_dan_forwards :
  forall (b1 b2: bexp_Dan) (idents: list ident),
    b2 = NEG_Dan b1 ->
    var_map_wf_wrt_bexp idents b1 ->
    var_map_wf_wrt_bexp idents b2.
Proof.
  intros. unfold_wf_bexp_in H0.
  unfold_wf_bexp; [ eapply WF | intros; rewrite H in *; simpl in H0; rewrite H0 in H1 .. ].
  - eapply A. ereflexivity. eassumption.
  - econstructor. eapply free_vars_in_bexp_has_variable; eauto.
    rewrite H0. eassumption.
  - eapply C. ereflexivity. eassumption.
Qed.

Lemma var_map_wf_neg_dan :
  forall (b1 b2: bexp_Dan) (idents: list ident),
    b2 = NEG_Dan b1 ->
    var_map_wf_wrt_bexp idents b2 ->
    var_map_wf_wrt_bexp idents b1.
Proof.
  intros b1 b2 idents NEG WF. unfold_wf_bexp_in WF; unfold_wf_bexp; intros; [ | clear WF0 .. ].
  - eapply WF0.
  - eapply A; try rewrite NEG; simpl; eassumption.
  - eapply bool_wf_help; eassumption.
  - eapply C. rewrite NEG. simpl. econstructor.
    match goal with
    | [ H: ?bexp_var_map = free_vars_bexp_src ?b1,
          H': In ?x ?bexp_var_map |- _ ] =>
        rewrite H in H0; eassumption
    end.
Qed.


Lemma var_map_wf_and_or_dan_forwards :
  forall (b1 b2 b3: bexp_Dan) (idents: list ident),
    (b3 = (AND_Dan b1 b2) \/ b3 = (OR_Dan b1 b2)) ->
    var_map_wf_wrt_bexp idents b3 ->
    var_map_wf_wrt_bexp idents b1 /\ var_map_wf_wrt_bexp idents b2.
Proof.
  intros b1 b2 b3 idents BOOL WF. unfold_wf_bexp_in WF; (split; (unfold_wf_bexp; [ eapply WF0 | clear WF0; intros .. ])).
  - destruct BOOL; subst; (eapply A; [ ereflexivity
                                     | simpl; eapply ListSet.set_union_intro1; eassumption ]).
  - eapply free_vars_in_bexp_has_variable; eauto.
  - destruct BOOL; subst; (eapply C; [ ereflexivity
                                     | simpl; eapply ListSet.set_union_intro1; eassumption ]).
  - destruct BOOL; subst; (eapply A; [ ereflexivity
                                     | simpl; eapply ListSet.set_union_intro2; eassumption ]).
  - eapply free_vars_in_bexp_has_variable; eauto.
  - destruct BOOL; subst; (eapply C; [ ereflexivity
                                     | simpl; eapply ListSet.set_union_intro2; eassumption ]).
Qed.

Lemma var_map_wf_and_or_dan_left :
  forall (b1 b2 b3: bexp_Dan) (idents: list ident),
    (b3 = (AND_Dan b1 b2) \/ b3 = (OR_Dan b1 b2)) ->
    var_map_wf_wrt_bexp idents b3 ->
    var_map_wf_wrt_bexp idents b1.
Proof.
  intros b1 b2 b3 idents BOOL WF. unfold_wf_bexp_in WF; unfold_wf_bexp; intros; [ | clear WF0 .. ].
  - eapply WF0.
  - destruct BOOL; match goal with
                   | [ BOOL': ?b3 = _ ?b1 ?b2 |- _ ] =>
                       rewrite BOOL' in *
                   end;
      (eapply A; [ ereflexivity | ]);
      simpl; eapply ListSet.set_union_iff; left;
      match goal with
      | [ H: ?bexp_var_map = free_vars_bexp_src ?b1,
            H': In ?x ?bexp_var_map |- _ ] =>
          rewrite H in H'; eassumption
      end.
  - eapply bool_wf_help; eassumption.
  - destruct BOOL; match goal with
                   | [ BOOL': ?b3 = _ ?b1 ?b2 |- _ ] =>
                       rewrite BOOL' in *
                   end;
      (eapply C; [ ereflexivity | ]);
      simpl; eapply ListSet.set_union_iff; left;
      match goal with
      | [ H: ?bexp_var_map = free_vars_bexp_src ?b1,
            H': In ?x ?bexp_var_map |- _ ] =>
          rewrite H in H'; eassumption
      end.
Qed.

Lemma var_map_wf_and_or_dan_right :
  forall (b1 b2 b3: bexp_Dan) (idents: list ident),
    (b3 = (AND_Dan b1 b2) \/ b3 = (OR_Dan b1 b2)) ->
    var_map_wf_wrt_bexp idents b3 ->
    var_map_wf_wrt_bexp idents b2.
Proof.
  intros b1 b2 b3 idents BOOL WF. unfold_wf_bexp_in WF; unfold_wf_bexp; intros; [ | clear WF0 .. ].
  - eapply WF0.
  - destruct BOOL; match goal with
                   | [ BOOL': ?b3 = _ ?b1 ?b2 |- _ ] =>
                       rewrite BOOL' in *
                   end;
      (eapply A; [ ereflexivity | ]);
      simpl; eapply ListSet.set_union_iff; right;
      match goal with
      | [ H: ?bexp_var_map = free_vars_bexp_src ?b1,
            H': In ?x ?bexp_var_map |- _ ] =>
          rewrite H in H'; eassumption
      end.
  - eapply bool_wf_help; eassumption.
  - destruct BOOL; match goal with
                   | [ BOOL': ?b3 = _ ?b1 ?b2 |- _ ] =>
                       rewrite BOOL' in *
                   end;
      (eapply C; [ ereflexivity | ]);
      simpl; eapply ListSet.set_union_iff; right;
      match goal with
      | [ H: ?bexp_var_map = free_vars_bexp_src ?b1,
            H': In ?x ?bexp_var_map |- _ ] =>
          rewrite H in H'; eassumption
      end.
Qed.

Lemma var_map_wf_leq_dan_forwards :
  forall (b: bexp_Dan) (a1 a2: aexp_Dan) (idents: list ident),
    b = LEQ_Dan a1 a2 ->
    var_map_wf_wrt_bexp idents b ->
    var_map_wf_wrt_aexp idents a1 /\ var_map_wf_wrt_aexp idents a2.
Proof.
  intros b a1 a2 idents LEQ WF. unfold_wf_bexp_in WF; (split; (unfold_wf_aexp; [ eapply WF0 | clear WF0; intros; rewrite LEQ in *; clear LEQ .. ])).
  - eapply A; [ ereflexivity
              | simpl; eapply ListSet.set_union_intro1; rewrite H in H0; eassumption ].
  - eapply free_vars_in_aexp_has_variable; eauto.
  - eapply C; [ ereflexivity
              | simpl; eapply ListSet.set_union_intro1; rewrite H in H0; eassumption ].
  - eapply has_args_app_case; [ ereflexivity | ].
    rewrite H0 in H1. rewrite H in H1.  eassumption.
  - eapply A; [ ereflexivity
              | simpl; eapply ListSet.set_union_intro2; rewrite H in H0; eassumption ].
  - eapply free_vars_in_aexp_has_variable; eauto.
  - eapply C; [ ereflexivity
              | simpl; eapply ListSet.set_union_intro2; rewrite H in H0; eassumption ].
  - eapply has_args_app_case; [ ereflexivity | ].
    rewrite H0 in H1. rewrite H in H1. eassumption.
Qed.


Lemma var_map_wf_leq_dan_left :
  forall (b: bexp_Dan) (a1 a2: aexp_Dan) (idents: list ident),
    b = LEQ_Dan a1 a2 ->
    var_map_wf_wrt_bexp idents b ->
    var_map_wf_wrt_aexp idents a1.
Proof.
  intros b a1 a2 idents LEQ WF.
  unfold_wf_bexp_in WF.
  unfold_wf_aexp; intros; [ | destruct WF0 as (NODUP & _) .. ].
  - eapply WF0.
  - eapply A; rewrite LEQ.
    ereflexivity.
    simpl. eapply ListSet.set_union_iff. left. rewrite H in H0.
    eassumption.
  - eapply free_vars_in_aexp_has_variable_forwards; eassumption.
  - eapply find_index_rel_in.
    eassumption.
    assumption.
    intros.
    eapply A.
    ereflexivity.
    rewrite LEQ. simpl. eapply ListSet.set_union_iff. left. rewrite <- H.
    assumption.
    assumption.
  - intros. eapply has_args_app_case.
    rewrite H in H0. eassumption.
    assumption.
Qed.

Lemma var_map_wf_leq_dan_right :
  forall (b: bexp_Dan) (a1 a2: aexp_Dan) (idents: list ident),
    b = LEQ_Dan a1 a2 ->
    var_map_wf_wrt_bexp idents b ->
    var_map_wf_wrt_aexp idents a2.
Proof.
  intros b a1 a2 idents LEQ WF.
  unfold_wf_bexp_in WF.
  unfold_wf_aexp; intros; [ | destruct WF0 as (NODUPS & _) .. ].
  - eapply WF0.
  - eapply A; rewrite LEQ.
    ereflexivity.
    simpl. eapply ListSet.set_union_iff. right. rewrite H in H0.
    eassumption.
  - eapply free_vars_in_aexp_has_variable_forwards; eassumption.
  - eapply find_index_rel_in.
    eassumption.
    assumption.
    intros.
    eapply A.
    ereflexivity.
    rewrite LEQ. simpl. eapply ListSet.set_union_iff. right. rewrite <- H.
    assumption.
    assumption.
  - intros. eapply has_args_app_case.
    rewrite H in H0. eassumption.
    assumption.
Qed.


Lemma var_map_wf_plus_minus_dan_left :
  forall a1 a2 a3 idents,
    (a3 = PLUS_Dan a1 a2 \/ a3 = MINUS_Dan a1 a2) ->
     var_map_wf_wrt_aexp idents a3 ->
     var_map_wf_wrt_aexp idents a1.
Proof.
  intros a1 a2 a3 idents PLUS_MINUS WF.
  unfold_wf_aexp_in WF.
  unfold_wf_aexp.
  - eapply WF0.
  - all: intros.
    + eapply A.
      * destruct PLUS_MINUS; simpl; subst; ereflexivity. 
      * destruct PLUS_MINUS; subst; simpl; eapply ListSet.set_union_iff; left; eassumption.
  - eapply free_vars_in_aexp_has_variable_forwards; eassumption.
  - intros. eapply C. ereflexivity.
    destruct PLUS_MINUS; subst;
      unfold free_vars_aexp_src; fold free_vars_aexp_src;
      eapply ListSet.set_union_iff; left; assumption.
  - intros. eapply has_args_app_case. ereflexivity. subst. eassumption.
Qed.

Lemma var_map_wf_plus_minus_dan_right :
  forall a1 a2 a3 idents,
    (a3 = PLUS_Dan a1 a2 \/ a3 = MINUS_Dan a1 a2) ->
     var_map_wf_wrt_aexp idents a3 ->
     var_map_wf_wrt_aexp idents a2.
Proof.
  intros a1 a2 a3 idents PLUS_MINUS WF.
  unfold_wf_aexp_in WF.
  unfold_wf_aexp.
  - eapply WF0.
  - all: intros.
    + eapply A.
      * destruct PLUS_MINUS; simpl; subst; ereflexivity. 
      * destruct PLUS_MINUS; subst; simpl;
          eapply ListSet.set_union_iff; right;
          eassumption.
  - eapply free_vars_in_aexp_has_variable_forwards; eassumption.
  - intros. eapply C. ereflexivity.
    destruct PLUS_MINUS; subst;
      unfold free_vars_aexp_src; fold free_vars_aexp_src;
      eapply ListSet.set_union_iff; right; assumption.
  - intros. eapply has_args_app_case. ereflexivity. subst. eassumption.
Qed.


Lemma var_map_wf_app_dan_rest :
  forall (a: aexp_Dan) (f: ident) (aexp: aexp_Dan) (aexps: list aexp_Dan) (idents: list ident),
    a = APP_Dan f (aexp :: aexps) ->
    var_map_wf_wrt_aexp idents a ->
    var_map_wf_wrt_aexp idents (APP_Dan f aexps).
Proof.
  intros a f aexp aexps idents APP WF.
  unfold_wf_aexp_in WF.
  unfold_wf_aexp; intros; rewrite APP in *.
  - eapply WF0.
  - eapply A. ereflexivity. refold free_vars_aexp_src. simpl.
    eapply variable_in_elim'. eapply ListSet.set_union_iff.
    right.
    match goal with
    | [ H0 : ?var_map = free_vars_aexp_src _,
          H1: In ?x ?var_map |-
          In ?x _ ] =>
        simpl in H0; rewrite H0 in H1
    end.
    assumption.
  - eapply free_vars_in_aexp_has_variable_forwards; eassumption.
  - eapply C. ereflexivity. refold free_vars_aexp_src. eapply variable_in_elim'. eapply ListSet.set_union_iff. right.
    match goal with
    | [ H0 : ?var_map = free_vars_aexp_src _,
          H1: In ?x ?var_map |-
          In ?x _ ] =>
        simpl in H0; rewrite H0 in H1
    end.
    assumption.
  - eapply has_args_app_case. ereflexivity.
    match goal with
    | [ H1 : ?var_map = free_vars_aexp_src ?aexp,
          H2 : In ?x ?var_map |- _ ] =>
        rewrite H1 in H2;
        match goal with
        | [ H' : aexp = ?aexp' |- _ ] =>
                 invs H'
        end
    end.
    assumption.
    Unshelve.
    assumption.
Qed.

Lemma var_map_wf_app_dan_first_and_rest :
  forall (a: aexp_Dan) (f: ident) (aexp: aexp_Dan) (aexps: list aexp_Dan) (idents: list ident),
    a = APP_Dan f (aexp :: aexps) ->
    var_map_wf_wrt_aexp idents a ->
    var_map_wf_wrt_aexp idents aexp /\ var_map_wf_wrt_aexp idents (APP_Dan f aexps).
Proof.
  intros; split.
  - eapply var_map_wf_app_dan_first; eassumption.
  - eapply var_map_wf_app_dan_rest; eassumption.
Qed.
Local Open Scope string_scope.
Local Open Scope list_scope.

Compute (ListSet.set_fold_left (fun (acc : list string) (x: string) => x :: acc) (ListSet.set_union string_dec (ListSet.empty_set string) ("z" :: "y" :: nil))).

Lemma no_dup_set_add_is_append :
  forall (s: ListSet.set string)
    (x: string),
    NoDup (x :: s) ->
    ListSet.set_add string_dec x s = s ++ (x :: nil).
Proof.
  induction s; intros.
  - simpl. reflexivity.
  - invs H.
    invs H3.
    eapply IHs in H3.
    simpl.
    assert (x <> a).
    unfold not; intros.
    assert (In x (a :: s)) by (econstructor; symmetry; eassumption).
    eapply H2 in H1. eassumption.
    destruct (string_dec x a).
    + eapply H0 in e. invs e.
    + assert (~ (In x s)).
      unfold not. intros.
      assert (In x (a :: s)).
      eapply in_cons.
      eassumption.
      invs H.
      eapply H9 in H6. eassumption.
      assert (NoDup (x :: s)) by (econstructor; eassumption).
      eapply IHs in H6.
      rewrite H6. reflexivity.
Qed.

Lemma in_append :
  forall (s1 s2: ListSet.set string)
    (x: string),
    In x (s1 ++ s2) <-> (In x s1) \/ (In x s2).
Proof.
  induction s1; split; intros.
  - simpl in H. right. eassumption.
  - destruct H; [ invs H | ].
    simpl. eassumption.
  - simpl. simpl in H.
    destruct H.
    + left; left. eassumption.
    + eapply IHs1 in H. destruct H.
      * left; right. eassumption.
      * right. eassumption.
  - simpl. simpl in H. destruct H.
    + destruct H.
      * left. eassumption.
      * right. eapply IHs1. left. eassumption.
    + right. eapply IHs1. right. eassumption.
Qed.

Lemma in_preserved_by_reverse :
  forall (s: ListSet.set string)
    (x: string),
    In x s <-> In x (rev s).
Proof.
  induction s; split; intros.
  - invs H.
  - invs H.
  - invs H.
    + simpl. eapply in_append. right. econstructor; reflexivity.
    + simpl. simpl in H. eapply IHs in H0. eapply in_append.
      left. eassumption.
  - simpl. simpl in H. eapply in_append in H. destruct H.
    + right. eapply IHs. eassumption.
    + left. invs H.
      * reflexivity.
      * invs H0.
Defined.

Lemma not_in_preserved_by_reverse :
  forall (s: ListSet.set string)
    (x: string),
    ~ (In x s) <-> ~ (In x (rev s)).
Proof.
  induction s; split; intros.
  - simpl. unfold not; intros. eassumption.
  - simpl in *. unfold not; intros. eassumption.
  - simpl. unfold not. intros.
    unfold not in H. eapply in_append in H0.
    destruct H0.
    + revert H0. fold (not (In x (rev s))).
      eapply IHs.
      unfold not; intros.
      assert (In x (a :: s)) by (eapply in_cons; eassumption).
      eapply H in H1. eassumption.
    + invs H0.
      * assert (In x (x :: s)) by (econstructor; reflexivity).
        eapply H in H1. eassumption.
      * invs H1.
  - unfold not; intros.
    invs H0.
    + simpl in H.
      assert (In x (rev s ++ (x :: nil))).
      eapply in_append. right. econstructor. reflexivity.
      eapply H in H1. eassumption.
    + revert H1. fold (not (In x s)).
      eapply IHs.
      simpl in H.
      invs H0.
      * assert (In x (rev s ++ (x :: nil))).
        eapply in_append.
        right. econstructor; reflexivity.
        unfold not; intros.
        eapply H in H1. eassumption.
      * unfold not. intros.
        assert (In x (rev s ++ a :: nil)).
        eapply in_append. left. eassumption.
        eapply H in H3. eassumption.
Qed.

Lemma not_in_append_not_in_either :
  forall (s1 s2: ListSet.set string)
    (x: string),
    ~ (In x (s1 ++ s2)) <-> (~ In x s1 /\ ~ In x s2).
Proof.
  induction s1; split; intros.
  - simpl in H. split. unfold not; intros. invs H0.
    eassumption.
  - destruct H.
    simpl. eassumption.
  - simpl in H. split.
    + unfold not; intros.
      unfold not in H.
      assert (a = x \/ In x (s1 ++ s2)).
      invs H0.
      left. reflexivity.
      right. eapply in_append. left. eassumption.
      eapply H. eassumption.
    + unfold not in H. unfold not; intros.
      assert (a = x \/ In x (s1 ++ s2)).
      right. eapply in_append. right. eassumption.
      eapply H. eassumption.
  - destruct H. simpl. unfold not. intros.
    destruct H1.
    + assert (In x (a :: s1)).
      econstructor; eassumption.
      eapply H; eassumption.
    + eapply in_append in H1. destruct H1.
      * assert (In x (a :: s1)) by (eapply in_cons; eassumption).
        eapply H. eassumption.
      * eapply H0. eassumption.
Qed.        

Lemma nodup_append :
  forall (s1 s2: ListSet.set string),
    NoDup (s1 ++ s2) <-> (NoDup s1 /\ NoDup s2 /\ (NoDup (s1 ++ s2))).
Proof.
  induction s1; split; intros.
  - simpl in H. simpl. split; [ econstructor | split; eassumption ].
  - destruct H as (H1 & H2 & H3).
    eassumption.
  - simpl in H. invs H.
    eapply IHs1 in H3. destruct H3 as (? & ? & ?).
    split; [ | split ].
    + econstructor.
      * eapply not_in_append_not_in_either in H2. destruct H2. eassumption.
      * eassumption.
    + eassumption.
    + simpl. eassumption.
  - destruct H as (? & ? & ?). simpl. econstructor.
    + unfold not. intros.
      simpl in H1. invs H1. eapply H5 in H2. eassumption.
    + invs H. eapply IHs1.
      invs H1.
      split; [ | split ]; eassumption.
Qed.

Lemma nodup_append_forward :
  forall (s1 s2: ListSet.set string),
    NoDup (s1 ++ s2) -> NoDup s1 /\ NoDup s2.
Proof.
  intros.
  eapply nodup_append in H.
  destruct H as ( ? & ? & ? ).
  split; eassumption.
Qed.

Lemma nodup_cons :
  forall (s: ListSet.set string)
    (a: string),
    NoDup (a :: s) ->
    ~ (In a s) /\ NoDup s.
Proof.
  intros.
  invs H. split; eassumption.
Qed.

Lemma nodup_preserved_by_reverse :
  forall (s: ListSet.set string),
    NoDup s <-> NoDup (rev s).
Proof.
  split; intros.
  - eapply NoDup_rev in H. eassumption.
  - rewrite <- rev_involutive.
    eapply NoDup_rev. eassumption.
Qed.

Compute (ListSet.set_union string_dec ("a" :: "a" :: nil) ("c" :: "d" :: nil)).

Lemma nil_set_union_is_reverse :
  forall (s: ListSet.set string),
    NoDup s ->
    ListSet.set_union string_dec nil s = rev s.
Proof.
  induction s; intros.
  - simpl. reflexivity.
  - simpl. invs H.
    eapply IHs in H3.
    rewrite H3. rewrite no_dup_set_add_is_append.
    reflexivity.
    invs H.
    econstructor.
    eapply not_in_preserved_by_reverse. rewrite rev_involutive.
    eassumption.
    eapply nodup_preserved_by_reverse in H5.
    eassumption.
Qed.



Compute (ListSet.set_union string_dec ("a" :: "b" :: nil) ("c" :: "d" :: nil)).
Compute (ListSet.set_union string_dec nil ("c" :: "d" :: nil)).
Compute (fold_left
           (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y))
           ((VAR_Dan "x") :: (PLUS_Dan (VAR_Dan "y") (VAR_Dan "z")) :: nil)
           
                  (ListSet.set_union string_dec (ListSet.empty_set string)
                                     ("a" :: "b" :: nil))).

Compute (fold_left
           (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y))
           ((VAR_Dan "x") :: (PLUS_Dan (VAR_Dan "y") (VAR_Dan "z")) :: nil)
           ("a" :: "b" :: nil)).
Compute (fold_left
           (fun (x : ListSet.set string) (y : aexp_Dan) =>
              ListSet.set_union string_dec x (free_vars_aexp_src y))
           ((VAR_Dan "x") :: (PLUS_Dan (VAR_Dan "y") (VAR_Dan "z")) :: nil)
           nil).

Lemma in_app_rev :
  forall (s1 s2: ListSet.set string) (x: string),
    In x (s1 ++ s2) <-> In x (s1 ++ (rev s2)).
Proof.
  induction s1; split; intros.
  - simpl. simpl in H. eapply in_preserved_by_reverse in H. eassumption.
  - simpl in *. eapply in_preserved_by_reverse. eassumption.
  - eapply in_app_or in H. eapply in_or_app.
    destruct H.
    + left. eassumption.
    + right. eapply in_preserved_by_reverse in H. eassumption.
  - eapply in_app_or in H. eapply in_or_app.
    destruct H.
    + left. eassumption.
    + right. eapply in_preserved_by_reverse. eassumption.
Qed.

Lemma nodup_app_rev :
  forall (s1 s2: ListSet.set string),
    NoDup (s1 ++ s2) <-> NoDup(s1 ++ (rev s2)).
Proof.
  induction s1; split; intros.
  - simpl in *. eapply nodup_preserved_by_reverse in H. eassumption.
  - simpl in *. eapply nodup_preserved_by_reverse. eassumption.
  - rewrite <- app_comm_cons in *.
    eapply NoDup_cons_iff in H.
    destruct H as (H1 & H2).
    eapply NoDup_cons_iff.
    split.
    + unfold not. intros.
      eapply in_app_rev in H. eapply H1 in H. eassumption.
    + eapply IHs1 in H2. eassumption.
  - rewrite <- app_comm_cons in *.
    eapply NoDup_cons_iff.
    eapply NoDup_cons_iff in H.
    destruct H. split.
    + unfold not; intros. eapply in_app_rev in H1. eapply H in H1. eassumption.
    + eapply IHs1. eassumption.
Qed.

Lemma not_in_musical_chairs :
  forall (s2: ListSet.set string) (a a0: string),
    NoDup (a0 :: s2) ->
    ~In a (a0 :: s2) -> ~In a0 (a :: s2).
Proof.
  destruct s2; intros.
  - unfold not. intros. invs H1.
    + eapply H0 in H1. eassumption.
    + invs H2.
  - unfold not. intros.
    invs H1.
    + eapply H0 in H1. eassumption.
    + invs H. eapply H5 in H2. eassumption.
Qed.

Lemma not_in_musical_chairs_app :
  forall (s1 s2: ListSet.set string) (a a0: string),
    ~ In a0 (a :: s1 ++ s2) <->
    ~ In a0 (s1 ++ a :: s2).
Proof.
  induction s1; split; intros; unfold not; intros; simpl in *.
  - eapply H in H0. eassumption.
  - eapply H in H0. eassumption.
  - destruct H0.
    + assert (a0 = a1 \/ a = a1 \/ In a1 (s1 ++ s2)) by (right; left; eassumption).
      eapply H in H1. eassumption.
    + revert H0. fold (not (In a1 (s1 ++ a0 :: s2))).
      eapply IHs1.
      unfold not. intros. destruct H0.
      * assert (a0 = a1 \/ a = a1 \/ In a1 (s1 ++ s2)) by (left; eassumption).
        eapply H in H1. eassumption.
      * assert (a0 = a1 \/ a = a1 \/ In a1 (s1 ++ s2)) by (right; right; eassumption).
        eapply H in H1. eassumption.
  - destruct H0.
    + eapply IHs1 in H.
      rewrite H0 in H.
      assert (In a1 ((s1 ++ (a :: nil)) ++ a1 :: s2)).
      eapply in_elt.
      rewrite <- app_assoc in H1. simpl in H1.
      eapply H in H1. eassumption.
    + destruct H0.
      * assert (a = a1 \/ In a1 (s1 ++ a0 :: s2)) by (left; eassumption).
        eapply H in H1. eassumption.
      * eapply IHs1 in H.
        assert (In a1 ((s1 ++ (a :: a0 :: nil)) ++ s2)).
        eapply in_or_app.
        eapply in_app_or in H0.
        destruct H0.
        left. eapply in_or_app. left. eassumption.
        right. eassumption.
        rewrite <- app_assoc in H1. simpl in H1. eapply H in H1. eassumption.
Qed.

Lemma not_in_musical_chairs_app_backwards :
  forall (s1 s2: ListSet.set string) (a a0: string),
    ~ In a0 (s1 ++ a :: s2) ->
    ~ In a0 (a :: s1 ++ s2).
Proof.
  intros. eapply not_in_musical_chairs_app in H. eassumption.
Qed.

Lemma not_in_preserved_by_subset :
  forall (s: ListSet.set string) (a a': string),
    ~ (In a (a' :: s)) ->
    ~ (In a s).
Proof.
  unfold not; intros.
  assert (In a (a' :: s)) by (eapply in_cons; eassumption).
  eapply H in H1. eassumption.
Qed.

Lemma not_in_musical_chairs_app_2 :
  forall (s1 s2: ListSet.set string) (a a1 a2: string),
    ~ In a (a1 :: s1 ++ a2 :: s2) ->
    ~ In a (a2 :: s1 ++ a1 :: s2).
Proof.
  intros.
  rewrite app_comm_cons in H.
  eapply not_in_musical_chairs_app_backwards in H.
  assert (a <> a2).
  unfold not. intros. rewrite H0 in H.
  assert (In a2 (a2 :: (a1 :: s1) ++ s2)).
  econstructor. reflexivity.
  eapply H in H1. eassumption.
  unfold not. intros.
  invs H1.
  - assert (a = a) by reflexivity. eapply H0 in H2. eassumption.
  - eapply not_in_preserved_by_subset in H.
    rewrite <- app_comm_cons in H.
    eapply not_in_musical_chairs_app in H. eapply H in H2. eassumption.
Qed.



Lemma nodup_musical_chairs :
  forall (s1 s2: ListSet.set string) (a a0: string),
    NoDup (a :: s1 ++ a0 :: s2) -> NoDup (a0 :: s1 ++ a :: s2).
Proof.
  induction s1; intros; simpl in *.
  - invs H.
    invs H3.
    econstructor.
    eapply not_in_musical_chairs.
    eassumption.
    eassumption.
    assert (a :: a0 :: s2 = (a :: nil) ++ (a0 :: s2)) by ereflexivity.
    rewrite H0 in H. eapply NoDup_remove_1 in H. simpl in H. eassumption.
  - invs H. invs H3.
    econstructor.
    rewrite app_comm_cons in H. rewrite app_comm_cons in H.
    eapply NoDup_remove_2 in H.
    eapply not_in_musical_chairs_app in H.
    rewrite <- app_comm_cons in H. eassumption.
    eapply IHs1.
    Check NoDup_cons_iff.
    eapply NoDup_cons_iff in H.
    destruct H.
    eapply not_in_musical_chairs_app_2 in H.
    eapply IHs1 in H3.
    invs H3.
    eapply NoDup_cons_iff.
    split.
    + unfold not. intros.
      eapply not_in_musical_chairs_app_2 in H2. eapply not_in_preserved_by_subset in H2.
      eapply H2 in H1. eassumption.
    + eassumption.
Qed.

Lemma nodup_swap :
  forall (s: ListSet.set string)
    (a a': string),
    NoDup (a :: a' :: s) -> NoDup (a' :: a :: s).
Proof.
  intros.
  invs H. apply not_in_musical_chairs in H2; [ | assumption ].
  constructor.
  - assumption.
  - invs H.
    invs H5.
    apply not_in_preserved_by_subset in H4.
    constructor; assumption.
Qed.
    
    

Lemma nodup_switch :
  forall (s1 s2: ListSet.set string)
    (a: string),
    NoDup (s1 ++ a :: s2) <-> NoDup (a :: s1 ++ s2).
Proof.
  induction s1; intros; split; intros.
  - simpl.
    simpl in H. assumption.
  - simpl. simpl in H. assumption.
  - simpl in *.
    invs H.
    apply IHs1 in H3.
    apply not_in_musical_chairs_app_backwards in H2.
    assert (NoDup (a :: a0 :: s1 ++ s2)).
    {
      constructor; assumption.
    }
    apply nodup_swap in H0. assumption.
  - simpl in *.
    invs H.
    apply not_in_musical_chairs in H2; [ | assumption ].
    apply not_in_musical_chairs_app in H2.
    invs H.
    apply not_in_preserved_by_subset in H4. invs H5.
    assert (NoDup (a0 :: s1 ++ s2)) by (constructor; assumption).
    apply IHs1 in H0.
    constructor; assumption.
Qed.

Lemma set_add_append_not_in_first :
  forall (s1 s2: ListSet.set string)
    (a: string),
    ~ In a s1 ->
    ListSet.set_add string_dec a (s1 ++ s2) = s1 ++ (ListSet.set_add string_dec a s2).
Proof.
  induction s1; intros.
  - simpl. reflexivity.
  - simpl. pose proof (H1 := H). simpl in H. eapply Decidable.not_or in H.
    destruct H.
    destruct (string_dec a0 a) eqn:Eq.
    + clear Eq. symmetry in e. eapply H in e. invs e.
    + rewrite IHs1. reflexivity.
      assumption.
Qed.

Lemma set_union_is_append' :
  forall (s1 s2: ListSet.set string),
    Forall (fun (s: string) => ~ In s s1) s2 ->
    ListSet.set_union string_dec s1 s2 = s1 ++ (ListSet.set_union string_dec nil s2).
Proof.
  intros. induction H; intros.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHForall.
    rewrite set_add_append_not_in_first; [ | assumption ].
    reflexivity.
Qed.



Lemma set_union_is_append :
  forall (s1 s2: ListSet.set string),
    NoDup (s1 ++ s2) ->
    ListSet.set_union string_dec s1 s2 = s1 ++ (rev s2).
Proof.
  induction s1; intros.
  - simpl. rewrite nil_set_union_is_reverse. reflexivity. simpl in H. eassumption.
  - simpl in *.
    rewrite <- IHs1.
    + revert H. revert IHs1. induction s2; intros.
      * simpl. reflexivity.
      * simpl. rewrite no_dup_set_add_is_append.
        -- rewrite no_dup_set_add_is_append.
           ++ rewrite IHs2.
              ** reflexivity.
              ** eapply IHs1.
              ** rewrite app_comm_cons in H. eapply NoDup_remove_1 in H.
                 rewrite app_comm_cons. eassumption.
           ++ rewrite IHs1. rewrite app_comm_cons in H.
              
              pose proof (NODUP := H).
              eapply NoDup_remove_2 in H.
              
              assert (~(In a0 ((a :: s1) ++ rev s2))).
              unfold not. intros.
              eapply in_app_rev in H0. eapply H in H0. eassumption.
              rewrite <- app_comm_cons in H0.
              eapply not_in_preserved_by_subset in H0.

              rewrite <- app_comm_cons in NODUP.
              eapply nodup_musical_chairs in NODUP.
              rewrite app_comm_cons in NODUP.
              eapply NoDup_remove_1 in NODUP.
              eapply nodup_app_rev in NODUP.
              rewrite <- app_comm_cons in NODUP.
              eassumption.
              rewrite app_comm_cons in H.
              eapply NoDup_remove_1 in H.
              rewrite <- app_comm_cons in H.
              eapply nodup_switch in H.
              eapply NoDup_remove_1 in H. eassumption.
        -- rewrite IHs2.
           ++ rewrite IHs1.
              rewrite app_comm_cons in H.
              remember (a :: s1) as s1'.
              eapply nodup_switch in H.
              rewrite Heqs1' in H. rewrite app_comm_cons in H.
              eapply nodup_app_rev in H. rewrite <- app_comm_cons in H. rewrite <- app_comm_cons in H. eassumption.
              eapply nodup_switch in H.
              eapply NoDup_remove_1 in H. eapply NoDup_remove_1 in H. eassumption.
           ++ eapply IHs1.
           ++ rewrite app_comm_cons in H. eapply NoDup_remove_1 in H. rewrite <- app_comm_cons in H. eassumption.
    + eapply nodup_switch in H. eapply NoDup_remove_1 in H. eassumption.
Qed.

Lemma not_in_append :
  forall (s1 s2: ListSet.set string) (a: string),
    ~ In a s1 ->
    ~ In a s2 ->
    ~ In a (s1 ++ s2).
Proof.
  induction s1; intros.
  - simpl in *. eassumption.
  - simpl in *. unfold not. intros.
    destruct H1.
    + assert (a = a0 \/ In a0 s1) by (left; assumption).
      apply H in H2. assumption.
    + eapply in_app_or in H1.
      destruct H1.
      * assert (a = a0 \/ In a0 s1) by (right; assumption).
        apply H in H2. assumption.
      * apply H0 in H1. assumption.
Qed.

Lemma not_in_append_subset :
  forall (s1 s2: ListSet.set string) (a: string),
    ~ In a (s1 ++ s2) ->
    ~ In a s1 /\ ~ In a s2.
Proof.
  induction s1; intros.
  - simpl in *. split. unfold not. intros. assumption.
    assumption.
  - simpl in H. simpl.
    eapply Decidable.not_or in H. destruct H.
    split.
    + unfold not. intros.
      destruct H1.
      * eapply H in H1. assumption.
      * apply IHs1 in H0. destruct H0. apply H0 in H1. assumption.
    + apply IHs1 in H0. destruct H0. assumption.
Qed.

Lemma nodup_transitive_sorta :
  forall (a b c: ListSet.set string),
    NoDup (a ++ b) ->
    NoDup (b ++ c) ->
    NoDup (a ++ c) ->
    NoDup (a ++ b ++ c).
Proof.
  induction a; intros.
  - simpl in *. eassumption.
  - simpl in *. invs H. invs H1.
    eapply NoDup_cons_iff.
    apply not_in_append_subset in H6.
    destruct H6.
    apply not_in_append with (s2 := c) in H4; [ | assumption ].
    rewrite <- app_assoc in H4.
    apply IHa with (b := b) (c := c) in H5; [ | assumption .. ].
    split; assumption.
Qed.



Lemma nodup_free_vars_aexp :
  forall (aexp: aexp_Dan),
    NoDup (free_vars_aexp_src aexp).
Proof.
  induction aexp using aexp_Dan_ind2.
  - simpl. econstructor.
  - simpl. econstructor.
    unfold not; intros. invs H. econstructor.
  - simpl. econstructor.
  - simpl. eapply ListSet.set_union_nodup; eassumption.
  - simpl. eapply ListSet.set_union_nodup; eassumption.
  - induction H.
    + simpl. econstructor.
    + simpl.  simpl in IHForall. revert IHForall. revert H0. revert H.
      revert x.
      induction l; intros.
      * simpl. eapply ListSet.set_union_nodup.
        econstructor. eassumption.
      * simpl. rewrite nil_set_union_is_reverse; [ | eassumption ].
        invs H0. simpl in IHForall.
        eapply nodup_preserved_by_reverse in H.
        eapply set_union_no_dups with (s2 := (free_vars_aexp_src a)) in H.
        eapply nodup_fold_left. assumption.
Qed.

Lemma var_map_wf_app_dan_first_and_rest_backward :
  forall (a: aexp_Dan) (f: ident) (aexp: aexp_Dan) (aexps: list aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents aexp /\ var_map_wf_wrt_aexp idents (APP_Dan f aexps) ->
    var_map_wf_wrt_aexp idents (APP_Dan f (aexp :: aexps)).
Proof.
  intros.
  destruct H as (WFaexp & WFaexps).
  unfold_wf_aexp_in WFaexp; unfold_wf_aexp_in WFaexps.
  unfold_wf_aexp; [ eapply WF | clear WF; destruct WF0 as (NODUPS & _); intros .. ].
  - simpl in H. rewrite H in H0. eapply in_fold_left_iff in H0.
    destruct H0.
    + eapply A0. ereflexivity. simpl. eassumption.
    + eapply A. ereflexivity.
      rewrite nil_set_union_is_reverse in H0.
      eapply in_preserved_by_reverse in H0. eassumption.
      eapply nodup_free_vars_aexp.
      
  - eapply free_vars_in_aexp_has_variable; eauto.
  - eapply find_index_rel_in. eassumption. assumption.
    intros.
    + rewrite H in H1. simpl in H1. apply in_fold_left_iff in H1.
      destruct H1.
      * eapply A0. ereflexivity. assumption.
      * eapply A. ereflexivity. rewrite nil_set_union_is_reverse in H1.
        apply in_rev in H1. assumption.
        apply nodup_free_vars_aexp.
    + assumption.
  - inversion H. eapply has_args_app_case; eauto.
Qed.
  
Lemma var_map_wf_app_dan_args_first :
  forall (f: ident) (x: aexp_Dan) (l: list aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents (APP_Dan f (x :: l)) ->
    var_map_wf_wrt_aexp idents x.
Proof.
  pose proof var_map_wf_app_dan_args_all.
  intros. 
  pose proof (H (x::l) f idents H0). invs H1. apply H4.    
Qed. 

Lemma var_map_wf_app_dan_args_rest :
  forall (f: ident) (x: aexp_Dan) (l: list aexp_Dan) (idents: list ident),
    var_map_wf_wrt_aexp idents (APP_Dan f (x :: l)) ->
    var_map_wf_wrt_aexp idents (APP_Dan f l).
Proof.
  pose proof var_map_wf_app_dan_rest.
  intros.
  pose proof (H (APP_Dan f (x :: l)) f x l idents eq_refl H0). apply H1. 
Qed. 


                        


Ltac solve_var_map_wf :=
  match goal with
  | [ |- var_map_wf_wrt_aexp ?idents ?a ] =>
      match goal with
      | [ H: var_map_wf_wrt_aexp ?idents' (?dan_op a ?a') |- _ ] =>
          eapply var_map_wf_plus_minus_dan_left;
          idtac;
          idtac;
          match goal with
          | [ |- (?a3 = PLUS_Dan a ?a') \/ (?a3 = MINUS_Dan a ?a') ] =>
              match dan_op with
              | PLUS_Dan => left
              | MINUS_Dan => right
              end;
              ereflexivity
          | [ |- var_map_wf_wrt_aexp idents ?a3 ] =>
              eapply H
          | _ =>
              idtac
          end
      | [ H: var_map_wf_wrt_aexp ?idents' (APP_Dan ?f (a :: ?aexps)) |- _ ] =>
          eapply var_map_wf_app_dan_first; try ereflexivity; try eassumption
      | [ H : var_map_wf_wrt_aexp ?idents' (APP_Dan ?f (?aexp :: ?aexps)) |- _ ] =>
          match a with
          | APP_Dan f aexps =>
              eapply var_map_wf_app_dan_rest; try ereflexivity; try eassumption
          end
      | [ H: var_map_wf_wrt_aexp ?idents' (?dan_op ?a' a) |- _ ] =>
          eapply var_map_wf_plus_minus_dan_right;
          idtac;
          idtac;
          match goal with
          | [ |- (?a3 = PLUS_Dan ?a' a) \/ (?a3 = MINUS_Dan ?a' a) ] =>
              match dan_op with
              | PLUS_Dan => left
              | MINUS_Dan => right
              end;
              ereflexivity
          | [ |- var_map_wf_wrt_aexp idents ?a3 ] =>
              eapply H
          | _ =>
              idtac
          end
      | [ H: var_map_wf_wrt_bexp ?idents' (LEQ_Dan a ?a') |- _ ] =>
          eapply var_map_wf_leq_dan_left; try ereflexivity; try eassumption;
          idtac;
          idtac
      | [ H: var_map_wf_wrt_bexp ?idents' (LEQ_Dan ?a' a) |- _ ] =>
          eapply var_map_wf_leq_dan_right; try ereflexivity; try eassumption
          ;
          idtac;
          idtac
      | _ =>
          idtac
      end
  | [ |- var_map_wf_wrt_bexp ?idents ?a ] =>
      match goal with
      | [ H: var_map_wf_wrt_bexp ?idents' (?dan_op a ?a') |- _ ] =>
          match dan_op with
          | LEQ_Dan =>
              eapply var_map_wf_leq_dan_left; try ereflexivity;
              match goal with
              | [ |- var_map_wf_wrt_bexp idents ?a3 ] =>
                  eapply H
              end
          | _ =>
              eapply var_map_wf_and_or_dan_left;
              idtac;
              idtac;
              match goal with
              | [ |- (?a3 = AND_Dan a ?a') \/ (?a3 = OR_Dan a ?a') ] =>
                  match dan_op with
                  | AND_Dan => left
                  | OR_Dan => right
                  end;
                  ereflexivity
              | [ |- var_map_wf_wrt_bexp idents ?a3 ] =>
                  eapply H
              | _ =>
                  idtac
              end
          end
      | [ H: var_map_wf_wrt_bexp ?idents' (NEG_Dan a) |- _ ] =>
          eapply var_map_wf_neg_dan; try ereflexivity; try eassumption
      | [ H: var_map_wf_wrt_bexp ?idents' (?dan_op ?a' a) |- _ ] =>
          eapply var_map_wf_and_or_dan_right;
          idtac;
          idtac;
          match goal with
          | [ |- (?a3 = AND_Dan ?a' a) \/ (?a3 = OR_Dan ?a' a) ] =>
              match dan_op with
              | AND_Dan => left
              | OR_Dan => right
              end;
              ereflexivity
          | [ |- var_map_wf_wrt_bexp idents ?a3 ] =>
              eapply H
          | _ =>
              idtac
          end
      end
  end.

Lemma fold_left_containment_stronger :
  forall (ident_set: ListSet.set ident) (x0: ident) (other: list ident),
    In x0 (ListSet.set_fold_left (fun (acc : list string) (x : string) => x :: acc) ident_set (other)) <->
    (In x0 other) \/ (In x0 (ListSet.set_fold_left (fun (acc : list string) (x : string) => x :: acc) ident_set nil)).
Proof.
  induction ident_set; intros x0 other; split; intros IN.
  - simpl in IN. left. assumption.
  - simpl in IN. simpl. destruct IN. assumption. invs H.
  - simpl in IN. eapply IHident_set in IN.
    simpl.
    destruct IN.
    + invs H.
      * right. eapply IHident_set.
        left. econstructor. reflexivity.
      * left. assumption.
    + right. eapply IHident_set. right. assumption.
  - simpl in IN. simpl. destruct IN.
    + eapply IHident_set. left. eapply in_cons. assumption.
    + eapply IHident_set in H. destruct H.
      * invs H.
        -- eapply IHident_set. left. econstructor. reflexivity.
        -- invs H0.
      * eapply IHident_set. right. assumption.
Qed.

Lemma fold_left_containment_helper :
  forall (ident_set: ListSet.set ident) (x0: ident),
    In x0 (ListSet.set_fold_left (fun (acc : list string) (x : string) => x :: acc) ident_set nil) <->
    In x0 ident_set.
Proof.
  induction ident_set; intros x0; split; intros IN.
  - invs IN.
  - invs IN.
  - simpl in IN. eapply fold_left_containment_stronger in IN.
    destruct IN.
    + econstructor. invs H. reflexivity. invs H0.
    + eapply in_cons. eapply IHident_set. assumption.
  - invs IN; simpl.
    + eapply fold_left_containment_stronger.
      * left. econstructor. reflexivity.
    + eapply fold_left_containment_stronger. right. eapply IHident_set. assumption.
Qed.

Lemma fold_left_cons_acc_preserves_containment :
  forall (ident_set: ListSet.set ident) (idents: list ident) (x0: ident),
    In x0 idents ->
    idents = ListSet.set_fold_left (fun (acc : list string) (x : string) => x :: acc) ident_set nil ->
    In x0 ident_set.
Proof.
  induction ident_set; intros.
  - simpl in H0. subst. invs H.
  - simpl in H0. rewrite H0 in H. eapply fold_left_containment_stronger in H.
    destruct H.
    + econstructor. invs H. reflexivity. invs H1.
    + eapply in_cons. eapply fold_left_containment_helper. eassumption.
Qed.




Lemma var_map_wf_var_dan :
  forall (x: ident) (idents: list ident),
    In x idents ->
    NoDup idents ->
    var_map_wf_wrt_aexp idents (VAR_Dan x).
Proof.
  intros.
  unfold_wf_aexp.
  - split; [ | split ; [ | split ]].
    + assumption.
    + intros. split; intros.
      * eapply find_index_rel_implication. assumption.
      * eapply find_index_rel_help; eassumption.
    + intros.
      eapply find_index_rel_in_stronger in H1. destruct H1.
      eapply find_index_rel_implication in H1.
      exists x1. assumption.
      assumption.
    + intros.
      unfold construct_trans in H2.
      rewrite H2 in H1. clear H2.
      eapply fold_left_cons_acc_preserves_containment in H1; [ | ereflexivity ].
      eapply free_vars_in_imp_has_variable; eauto.
  - intros. simpl in H1. subst. invs H2.
    + eassumption.
    + invs H1.
  - intros. simpl in H1. subst. invs H2.
    + econstructor.
      eapply String.eqb_eq. reflexivity.
    + invs H1.
  - intros. invs H1. simpl in H2. destruct H2.
    + subst.
      eapply find_index_rel_in_stronger; eassumption.
    + invs H1.
  - intros.
    simpl in H2. subst. invs H3.
    + invs H1.
    + invs H2.
Qed.




  
  



Lemma nodup_idents_means_maps_are_same :
  forall (idents: list ident) (x: ident) nenv (n: nat),
    NoDup (x :: idents) ->
    map
      (fun y : DanTrickLanguage.ident =>
         if string_dec x y then n else nenv y) idents = 
      map nenv idents.
Proof.
  induction idents; intros.
  - reflexivity.
  - invs H. simpl.
    assert (x <> a).
    {
      unfold not. intros.
      rewrite H0 in H2.
      assert (In a (a :: idents)) by (constructor; reflexivity).
      apply H2 in H1. assumption.
    }
    destruct (string_dec x a) eqn:?; [ congruence | ].
    f_equal. apply IHidents. eapply nodup_swap in H.
    invs H. assumption.
Qed.
