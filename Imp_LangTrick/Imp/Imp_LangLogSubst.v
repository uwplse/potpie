From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.
(* Add LoadPath "./" as Imp_LangTrick. *)
From Imp_LangTrick Require Import Imp.Imp_LangTrickLanguage LogicProp Imp.Imp_LangLogicHelpers Imp.Imp_LangLogProp.

Scheme a_Imp_Lang_mut := Induction for a_Imp_Lang Sort Prop
    with args_Imp_Lang_mut := Induction for args_Imp_Lang Sort Prop.
  
Combined Scheme a_syntactic_ind from a_Imp_Lang_mut, args_Imp_Lang_mut.

Check a_syntactic_ind. 

Definition subst_Imp_Lang_lp substout substin (prop : Imp_Lang_lp) := 
  match prop with
  |Imp_Lang_lp_arith l => 
    Imp_Lang_lp_arith (transform_prop_exprs l (fun a => imp_lang_aexp_update substout substin a))
  |Imp_Lang_lp_bool l => 
    Imp_Lang_lp_bool (transform_prop_exprs l (fun b => imp_lang_bexp_update substout substin b))
    end.

Fixpoint subst_AbsEnv substout substin log :=
  match log with
  | AbsEnvLP l => 
    AbsEnvLP
    (subst_Imp_Lang_lp substout substin l)
  | AbsEnvAnd l1 l2 => 
    AbsEnvAnd 
    (subst_AbsEnv substout substin l1)
    (subst_AbsEnv substout substin l2)
  | AbsEnvOr l1 l2 => 
    AbsEnvOr 
    (subst_AbsEnv substout substin l1)
    (subst_AbsEnv substout substin l2)
  end
.

Inductive subst_Imp_Lang_lp_rel : ident -> aexp_Imp_Lang -> Imp_Lang_lp -> Imp_Lang_lp -> Prop :=
| SubstImp_LangArith :
  forall x a l l',
    transformed_prop_exprs (fun aexp aexp' => imp_lang_aexp_update_rel x a aexp aexp') l l' ->
    subst_Imp_Lang_lp_rel x a (Imp_Lang_lp_arith l) (Imp_Lang_lp_arith l')
| SubstImp_LangBool :
  forall x a l l',
    transformed_prop_exprs (fun bexp bexp' => imp_lang_bexp_update_rel x a bexp bexp') l l' ->
    subst_Imp_Lang_lp_rel x a (Imp_Lang_lp_bool l) (Imp_Lang_lp_bool l').

Inductive subst_AbsEnv_rel : ident -> aexp_Imp_Lang -> AbsEnv -> AbsEnv -> Prop :=
| SubstImp_LangLpLog :
  forall x a l l',
    subst_Imp_Lang_lp_rel x a l l' ->
    subst_AbsEnv_rel x a (AbsEnvLP l) (AbsEnvLP l')
| SubstImp_LangAndLog :
  forall x a l1 l2 l1' l2',
    subst_AbsEnv_rel x a l1 l1' ->
    subst_AbsEnv_rel x a l2 l2' ->
    subst_AbsEnv_rel x a (AbsEnvAnd l1 l2) (AbsEnvAnd l1' l2')
| SubstImp_LangOrLog :
  forall x a l1 l2 l1' l2',
    subst_AbsEnv_rel x a l1 l1' ->
    subst_AbsEnv_rel x a l2 l2' ->
    subst_AbsEnv_rel x a (AbsEnvOr l1 l2) (AbsEnvOr l1' l2').

  Lemma update_imp_lang_update_equiv_forward: 
  (forall potato dbenv fenv nenv n' ,
  a_Imp_Lang potato dbenv fenv nenv n' -> 
  forall substin substin_n substout aexp, 
  (potato = (imp_lang_aexp_update substout substin aexp)) -> 
  a_Imp_Lang substin dbenv fenv nenv substin_n ->
  a_Imp_Lang aexp dbenv fenv (update substout substin_n nenv) n')
  /\
  (forall substargs dbenv fenv nenv new_ns,
  args_Imp_Lang substargs dbenv fenv nenv new_ns -> 
  forall substout substin args n, 
  a_Imp_Lang substin dbenv fenv nenv n ->
  substargs = (List.map (fun x => imp_lang_aexp_update substout substin x) args) ->
  (args_Imp_Lang (List.map (fun x => imp_lang_aexp_update substout substin x) args) dbenv fenv nenv new_ns ->
      args_Imp_Lang args dbenv fenv (update substout n nenv) new_ns))
  .
  Proof. 
    pose (fun potato dbenv fenv nenv n' =>
    fun H:(a_Imp_Lang potato dbenv fenv nenv n') => 
    forall substin substin_n substout aexp, 
    (potato = (imp_lang_aexp_update substout substin aexp)) -> 
    a_Imp_Lang substin dbenv fenv nenv substin_n ->
    a_Imp_Lang aexp dbenv fenv (update substout substin_n nenv) n')
    as P.
    pose (fun substargs dbenv fenv nenv new_ns => 
    fun H:(args_Imp_Lang substargs dbenv fenv nenv new_ns) => 
    forall substout substin args n, 
    a_Imp_Lang substin dbenv fenv nenv n ->
    substargs = (List.map (fun x => imp_lang_aexp_update substout substin x) args) ->
    (args_Imp_Lang (List.map (fun x => imp_lang_aexp_update substout substin x) args) dbenv fenv nenv new_ns ->
    args_Imp_Lang args dbenv fenv (update substout n nenv) new_ns)) as P'.
    apply (a_syntactic_ind P P'). 
    - unfold P. intros. induction aexp; try (inversion H). 
      + inversion H. apply Imp_Lang_const.
      + inversion H. destruct ((x =? substout)%string) eqn:eq in H2.
        --unfold update. inversion H. apply Imp_Lang_var. destruct (string_dec substout x).
          ++subst. inversion H0. auto.
          ++destruct n0. pose proof (eqb_eq x substout) as H1; destruct H1;
          pose proof (H1 eq). auto.
        --discriminate.
    - unfold P. intros. induction aexp; try (inversion H).
      unfold update. destruct ((x0 =? substout)%string) eqn:eq in H2.
      + unfold imp_lang_aexp_update in H. subst. apply Imp_Lang_var. 
        destruct (string_dec substout x0).
        --inversion H0. auto.
        --destruct n. pose proof (eqb_eq x0 substout) as H1; destruct H1;
        pose proof (H1 eq). auto.
      + subst. inversion H2. apply Imp_Lang_var. destruct (string_dec substout x0).
        --subst. pose proof (eqb_neq x0 x0) as H3; destruct H3; pose proof (H1 eq).
          destruct H4. auto.
        --auto.
    - unfold P. intros. induction aexp; try (inversion H).
      + apply Imp_Lang_var. unfold update. destruct (string_dec substout x); 
      destruct ((x =? substout)%string) eqn:eq in H2.
        --subst. inversion H0. subst. rewrite e in H3. inversion H3. auto.
        --pose proof (eqb_neq x substout).
          destruct H1. pose proof (H1 eq). destruct H4. auto.   
        --destruct n0. pose proof (eqb_eq x substout). destruct H1.
          pose proof (H1 eq). auto.     
        --inversion H2.
      + apply Imp_Lang_param. rewrite H2 in a. auto. rewrite <- H2. auto.
    - unfold P. intros. induction aexp; unfold imp_lang_aexp_update in H1; try (inversion H1).
      + apply Imp_Lang_var. unfold update. destruct (string_dec substout x) eqn:eq.
        --destruct ((x =? substout)%string) eqn:eq2 in H4.
          ++subst. inversion H2. subst. 
            pose proof (a_Imp_Lang_deterministic dbenv fenv nenv a1 n1 n0 a H5).
            pose proof (a_Imp_Lang_deterministic dbenv fenv nenv a2 n2 n3 a0 H10). 
            subst. auto.
          ++pose proof (eqb_neq x substout).
            destruct H3. pose proof (H3 eq2). destruct H6. auto.   
        --destruct ((x =? substout)%string) eqn:eq2 in H4.
          ++pose proof (eqb_eq x substout). 
            destruct H3. pose proof (H3 eq2). destruct n. auto.  
          ++discriminate.
      + pose proof (H substin substin_n substout aexp1 H4 H2).
        pose proof (H0 substin substin_n substout aexp2 H5 H2). apply Imp_Lang_plus; assumption.
    - unfold P. intros. induction aexp; unfold imp_lang_aexp_update in H1; try (inversion H1).
      + apply Imp_Lang_var. unfold update. destruct (string_dec substout x) eqn:eq.
        --destruct ((x =? substout)%string) eqn:eq2 in H4.
          ++subst. inversion H2. subst. 
            pose proof (a_Imp_Lang_deterministic dbenv fenv nenv a1 n1 n0 a H5).
            pose proof (a_Imp_Lang_deterministic dbenv fenv nenv a2 n2 n3 a0 H10). 
            subst. auto.
          ++pose proof (eqb_neq x substout).
            destruct H3. pose proof (H3 eq2). destruct H6. auto.   
        --destruct ((x =? substout)%string) eqn:eq2 in H4.
          ++pose proof (eqb_eq x substout). 
            destruct H3. pose proof (H3 eq2). destruct n. auto. 
          ++discriminate.
      + pose proof (H substin substin_n substout aexp1 H4 H2).
        pose proof (H0 substin substin_n substout aexp2 H5 H2). apply Imp_Lang_minus; assumption.
    - unfold P, P'. induction aexp; intros; unfold imp_lang_aexp_update in H0; inversion H0.
      + destruct ((x =? substout)%string) eqn:eq in H0.
        --apply Imp_Lang_var. unfold update. destruct (string_dec substout x).
          ++subst.  
            inversion H1. subst.
            pose proof (args_Imp_Lang_deterministic dbenv fenv nenv aexps ns ns0 a H6).
            subst.   
            pose proof (i_Imp_Lang_deterministic ns0 fenv init_nenv (Body (fenv f)) nenv'' nenv''0 i H7).
            subst. auto.
          ++pose proof (eqb_eq x substout).
            destruct H2. pose proof (H2 eq). destruct n. auto.   
        --discriminate.
      + unfold update. rewrite <- H3 in *. 
        pose proof (H substout substin aexps0 substin_n H1 H4).
        rewrite H4 in a.  pose proof (H2 a).
        eapply Imp_Lang_app. pose proof (fenv f). exists. rewrite <- e in *.
        rewrite -> e0 in *. rewrite H4. rewrite map_length. apply eq_refl.   
        inversion H5. subst. auto. apply args_cons. auto. auto.
        rewrite <- e in i. apply i. rewrite <- e in e1.  assumption.
    - unfold P'. intros. 
      + intros. induction args. apply args_nil. inversion H0.
    - unfold P, P'. intros. 
      + intros. induction args; try discriminate.  
        pose proof (H0 substout substin args n H1) as H4. apply args_cons.
        --pose proof (H substin n substout a1) as H5. unfold map in H2.
          inversion H2. apply (H5 H7 H1). 
        --inversion H2. pose proof (H4 H7). apply H5. subst. assumption.
Qed.    


Lemma update_imp_lang_update_equiv_backwards:
  forall aexp dbenv fenv up_nenv n', 
    a_Imp_Lang aexp dbenv fenv up_nenv n' -> 
    forall substin substin_n substout nenv, 
    (up_nenv = (update substout substin_n nenv)) -> 
    a_Imp_Lang substin dbenv fenv nenv substin_n ->
    a_Imp_Lang (imp_lang_aexp_update substout substin aexp) dbenv fenv nenv n'.
  Proof.
    pose (fun potato dbenv fenv up_nenv n' =>
    fun H:(a_Imp_Lang potato dbenv fenv up_nenv n') => 
    forall substin substin_n substout nenv, 
    (up_nenv = (update substout substin_n nenv)) -> 
    a_Imp_Lang substin dbenv fenv nenv substin_n ->
    a_Imp_Lang (imp_lang_aexp_update substout substin potato) dbenv fenv nenv n')
    as P.
    pose (fun substargs dbenv fenv up_nenv new_ns => 
    fun H:(args_Imp_Lang substargs dbenv fenv up_nenv new_ns) => 
    forall substout substin n nenv, 
    a_Imp_Lang substin dbenv fenv nenv n ->
    up_nenv = (update substout n nenv) ->
    args_Imp_Lang substargs dbenv fenv up_nenv new_ns -> 
    (args_Imp_Lang (List.map (fun x => imp_lang_aexp_update substout substin x) substargs) dbenv fenv nenv new_ns)) as P'.
    apply (a_syntactic_ind P P').
    - unfold P. intros. unfold imp_lang_aexp_update. apply Imp_Lang_const.
    - unfold P. intros. unfold imp_lang_aexp_update. 
      destruct ((x =? substout)%string) eqn:eq.
      + unfold update in H. subst. destruct (string_dec substout x).
        --assumption.
        --destruct n. pose proof (eqb_eq x substout).
          destruct H. pose proof (H eq). auto.
      + unfold update in H. subst. destruct (string_dec substout x).
        --pose proof (eqb_neq x substout). destruct H.
          pose proof (H eq). destruct H2. auto.
        --apply Imp_Lang_var. auto.
    - unfold P. intros. subst. unfold imp_lang_aexp_update. 
      apply Imp_Lang_param; assumption.
    - unfold P. intros. subst. unfold imp_lang_aexp_update.
      pose proof (H substin substin_n substout nenv0).
      pose proof (H0 substin substin_n substout nenv0).
      apply Imp_Lang_plus.
      + apply H1; auto.
      + apply H3; auto.
    - unfold P. intros. subst. unfold imp_lang_aexp_update.
      pose proof (H substin substin_n substout nenv0).
      pose proof (H0 substin substin_n substout nenv0).
      apply Imp_Lang_minus.
      + apply H1; auto.
      + apply H3; auto.
    - unfold P, P'. intros. subst. unfold imp_lang_aexp_update.
      pose proof (H substout substin substin_n nenv0 H1).
      eapply Imp_Lang_app.
      + pose proof (fenv f). exists.
      + rewrite e0. rewrite map_length. apply eq_refl.  
      + apply H0; auto.
      + apply i.
      + auto.
    - unfold P'. intros. apply args_nil.
    - unfold P, P'. intros. apply args_cons.
      + inversion H3. subst. apply (H substin n substout nenv0); auto.
      + eapply H0. apply H1. apply H2. inversion H3. auto.
    Qed.                     

Lemma update_imp_lang_update_equiv : 
        (forall substin dbenv fenv nenv substin_n,
            a_Imp_Lang substin dbenv fenv nenv substin_n ->
            forall n' substout aexp,
            (a_Imp_Lang (imp_lang_aexp_update substout substin aexp) dbenv fenv nenv n' <-> 
                a_Imp_Lang aexp dbenv fenv (update substout substin_n nenv) n')).
  Proof.
    intros; split.
    - pose proof update_imp_lang_update_equiv_forward. intros.
      destruct H0. 
      pose proof (H0 (imp_lang_aexp_update substout substin aexp) dbenv fenv nenv n' H1 substin substin_n substout aexp).
      apply H3. auto. auto.
    - pose proof update_imp_lang_update_equiv_backwards. intros.
      pose proof (H0 aexp dbenv fenv (update substout substin_n nenv) n' H1 substin substin_n substout nenv). 
      apply H2; auto.    
  Qed.    

Lemma update_imp_lang_update_equiv_bexp : 
(forall substin dbenv fenv nenv substin_n,
    a_Imp_Lang substin dbenv fenv nenv substin_n ->
    forall bexp val substout,
    (b_Imp_Lang (imp_lang_bexp_update substout substin bexp) dbenv fenv nenv val <-> 
    b_Imp_Lang bexp dbenv fenv (update substout substin_n nenv) val)).
Proof. 
  induction bexp; split.
  - intros. inversion H0. apply Imp_Lang_true.
  - intros. inversion H0. subst. unfold imp_lang_bexp_update.  
    apply Imp_Lang_true.
  - intros. inversion H0. apply Imp_Lang_false.  
  - intros. inversion H0. subst. unfold imp_lang_bexp_update.
    apply Imp_Lang_false.  
  - intros. inversion H0. subst. apply Imp_Lang_neg. apply IHbexp. auto.
  - intros. inversion H0. subst. cbn. 
    apply Imp_Lang_neg. apply IHbexp. auto. 
  - intros. inversion H0. subst. apply Imp_Lang_and.
    + apply IHbexp1. auto.
    + apply IHbexp2. auto.
  - intros. inversion H0. subst. cbn. apply Imp_Lang_and.
    + apply IHbexp1. auto.  
    + apply IHbexp2. auto.
  - intros. inversion H0. subst. apply Imp_Lang_or.
    + apply IHbexp1. auto.
    + apply IHbexp2. auto.
  - intros. inversion H0. subst. cbn. apply Imp_Lang_or.
    + apply IHbexp1. auto.
    + apply IHbexp2. auto.
  - intros. inversion H0. subst. 
    pose proof (update_imp_lang_update_equiv substin dbenv fenv nenv substin_n H). 
    apply Imp_Lang_leq.
    + apply H1. auto.
    + apply H1. auto.
  - intros. inversion H0. subst. cbn. 
    pose proof (update_imp_lang_update_equiv substin dbenv fenv nenv substin_n H).
    apply Imp_Lang_leq.
    + apply H1. auto.  
    + apply H1. auto.
  Qed. 




Scheme prop_args_ind := Induction for eval_prop_args_rel Sort Prop.
Check prop_args_ind. 

Lemma aupdate_subst_args_equiv :
forall rel newargs ns, 
eval_prop_args_rel rel newargs ns -> 
forall dbenv nenv fenv aexp n args x, 
rel = (fun a v => a_Imp_Lang a dbenv fenv nenv v) -> 
newargs = (map (fun a : aexp_Imp_Lang => imp_lang_aexp_update x aexp a)
args) -> 
a_Imp_Lang aexp dbenv fenv nenv n -> 
eval_prop_args_rel (fun a v => a_Imp_Lang a dbenv fenv (update x n nenv) v) args ns. 
Proof.
  pose (fun rel newargs ns => 
        fun H: (eval_prop_args_rel rel newargs ns) => 
        forall dbenv nenv fenv aexp n args x, 
        rel = (fun a v => a_Imp_Lang a dbenv fenv nenv v) -> 
        newargs = (map (fun a : aexp_Imp_Lang => imp_lang_aexp_update x aexp a)
        args) -> 
        a_Imp_Lang aexp dbenv fenv nenv n -> 
        eval_prop_args_rel (fun a v => a_Imp_Lang a dbenv fenv (update x n nenv) v) args ns)
        as P. 
  apply (prop_args_ind nat aexp_Imp_Lang P).
  - unfold P. intros. 
    symmetry in H0. 
    pose proof (map_eq_nil (fun a : aexp_Imp_Lang => imp_lang_aexp_update x aexp a) args H0).
    subst. apply RelArgsNil.

  - unfold P. intros.
    pose proof (map_eq_cons (fun a : aexp_Imp_Lang => imp_lang_aexp_update x aexp a) args0).
    symmetry in H1. 
    pose proof (H3 args arg H1). destruct H4; destruct H4; destruct H4; destruct H5.
    rewrite H4. apply RelArgsCons. 
      + subst. 
        pose proof (update_imp_lang_update_equiv aexp dbenv fenv nenv n H2 val x x0).
        destruct H0. apply H0. auto.   
      + symmetry in H6. 
        pose proof (H dbenv nenv fenv aexp n x1 x). 
        apply H7; auto.  
Qed. 

Lemma aupdate_subst_args_equiv_bexp :
forall rel newargs ns, 
eval_prop_args_rel rel newargs ns -> 
forall dbenv nenv fenv aexp n args x, 
rel = (fun a v => b_Imp_Lang a dbenv fenv nenv v) -> 
newargs = (map (fun a : bexp_Imp_Lang => imp_lang_bexp_update x aexp a)
args) -> 
a_Imp_Lang aexp dbenv fenv nenv n -> 
eval_prop_args_rel (fun a v => b_Imp_Lang a dbenv fenv (update x n nenv) v) args ns. 
Proof.
  pose (fun rel newargs ns => 
  fun H: (eval_prop_args_rel rel newargs ns) => 
  forall dbenv nenv fenv aexp n args x, 
  rel = (fun a v => b_Imp_Lang a dbenv fenv nenv v) -> 
  newargs = (map (fun a : bexp_Imp_Lang => imp_lang_bexp_update x aexp a)
  args) -> 
  a_Imp_Lang aexp dbenv fenv nenv n -> 
  eval_prop_args_rel (fun a v => b_Imp_Lang a dbenv fenv (update x n nenv) v) args ns)
  as P.
  apply (prop_args_ind bool bexp_Imp_Lang P).
  - unfold P. intros. 
    symmetry in H0. 
    pose proof (map_eq_nil (fun a : bexp_Imp_Lang => imp_lang_bexp_update x aexp a) args H0).
    subst. apply RelArgsNil.
  - unfold P. intros.
    pose proof (map_eq_cons (fun a : bexp_Imp_Lang => imp_lang_bexp_update x aexp a) args0).
    symmetry in H1. 
    pose proof (H3 args arg H1). destruct H4; destruct H4; destruct H4; destruct H5.
    rewrite H4. apply RelArgsCons. 
      + subst. 
        pose proof (update_imp_lang_update_equiv_bexp aexp dbenv fenv nenv n H2 x0 val x). 
        destruct H0. apply H0. auto.   
      + symmetry in H6. 
        pose proof (H dbenv nenv fenv aexp n x1 x). 
        apply H7; auto.  
  Qed. 

Lemma aupdate_subst_equiv_aexp_TrueProp (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)) fenv dbenv
             (update x n0 nenv).

Proof.
  apply Imp_Lang_lp_rel_arith. apply RelTrueProp.
Qed.

Lemma aupdate_subst_equiv_aexp_FalseProp (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (FalseProp nat aexp_Imp_Lang)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (FalseProp nat aexp_Imp_Lang)) fenv dbenv
             (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst. inversion H3. subst.
  inversion H4.
Qed.

Lemma aupdate_subst_equiv_aexp_UnaryProp (f : nat -> Prop)
      (a : aexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (UnaryProp nat aexp_Imp_Lang f a)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (UnaryProp nat aexp_Imp_Lang f a)) fenv dbenv
             (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv aexp dbenv fenv nenv n0 H1 v x a).
  destruct H2.
  pose proof (H2 H7).
  eapply RelUnaryProp.
  - apply H6.
  - apply H8.
Qed.


Lemma aupdate_subst_equiv_aexp_BinaryProp (f : nat -> nat -> Prop)
      (a1 a2 : aexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (BinaryProp nat aexp_Imp_Lang f a1 a2))))
              fenv dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (BinaryProp nat aexp_Imp_Lang f a1 a2)) fenv dbenv
             (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv aexp dbenv fenv nenv n0 H1).
  eapply RelBinaryProp.
  - pose proof (H2 v1 x a1). apply H5. auto.
  - pose proof (H2 v2 x a2). apply H5. auto.
  - auto.
Qed.

Lemma aupdate_subst_equiv_aexp_AndProp (l1 l2 : LogicProp nat aexp_Imp_Lang)
      (fenv : fun_env)
      (IHl1 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_arith l1)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_arith l1)) fenv) dbenv nenv)
      (IHl2 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_arith l2)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_arith l2)) fenv) dbenv nenv)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (AndProp nat aexp_Imp_Lang l1 l2)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (AndProp nat aexp_Imp_Lang l1 l2)) fenv dbenv
             (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv aexp dbenv fenv nenv n0 H1).
  eapply RelAndProp.
  - pose proof (IHl1 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
    (Imp_Lang_lp_arith l1))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_arith. auto.
    + pose proof (H5 H6). unfold aupdate in H9.
      pose proof (H9 n0 H1).
      inversion H10. subst. inversion H12. subst. auto.
  - pose proof (IHl2 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
    (Imp_Lang_lp_arith l2))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_arith. auto.
    + pose proof (H5 H6). unfold aupdate in H9.
      pose proof (H9 n0 H1).
      inversion H10. subst. inversion H12. subst. auto.
Qed.

Lemma aupdate_subst_equiv_aexp_OrProp (l1 l2 : LogicProp nat aexp_Imp_Lang)
      (fenv : fun_env)
      (IHl1 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_arith l1)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_arith l1)) fenv) dbenv nenv)
      (IHl2 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_arith l2)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_arith l2)) fenv) dbenv nenv)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (OrProp nat aexp_Imp_Lang l1 l2)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (OrProp nat aexp_Imp_Lang l1 l2)) fenv dbenv
             (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst.  inversion H3. subst.
  inversion H4; subst.
  - eapply RelOrPropLeft.
    pose proof (IHl1 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
    (Imp_Lang_lp_arith l1))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_arith. auto.
    + pose proof (H2 H5). unfold aupdate in H7.
      pose proof (H7 n0 H1).
      inversion H8. subst. inversion H10. subst. auto.
  - eapply RelOrPropRight.
    pose proof (IHl2 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
    (Imp_Lang_lp_arith l2))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_arith. auto.
    + pose proof (H2 H5). unfold aupdate in H7.
      pose proof (H7 n0 H1).
      inversion H8. subst. inversion H10. subst. auto.
Qed.

Lemma aupdate_subst_equiv_aexp_TernaryProp (f : nat -> nat -> nat -> Prop)
      (a1 a2 a3 : aexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP
                                (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang f a1 a2 a3)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang f a1 a2 a3)) fenv
             dbenv (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst. inversion H3. subst.
  inversion H4. subst.
  pose proof (update_imp_lang_update_equiv aexp dbenv fenv nenv n0 H1).
  eapply RelTernaryProp.
  - pose proof (H2 v1 x a1). apply H5. auto.
  - pose proof (H2 v2 x a2). apply H5. auto.
  - pose proof (H2 v3 x a3). apply H5. auto.
  - auto.
Qed.

Lemma aupdate_subst_equiv_aexp_NaryProp (f : list nat -> Prop)
      (a_list : list aexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_arith (NaryProp nat aexp_Imp_Lang f a_list))))
              fenv dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  Imp_Lang_lp_rel (Imp_Lang_lp_arith (NaryProp nat aexp_Imp_Lang f a_list)) fenv dbenv
             (update x n0 nenv).
Proof.
  apply Imp_Lang_lp_rel_arith. inversion H0. subst. inversion H3. subst.
  inversion H4. subst. eapply RelNaryProp.
  - pose proof (aupdate_subst_args_equiv (fun (a : aexp_Imp_Lang) (v : nat) =>
    a_Imp_Lang a dbenv fenv nenv v) ((map (fun a : aexp_Imp_Lang => imp_lang_aexp_update x aexp a) a_list)) vals).
    pose proof (H2 H7 dbenv nenv fenv aexp n0 a_list x).
    apply H5; auto.
  - auto.
Qed.

Lemma aupdate_subst_equiv_logic_prop_aexp (l : LogicProp nat aexp_Imp_Lang)
      (fenv : fun_env):
  forall (dbenv : list nat) (nenv : nat_env) (aexp : aexp_Imp_Lang) 
    (n : nat) (x : string),
    a_Imp_Lang aexp dbenv fenv nenv n ->
    AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_arith l))) fenv
                dbenv nenv ->
    aupdate x aexp fenv (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_arith l)) fenv)
            dbenv nenv.
Proof.
  induction l; intros; unfold aupdate; intros;
  pose proof (a_Imp_Lang_deterministic dbenv fenv nenv aexp n n0 H H1);
  subst; apply AbsEnv_leaf.
  - eapply aupdate_subst_equiv_aexp_TrueProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_FalseProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_UnaryProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_BinaryProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_AndProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_OrProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_TernaryProp; eassumption.
  - eapply aupdate_subst_equiv_aexp_NaryProp; eassumption. 
Qed.


Lemma aupdate_subst_equiv_TrueProp (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (TrueProp bool bexp_Imp_Lang)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v) (TrueProp bool bexp_Imp_Lang).
Proof.
  apply RelTrueProp.
Qed.

Lemma aupdate_subst_equiv_FalseProp (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (FalseProp bool bexp_Imp_Lang)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v) (FalseProp bool bexp_Imp_Lang).
Proof.
  inversion H0. subst. inversion H3. subst. inversion H4.
Qed.

Lemma aupdate_subst_equiv_UnaryProp (f : bool -> Prop)
      (a : bexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp bool bexp_Imp_Lang f a)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v)
    (UnaryProp bool bexp_Imp_Lang f a).
Proof.
  inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv_bexp aexp dbenv fenv nenv n0 H1 a v x).
  destruct H2.
  eapply RelUnaryProp.
  - apply H2. auto.
  - auto.
Qed.



Lemma aupdate_subst_equiv_BinaryProp (f : bool -> bool -> Prop)
      (a1 a2 : bexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (BinaryProp bool bexp_Imp_Lang f a1 a2))))
              fenv dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v)
    (BinaryProp bool bexp_Imp_Lang f a1 a2).
Proof.
  inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv_bexp aexp dbenv fenv nenv n0 H1).
  eapply RelBinaryProp.
  - apply H2. apply H8.
  - apply H2. apply H9.
  - apply H10.
Qed.


Lemma aupdate_subst_equiv_AndProp (l1 l2 : LogicProp bool bexp_Imp_Lang)
      (fenv : fun_env)
      (IHl1 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_bool l1)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_bool l1)) fenv) dbenv nenv)
      (IHl2 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_bool l2)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_bool l2)) fenv) dbenv nenv)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (AndProp bool bexp_Imp_Lang l1 l2)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v)
    (AndProp bool bexp_Imp_Lang l1 l2).
Proof.
  inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv_bexp aexp dbenv fenv nenv n0 H1).
  eapply RelAndProp.
  - pose proof (IHl1 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
                                                 (Imp_Lang_lp_bool l1))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_bool. auto.
    + pose proof (H5 H6). unfold aupdate in H9.
      pose proof (H9 n0 H1).
      inversion H10. subst. inversion H12. subst. auto.
  - pose proof (IHl2 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
                                                 (Imp_Lang_lp_bool l2))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_bool. auto.
    + pose proof (H5 H6). unfold aupdate in H9.
      pose proof (H9 n0 H1).
      inversion H10. subst. inversion H12. subst. auto.
Qed.


Lemma aupdate_subst_equiv_OrProp (l1 l2 : LogicProp bool bexp_Imp_Lang)
      (fenv : fun_env)
      (IHl1 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_bool l1)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_bool l1)) fenv) dbenv nenv)
      (IHl2 : forall (dbenv : list nat) (nenv : nat_env)
                (aexp : aexp_Imp_Lang) (n : nat) (x : string),
          a_Imp_Lang aexp dbenv fenv nenv n ->
          AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_bool l2)))
                      fenv dbenv nenv ->
          aupdate x aexp fenv
                  (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_bool l2)) fenv) dbenv nenv)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (OrProp bool bexp_Imp_Lang l1 l2)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v) (OrProp bool bexp_Imp_Lang l1 l2).
Proof.
  inversion H0. subst.  inversion H3. subst.
  inversion H4; subst.
  - eapply RelOrPropLeft.
    pose proof (IHl1 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
                                                 (Imp_Lang_lp_bool l1))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_bool. auto.
    + pose proof (H2 H5). unfold aupdate in H7.
      pose proof (H7 n0 H1).
      inversion H8. subst. inversion H10. subst. auto.
  - eapply RelOrPropRight.
    pose proof (IHl2 dbenv nenv aexp n0 x H1).
    assert (AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP
                                                 (Imp_Lang_lp_bool l2))) fenv dbenv nenv).
    + cbn. apply AbsEnv_leaf. apply Imp_Lang_lp_rel_bool. auto.
    + pose proof (H2 H5). unfold aupdate in H7.
      pose proof (H7 n0 H1).
      inversion H8. subst. inversion H10. subst. auto.
Qed.


Lemma aupdate_subst_equiv_TernaryProp (f : bool -> bool -> bool -> Prop)
      (a1 a2 a3 : bexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP
                                (Imp_Lang_lp_bool (TernaryProp bool bexp_Imp_Lang f a1 a2 a3)))) fenv
              dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v)
    (TernaryProp bool bexp_Imp_Lang f a1 a2 a3).
Proof.
  inversion H0. subst.
  inversion H3. subst. inversion H4. subst.
  pose proof (update_imp_lang_update_equiv_bexp aexp dbenv fenv nenv n0 H1).
  eapply RelTernaryProp.
  - apply H2. apply H9.
  - apply H2. apply H10.
  - apply H2. apply H11.
  - auto.
Qed.


Lemma aupdate_subst_equiv_NaryProp (f : list bool -> Prop)
      (a_list : list bexp_Imp_Lang)
      (fenv : fun_env)
      (dbenv : list nat)
      (nenv : nat_env)
      (aexp : aexp_Imp_Lang)
      (x : string)
      (n0 : nat)
      (H : a_Imp_Lang aexp dbenv fenv nenv n0)
      (H0 : AbsEnv_rel
              (subst_AbsEnv x aexp
                             (AbsEnvLP (Imp_Lang_lp_bool (NaryProp bool bexp_Imp_Lang f a_list))))
              fenv dbenv nenv)
      (H1 : a_Imp_Lang aexp dbenv fenv nenv n0):
  eval_prop_rel
    (fun (b : bexp_Imp_Lang) (v : bool) =>
       b_Imp_Lang b dbenv fenv (update x n0 nenv) v)
    (NaryProp bool bexp_Imp_Lang f a_list).
Proof.
  inversion H0. subst. inversion H3. subst.
  inversion H4. subst. eapply RelNaryProp.
  - pose proof (aupdate_subst_args_equiv_bexp (fun (a : bexp_Imp_Lang) (v : bool) =>
    b_Imp_Lang a dbenv fenv nenv v) ((map (fun a : bexp_Imp_Lang => imp_lang_bexp_update x aexp a) a_list)) vals).
    pose proof (H2 H7 dbenv nenv fenv aexp n0 a_list x).
    apply H5; auto.
  - auto.
Qed.


Lemma aupdate_subst_equiv_logic_prop_bool (l : LogicProp bool bexp_Imp_Lang)
      (fenv : fun_env):
  forall (dbenv : list nat) (nenv : nat_env) (aexp : aexp_Imp_Lang) 
    (n : nat) (x : string),
    a_Imp_Lang aexp dbenv fenv nenv n ->
    AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP (Imp_Lang_lp_bool l))) fenv
                dbenv nenv ->
    aupdate x aexp fenv (AbsEnv_rel (AbsEnvLP (Imp_Lang_lp_bool l)) fenv)
            dbenv nenv.
Proof.
  induction l; intros; unfold aupdate; intros;
  pose proof (a_Imp_Lang_deterministic dbenv fenv nenv aexp n n0 H H1);
  subst; apply AbsEnv_leaf; apply Imp_Lang_lp_rel_bool.
  - eapply aupdate_subst_equiv_TrueProp; eassumption.
  - eapply aupdate_subst_equiv_FalseProp; eassumption.
  - eapply aupdate_subst_equiv_UnaryProp; eassumption.
  - eapply aupdate_subst_equiv_BinaryProp; eassumption.
  - eapply aupdate_subst_equiv_AndProp; eassumption.
  - eapply aupdate_subst_equiv_OrProp; eassumption.
  - eapply aupdate_subst_equiv_TernaryProp; eassumption.
  - eapply aupdate_subst_equiv_NaryProp; eassumption.
Qed.


Lemma aupdate_subst_equiv_imp_lang_lp_log (s : Imp_Lang_lp)
      (fenv : fun_env):
  forall (dbenv : list nat) (nenv : nat_env) (aexp : aexp_Imp_Lang) 
    (n : nat) (x : string),
    a_Imp_Lang aexp dbenv fenv nenv n ->
    AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvLP s)) fenv dbenv nenv ->
    aupdate x aexp fenv (AbsEnv_rel (AbsEnvLP s) fenv) dbenv nenv.
Proof.
  induction s.
  - apply aupdate_subst_equiv_logic_prop_aexp; assumption.
  - apply aupdate_subst_equiv_logic_prop_bool; assumption. 
Qed.



Lemma  aupdate_subst_equiv_imp_lang_and_log (log1 log2 : AbsEnv)
       (fenv : fun_env)
       (IHlog1 : forall (dbenv : list nat) (nenv : nat_env)
                   (aexp : aexp_Imp_Lang) (n : nat) (x : string),
           a_Imp_Lang aexp dbenv fenv nenv n ->
           AbsEnv_rel (subst_AbsEnv x aexp log1) fenv dbenv nenv ->
           aupdate x aexp fenv (AbsEnv_rel log1 fenv) dbenv nenv)
       (IHlog2 : forall (dbenv : list nat) (nenv : nat_env)
                   (aexp : aexp_Imp_Lang) (n : nat) (x : string),
           a_Imp_Lang aexp dbenv fenv nenv n ->
           AbsEnv_rel (subst_AbsEnv x aexp log2) fenv dbenv nenv ->
           aupdate x aexp fenv (AbsEnv_rel log2 fenv) dbenv nenv):
  forall (dbenv : list nat) (nenv : nat_env) (aexp : aexp_Imp_Lang) 
    (n : nat) (x : string),
    a_Imp_Lang aexp dbenv fenv nenv n ->
    AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvAnd log1 log2)) fenv dbenv
                nenv ->
    aupdate x aexp fenv (AbsEnv_rel (AbsEnvAnd log1 log2) fenv) dbenv
            nenv.
Proof.
  unfold aupdate; intros;
  pose proof (a_Imp_Lang_deterministic dbenv fenv nenv aexp n n0 H H1);
  subst; inversion H0. subst. apply AbsEnv_and.
  - pose proof (IHlog1 dbenv nenv aexp n0 x H). apply H2; auto.
  - pose proof (IHlog2 dbenv nenv aexp n0 x H). apply H2; auto.
Qed.




Lemma  aupdate_subst_equiv_imp_lang_or_log (log1 log2 : AbsEnv)
       (fenv : fun_env)
       (IHlog1 : forall (dbenv : list nat) (nenv : nat_env)
                   (aexp : aexp_Imp_Lang) (n : nat) (x : string),
           a_Imp_Lang aexp dbenv fenv nenv n ->
           AbsEnv_rel (subst_AbsEnv x aexp log1) fenv dbenv nenv ->
           aupdate x aexp fenv (AbsEnv_rel log1 fenv) dbenv nenv)
       (IHlog2 : forall (dbenv : list nat) (nenv : nat_env)
                   (aexp : aexp_Imp_Lang) (n : nat) (x : string),
           a_Imp_Lang aexp dbenv fenv nenv n ->
           AbsEnv_rel (subst_AbsEnv x aexp log2) fenv dbenv nenv ->
           aupdate x aexp fenv (AbsEnv_rel log2 fenv) dbenv nenv):
  forall (dbenv : list nat) (nenv : nat_env) (aexp : aexp_Imp_Lang) 
    (n : nat) (x : string),
    a_Imp_Lang aexp dbenv fenv nenv n ->
    AbsEnv_rel (subst_AbsEnv x aexp (AbsEnvOr log1 log2)) fenv dbenv
                nenv ->
    aupdate x aexp fenv (AbsEnv_rel (AbsEnvOr log1 log2) fenv) dbenv nenv.
Proof.
  unfold aupdate; intros;
  pose proof (a_Imp_Lang_deterministic dbenv fenv nenv aexp n n0 H H1);
  subst; inversion H0; subst.
  - pose proof (IHlog1 dbenv nenv aexp n0 x H H7). unfold aupdate in H2.
    apply AbsEnv_or_left.
    apply H2; auto.
  - pose proof (IHlog2 dbenv nenv aexp n0 x H H7). unfold aupdate in H2.
    apply AbsEnv_or_right.
    apply H2; auto.
Qed.


Lemma aupdate_subst_equiv log fenv : 
  forall dbenv nenv aexp n x, 
    a_Imp_Lang aexp dbenv fenv nenv n -> 
    AbsEnv_rel (subst_AbsEnv x aexp log) fenv dbenv nenv -> 
    aupdate x aexp fenv (AbsEnv_rel log fenv) dbenv nenv.
Proof. 
  induction log.
  - apply aupdate_subst_equiv_imp_lang_lp_log; assumption.
  - apply aupdate_subst_equiv_imp_lang_and_log; assumption.
  - apply aupdate_subst_equiv_imp_lang_or_log; assumption.
Qed.



