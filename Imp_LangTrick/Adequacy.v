From Coq Require Import Arith Psatz Bool String List Program.Equality Logic.Eqdep_dec Nat.
(* requires coq-reduction-effects
   you can install this with `opam install coq-reduction-effects`
   I used this for debugging the evaluation function *)
From ReductionEffect Require Import PrintingEffect.
From Imp_LangTrick Require Import Imp_LangTrickLanguage.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.


Theorem successor_fuel :
  forall fuel dbenv fenv nenv,
    (forall i nenv',
        eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some nenv' ->
        eval_fuel_Imp_Lang i (S fuel) dbenv fenv nenv = Some nenv')
    /\ (forall a n,
          eval_aImp_Lang a fuel dbenv fenv nenv = Some n ->
          eval_aImp_Lang a (S fuel) dbenv fenv nenv = Some n)
    /\ (forall b bl,
          eval_bImp_Lang b fuel dbenv fenv nenv = Some bl ->
          eval_bImp_Lang b (S fuel) dbenv fenv nenv = Some bl)
    /\ (forall args dbenv',
          eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv' ->
          eval_args_Imp_Lang args (S fuel) dbenv fenv nenv = Some dbenv').
Proof.
  dependent induction fuel.
  - intros. split; [| split; [| split ]]; intros; inversion H.
    + destruct i; try discriminate.
      simpl. reflexivity.
    + destruct a; try discriminate; try (simpl; reflexivity).
  - intros; split; [| split; [| split]]; intros; pose proof IHfuel as IHfuel'; pose proof IHfuel as IHfuel''; specialize (IHfuel' dbenv fenv); specialize (IHfuel dbenv fenv nenv); destruct IHfuel as [IHiImp_Lang [IHaImp_Lang [IHbImp_Lang IHargsImp_Lang]]].
    (* pose proof IHfuel as IHfuel'. *)
    (* specialize (IHfuel' dbenv fenv). *)
    (* specialize (IHfuel dbenv fenv nenv). *)
    
    + destruct i; simpl in H; unfold option_bind, option_map in H; remember (S fuel) as fuel'; simpl; unfold option_bind, option_map, option_map_map.
      * destruct (eval_bImp_Lang b fuel dbenv fenv nenv) eqn:EVALB; try discriminate.
        eapply IHbImp_Lang in EVALB.
        rewrite EVALB.
        eapply IHiImp_Lang in H. eassumption.
      * eassumption.
      * destruct (eval_bImp_Lang b fuel dbenv fenv nenv) eqn:EVALB; try discriminate.
        eapply IHbImp_Lang in EVALB.
        rewrite EVALB.
        destruct b0.
        -- destruct (eval_fuel_Imp_Lang i fuel dbenv fenv nenv) eqn:EVALIMP_LANG; try discriminate.
           eapply IHiImp_Lang in EVALIMP_LANG.
           rewrite EVALIMP_LANG.
           specialize (IHfuel' n); destruct IHfuel' as [IHiImp_Lang' _].
           eapply IHiImp_Lang' in H.
           assumption.
        -- assumption.
      * destruct (eval_aImp_Lang a fuel dbenv fenv nenv) eqn:EVALA; try discriminate.
        eapply IHaImp_Lang in EVALA.
        rewrite EVALA.
        assumption.
      * destruct (eval_fuel_Imp_Lang i1 fuel dbenv fenv) eqn:EVALI; try discriminate.
        eapply IHiImp_Lang in EVALI.
        rewrite EVALI.
        specialize (IHfuel' n); destruct IHfuel' as [IHiImp_Lang' _].
        eapply IHiImp_Lang' in H.
        assumption.
    + destruct a; simpl in H; unfold option_bind, option_map, option_map_map in H; remember (S fuel) as fuel'; simpl; unfold option_bind, option_map, option_map_map; try assumption.
      * destruct (eval_aImp_Lang a1 fuel dbenv fenv nenv) eqn:EVALA; try discriminate.
        eapply IHaImp_Lang in EVALA.
        rewrite EVALA.
        unfold option_map in *.
        destruct (eval_aImp_Lang a2 fuel dbenv fenv nenv) eqn:EVALA2; try discriminate.
        eapply IHaImp_Lang in EVALA2.
        rewrite EVALA2.
        assumption.
      * destruct (eval_aImp_Lang a1 fuel dbenv fenv nenv) eqn:EVALA1; try discriminate.
        eapply IHaImp_Lang in EVALA1.
        rewrite EVALA1.
        unfold option_map in *.
        destruct (eval_aImp_Lang a2 fuel dbenv fenv nenv) eqn:EVALA2; try discriminate.
        eapply IHaImp_Lang in EVALA2.
        rewrite EVALA2.
        assumption. 
      * destruct (eval_args_Imp_Lang aexps fuel dbenv fenv nenv) eqn:EVALARGS; try discriminate.
        eapply IHargsImp_Lang in EVALARGS.
        rewrite EVALARGS.
        destruct (eval_fuel_Imp_Lang (Body (fenv f)) fuel l fenv init_nenv) eqn:BODY; try discriminate.
        specialize (IHfuel'' l fenv init_nenv); destruct IHfuel'' as [IHiImp_Lang' _].
        eapply IHiImp_Lang' in BODY.
        rewrite BODY.
        assumption.
        destruct Nat.eqb in H; try discriminate.  
        destruct Nat.eqb in H; try discriminate.   
    + destruct b; simpl in H; unfold option_bind, option_map, option_map_map in H; remember (S fuel) as fuel'; simpl; unfold option_bind, option_map, option_map_map; try assumption.
      * destruct (eval_bImp_Lang b fuel dbenv fenv nenv) eqn:EVALB; try discriminate.
        eapply IHbImp_Lang in EVALB.
        rewrite EVALB. assumption.
      * destruct (eval_bImp_Lang b1 fuel dbenv fenv nenv) eqn:EVALB1; try discriminate.
        eapply IHbImp_Lang in EVALB1.
        rewrite EVALB1.
        unfold option_map in *.
        destruct (eval_bImp_Lang b2 fuel dbenv fenv nenv) eqn:EVALB2; try discriminate.
        eapply IHbImp_Lang in EVALB2. rewrite EVALB2. assumption.
      * destruct (eval_bImp_Lang b1 fuel dbenv fenv nenv) eqn:EVALB1; try discriminate.
        eapply IHbImp_Lang in EVALB1.
        rewrite EVALB1.
        unfold option_map in *.
        destruct (eval_bImp_Lang b2 fuel dbenv fenv nenv) eqn:EVALB2; try discriminate.
        eapply IHbImp_Lang in EVALB2. rewrite EVALB2. assumption.
      * destruct (eval_aImp_Lang a1 fuel dbenv fenv nenv) eqn:EVALA1; try discriminate.
        eapply IHaImp_Lang in EVALA1.
        rewrite EVALA1.
        unfold option_map in *.
        destruct (eval_aImp_Lang a2 fuel dbenv fenv nenv) eqn:EVALA2; try discriminate.
        eapply IHaImp_Lang in EVALA2.
        rewrite EVALA2.
        assumption.
    + destruct args; simpl in H.
      * inversion H. simpl. reflexivity.
      * destruct (eval_aImp_Lang a fuel dbenv fenv nenv) eqn:EVALA; try discriminate.
        remember (S fuel) as fuel'. simpl.
        eapply IHaImp_Lang in EVALA.
        rewrite EVALA.
        destruct (eval_args_Imp_Lang args fuel dbenv fenv nenv) eqn:EVALARGS; try discriminate.
        apply IHargsImp_Lang in EVALARGS.
        rewrite EVALARGS.
        assumption.
Qed.

                                                                  
        
        
      

Lemma successor_fuel_bImp_Lang :
  forall b fuel dbenv fenv nenv b',
    eval_bImp_Lang b fuel dbenv fenv nenv = Some b' ->
    eval_bImp_Lang b (S fuel) dbenv fenv nenv = Some b'.
Proof.
  intros.
  pose proof (successor_fuel fuel dbenv fenv nenv) as FUEL; destruct FUEL as [_ [_ [BFUEL _ ]]].
  eapply BFUEL.
  assumption.
Qed.

Lemma added_fuel_bImp_Lang :
  forall b fuel deltafuel dbenv fenv nenv b',
    eval_bImp_Lang b fuel dbenv fenv nenv = Some b' ->
    eval_bImp_Lang b (fuel + deltafuel) dbenv fenv nenv = Some b'.
Proof.
  intros b fuel deltafuel.
  revert b fuel.
  induction deltafuel; intros.
  - rewrite Nat.add_0_r. assumption.
  - rewrite Nat.add_comm. remember (S deltafuel + fuel) as fuel'. simpl in Heqfuel'. rewrite Heqfuel' in *. clear Heqfuel' fuel'.
    eapply IHdeltafuel in H.
    rewrite Nat.add_comm in H.
    eapply successor_fuel_bImp_Lang. assumption.
Qed.


Lemma geq_fuel_bImp_Lang :
  forall b fuel fuel' dbenv fenv nenv b',
    fuel <= fuel' ->
    eval_bImp_Lang b fuel dbenv fenv nenv = Some b' ->
    eval_bImp_Lang b fuel' dbenv fenv nenv = Some b'.
Proof.
  intros.
  apply Nat.le_exists_sub in H.
  destruct H as [deltafuel H].
  destruct H as [Hplus _].
  rewrite Nat.add_comm in Hplus.
  rewrite Hplus. eapply added_fuel_bImp_Lang.
  assumption.
Qed.


Lemma successor_fuel_aImp_Lang :
  forall a fuel dbenv fenv nenv a',
    eval_aImp_Lang a fuel dbenv fenv nenv = Some a' ->
    eval_aImp_Lang a (S fuel) dbenv fenv nenv = Some a'.
Proof.
  intros.
  pose proof (successor_fuel fuel dbenv fenv nenv) as FUEL; destruct FUEL as [_ [AFUEL _]].
  eapply AFUEL. assumption.
Qed.

Lemma geq_fuel_aImp_Lang :
  forall a fuel fuel' dbenv fenv nenv a',
    fuel <= fuel' ->
    eval_aImp_Lang a fuel dbenv fenv nenv = Some a' ->
    eval_aImp_Lang a fuel' dbenv fenv nenv = Some a'.
Proof.
  intros a fuel fuel' dbenv fenv nenv a' Hfuel.
  apply Nat.le_exists_sub in Hfuel.
  destruct Hfuel as [deltafuel [Hfuel _]].
  rewrite Nat.add_comm in Hfuel.
  revert Hfuel. revert a' nenv fenv dbenv fuel' fuel a.
  induction deltafuel; intros.
  - rewrite Nat.add_0_r in Hfuel.
    rewrite Hfuel in *.
    assumption.
  - rewrite Nat.add_comm in Hfuel. simpl in Hfuel. rewrite Nat.add_comm in Hfuel.
    eapply IHdeltafuel.
    rewrite <- Nat.add_succ_l in Hfuel.
    eassumption.
    eapply successor_fuel_aImp_Lang.
    assumption.
Qed.

Local Open Scope imp_langtrick_scope.

Lemma successor_fuel_false_ifImp_Lang :
  forall fuel fenv dbenv nenv nenv' b i1 i2,
    eval_bImp_Lang b fuel dbenv fenv nenv = Some false ->
    eval_fuel_Imp_Lang (when b then i1 else i2 done) (S fuel) dbenv fenv nenv = Some nenv' ->
    eval_fuel_Imp_Lang i2 fuel dbenv fenv nenv = Some nenv'.
Proof.
  intros. simpl in H0. unfold option_bind in H0.
  rewrite H in H0. simpl in H0. assumption.
Qed.

Lemma successor_fuel_true_ifImp_Lang :
  forall fuel fenv dbenv nenv nenv' b i1 i2,
    eval_bImp_Lang b fuel dbenv fenv nenv = Some true ->
    eval_fuel_Imp_Lang (when b then i1 else i2 done) (S fuel) dbenv fenv nenv = Some nenv' ->
    eval_fuel_Imp_Lang i1 fuel dbenv fenv nenv = Some nenv'.
Proof.
  intros. simpl in H0. unfold option_bind in H0.
  rewrite H in H0. simpl in H0. assumption.
Qed.

Lemma successor_fuel_imp_Imp_Lang :
  forall i fuel fenv dbenv nenv nenv',
    eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some nenv' ->
    eval_fuel_Imp_Lang i (S fuel) dbenv fenv nenv = Some nenv'.
Proof.
  intros. pose proof (successor_fuel fuel dbenv fenv nenv) as FUEL; destruct FUEL as [IFUEL _].
  eapply IFUEL. assumption.
Qed.

Lemma geq_fuel_imp_Imp_Lang :
  forall i fuel fuel' dbenv fenv nenv nenv',
    fuel <= fuel' ->
    eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some nenv' ->
    eval_fuel_Imp_Lang i fuel' dbenv fenv nenv = Some nenv'.
Proof.
  intros i fuel fuel' dbenv fenv nenv nenv' Hfuel.
  apply Nat.le_exists_sub in Hfuel.
  destruct Hfuel as [deltafuel [Hfuel _]].
  rewrite Nat.add_comm in Hfuel.
  revert Hfuel. revert nenv' nenv fenv dbenv fuel' fuel i.
  induction deltafuel; intros.
  - rewrite Nat.add_0_r in Hfuel.
    rewrite Hfuel in *.
    assumption.
  - rewrite Nat.add_comm in Hfuel. simpl in Hfuel. rewrite Nat.add_comm in Hfuel.
    eapply IHdeltafuel.
    rewrite <- Nat.add_succ_l in Hfuel.
    eassumption.
    eapply successor_fuel_imp_Imp_Lang.
    assumption.
Qed.

Lemma successor_fuel_args_Imp_Lang :
  forall args fuel fenv dbenv nenv dbenv',
    eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv' ->
    eval_args_Imp_Lang args (S fuel) dbenv fenv nenv = Some dbenv'.
Proof.
  intros. pose proof (successor_fuel fuel dbenv fenv nenv) as FUEL; destruct FUEL as [_ [_ [_ ARGSFUEL]]].
  eapply ARGSFUEL. assumption.
Qed.

Lemma geq_fuel_args_Imp_Lang :
  forall args fuel fuel' dbenv fenv nenv dbenv',
    fuel <= fuel' ->
    eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv' ->
    eval_args_Imp_Lang args fuel' dbenv fenv nenv = Some dbenv'.
Proof.
  intros args fuel fuel' dbenv fenv nenv dbenv' Hfuel.
  apply Nat.le_exists_sub in Hfuel.
  destruct Hfuel as [deltafuel [Hfuel _]].
  rewrite Nat.add_comm in Hfuel.
  revert Hfuel. revert dbenv' nenv fenv dbenv fuel' fuel args.
  induction deltafuel; intros.
  - rewrite Nat.add_0_r in Hfuel.
    rewrite Hfuel in *.
    assumption.
  - rewrite Nat.add_comm in Hfuel. simpl in Hfuel. rewrite Nat.add_comm in Hfuel.
    eapply IHdeltafuel.
    rewrite <- Nat.add_succ_l in Hfuel.
    eassumption.
    eapply successor_fuel_args_Imp_Lang.
    assumption.
Qed.

(* Lemma successor_fuel_blue_Imp_Lang : *)
(*   forall i fuel fenv nenv nenv', *)
(*     blue_Imp_Lang fuel (i, fenv, nenv) nenv' -> *)
(*     blue_Imp_Lang (S fuel) (i, fenv, nenv) nenv'. *)
(* Proof. *)
(* Admitted. *)

Ltac invc H :=
  inversion H; subst; clear H.

Ltac duplicate_proof H H' :=
  pose proof H as H'.

Tactic Notation "dupe" ident(H) "as" ident(H') := (duplicate_proof H H').


(*eval_fuel_Imp_Lang (i: imp_Imp_Lang) (fuel: nat) (fenv: fun_env) (nenv: nat_env) : option nat_env*)

(* Definition star_Imp_Lang := star (imp_Imp_Lang * fun_env * nat_env) red_Imp_Lang. *)

Fixpoint construct_fenv lst (f: fun_env) : fun_env :=
  match lst with
  | nil => f
  | foo::foos => construct_fenv foos (update ((foo).(Name)) foo f)
  end.

Definition eval_fuel_pImp_Lang (p: prog_Imp_Lang) (fuel: nat): option nat_env :=
  match p with
  | PROF_Imp_Lang lst imp =>
      let new_fenv := construct_fenv lst init_fenv in
      eval_fuel_Imp_Lang imp fuel nil new_fenv init_nenv
  end.


Check imp_Imp_Lang_ind. 

Scheme i_Imp_Lang_mut := Induction for i_Imp_Lang Sort Prop
with a_Imp_Lang_mut := Induction for a_Imp_Lang Sort Prop
with b_Imp_Lang_mut := Induction for b_Imp_Lang Sort Prop
with args_Imp_Lang_mut := Induction for args_Imp_Lang Sort Prop.

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

Tactic Notation "destruct_discrim" constr(x) "eqn" ident(eq) :=
  destruct x eqn:eq; try discriminate; try discrim_neq.

Ltac specialize_ihfuel_bimp IHfuel bexp dbenv fenv nenv b :=
  specialize (IHfuel SKIP_Imp_Lang (CONST_Imp_Lang 0) bexp dbenv fenv nenv init_nenv 0 b nil nil);
  destruct IHfuel as [_ [_ [IHbImp_Lang _]]];
  match goal with
  | [ H: eval_bImp_Lang bexp _ dbenv fenv nenv = Some b |- _ ] => apply IHbImp_Lang in H
  | _ => idtac "no match"
  end.

Ltac specialize_ihfuel_aimp_lang IHfuel aexp dbenv fenv nenv n :=
  specialize (IHfuel SKIP_Imp_Lang aexp TRUE_Imp_Lang dbenv fenv nenv init_nenv n true nil nil);
  destruct IHfuel as [_ [IHaImp_Lang _]];
  match goal with
  | [ H: eval_aImp_Lang aexp _ dbenv fenv nenv = Some n |- _ ] => apply IHaImp_Lang in H
  | _ => idtac "no match"
  end.

(* IHfuel: forall (i : imp_Imp_Lang) (aexp : aexp_Imp_Lang) (bexp : bexp_Imp_Lang)
           (dbenv : list nat) (fenv : fun_env) (nenv s : nat_env) 
           (n : nat) (b : bool) (args : list aexp_Imp_Lang) 
           (dbenv' : list nat),
         (eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some s ->
          i_Imp_Lang i dbenv fenv nenv s) /\
         (eval_aImp_Lang aexp fuel dbenv fenv nenv = Some n ->
          a_Imp_Lang aexp dbenv fenv nenv n) /\
         (eval_bImp_Lang bexp fuel dbenv fenv nenv = Some b ->
          b_Imp_Lang bexp dbenv fenv nenv b) /\
         (eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv' ->
          args_Imp_Lang args dbenv fenv nenv dbenv') *)

Ltac specialize_ihfuel_args_imp_lang IHfuel args dbenv fenv nenv dbenv' :=
  specialize (IHfuel SKIP_Imp_Lang (CONST_Imp_Lang 0) TRUE_Imp_Lang dbenv fenv nenv init_nenv 0 true args dbenv');
  destruct IHfuel as [_ [_ [_ IHargsImp_Lang]]];
  match goal with
  | [ H: eval_args_Imp_Lang args _ dbenv fenv nenv = Some dbenv' |- _ ] => apply IHargsImp_Lang in H
  | _ => idtac "no match"
  end.

Ltac specialize_ihfuel_iimp_lang IHfuel i dbenv fenv nenv s :=
  specialize (IHfuel i (CONST_Imp_Lang 0) TRUE_Imp_Lang dbenv fenv nenv s 0 true nil nil);
  destruct IHfuel as [IHiImp_Lang _];
  match goal with
  | [ H: eval_fuel_Imp_Lang i _ dbenv fenv nenv = Some s |- _ ] => apply IHiImp_Lang in H
  | _ => idtac "no match"
  end.

(* This lemma is actually not true, rip *)
Lemma nth_error_some_greater_than :
  forall A (l: list A) n (k: A),
    nth_error l n = Some k ->
    0 <= n < Datatypes.length l.
Proof.
  induction l; intros.
  - induction n; simpl in H; discriminate.
  - induction n; simpl in *; try lia. specialize (IHl n k H). lia.    
Qed. 


Lemma really_adequate_forward_i: 
  forall fuel i aexp bexp dbenv fenv nenv s n b args dbenv',
  (eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some s ->
   i_Imp_Lang i dbenv fenv nenv s) /\
    (eval_aImp_Lang aexp fuel dbenv fenv nenv = Some n -> 
     a_Imp_Lang aexp dbenv fenv nenv n) /\
    (eval_bImp_Lang bexp fuel dbenv fenv nenv = Some b ->
     b_Imp_Lang bexp dbenv fenv nenv b) /\
    (eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv' ->
     args_Imp_Lang args dbenv fenv nenv dbenv'). 
Proof.
  dependent induction fuel.
  - split.
    + intros. 
      inversion H. 
      destruct i; (try inversion H1).
      econstructor.
    + split; [| split]; intros; (try inversion H). 
      destruct aexp; (try inversion H1); try econstructor.
      * reflexivity.
      * eapply nth_error_some_greater_than in H1. assumption.
      * assumption.
  - split; [ | split; [| split ]]; revert i aexp bexp fenv nenv s n b.
    + dependent induction i; intros.
      * inversion H. 
        unfold option_bind, option_map in H1.
        destruct (eval_bImp_Lang b fuel dbenv fenv nenv) eqn:beval.
        -- destruct b1. 
           ++ eapply Imp_Lang_if_true;
                specialize (IHfuel i1 (CONST_Imp_Lang 0) b dbenv fenv nenv s 0 true nil nil); 
                destruct IHfuel as [IHiImp_Lang [_ [IHbImp_Lang _]]].
              ** apply IHbImp_Lang. 
                 assumption.
              ** apply IHiImp_Lang.  
                 assumption.
           ++ eapply Imp_Lang_if_false;
                specialize (IHfuel i2 (CONST_Imp_Lang 0) b dbenv fenv nenv s 0 false nil nil); 
                destruct IHfuel as [IHiImp_Lang [_ [IHbImp_Lang _]]].
              ** apply IHbImp_Lang. 
                 assumption.
              ** apply IHiImp_Lang.  
                 assumption.
        -- discriminate.
      * inversion H. constructor.
      * inversion H. unfold option_bind in H1.
        destruct (eval_bImp_Lang b fuel dbenv fenv nenv) eqn:beval.
        -- destruct b1.
           ++ destruct (eval_fuel_Imp_Lang i fuel dbenv fenv nenv) eqn:ieval.
              ** apply (Imp_Lang_while_step dbenv fenv nenv n0 s b i).
                 --- specialize (IHfuel i (CONST_Imp_Lang 0) b dbenv fenv nenv s 0 true nil nil); 
                       destruct IHfuel as [_ [_ [IHbImp_Lang _ ]]].
                     apply IHbImp_Lang. assumption.   
                 --- specialize (IHfuel i (CONST_Imp_Lang 0) b dbenv fenv nenv n0 0 true nil nil); 
                       destruct IHfuel as [IHiImp_Lang _].
                     apply IHiImp_Lang.
                     assumption.
                 --- specialize (IHfuel (while b loop i done) (CONST_Imp_Lang 0) b dbenv fenv n0 s 0 true nil nil); 
                       destruct IHfuel as [IHiImp_Lang [IHaImp_Lang IHbImp_Lang]].
                     apply IHiImp_Lang.
                     assumption.
              ** discriminate. 
           ++ inversion H. inversion H1. apply (Imp_Lang_while_done dbenv fenv s b i).
              specialize (IHfuel (while b loop i done) (CONST_Imp_Lang 0) b dbenv fenv s s 0 false nil nil); 
                destruct IHfuel as [IHiImp_Lang [IHaImp_Lang [IHbImp_Lang _]]].
              apply IHbImp_Lang.
              subst.
              assumption.
        -- discriminate.   
      * inversion H.
        unfold print_id, option_map in H1. 
        destruct (eval_aImp_Lang a fuel dbenv fenv nenv) eqn:aeval.
        specialize (IHfuel (SKIP_Imp_Lang) a TRUE_Imp_Lang dbenv fenv nenv nenv n0 true nil nil).
        destruct IHfuel as [IHiImp_Lang [IHaImp_Lang _]].
        inversion H1.
        constructor.
        apply IHaImp_Lang. assumption.
        discriminate.
      * inversion H. 
        unfold option_bind, option_map in H1.
        destruct (eval_fuel_Imp_Lang i1 fuel dbenv fenv nenv) eqn:i1eq. 
        apply (Imp_Lang_seq dbenv fenv nenv n0 s i1 i2).  
        -- specialize (IHfuel i1 (CONST_Imp_Lang 0) (TRUE_Imp_Lang) dbenv fenv nenv n0 0 true nil nil).
           destruct IHfuel as [IHiImp_Lang _].
           apply IHiImp_Lang. assumption.
        -- specialize (IHfuel i2 (CONST_Imp_Lang 0) (TRUE_Imp_Lang) dbenv fenv n0 s 0 true nil nil).
           destruct IHfuel as [IHiImp_Lang _].
           apply IHiImp_Lang. assumption.
        -- discriminate.
    + intros impimp_lang. dependent induction aexp; intros. 
      * inversion H. constructor.
      * inversion H.
        constructor.
        reflexivity.
      * assert (eval_aImp_Lang (PARAM_Imp_Lang n) fuel dbenv fenv nenv = Some n0).
        {
          destruct fuel.
          simpl.
          simpl in H. assumption.
          simpl. simpl in H. assumption.
        }
        specialize_ihfuel_aimp_lang IHfuel (PARAM_Imp_Lang n) dbenv fenv nenv n0.
        assumption.
           
      * inversion H. unfold option_map_map in H1. unfold option_map in H1.
        destruct (eval_aImp_Lang aexp1 fuel dbenv fenv nenv) eqn:Eqaexp1.
        destruct (eval_aImp_Lang aexp2 fuel dbenv fenv nenv) eqn:Eqaexp2.
        inversion H1.
        constructor.  
        specialize (IHaexp1 bexp fenv nenv s n0 b). 
        apply successor_fuel_aImp_Lang in Eqaexp1. apply IHaexp1 in Eqaexp1.
        assumption.
        specialize (IHaexp2 bexp fenv nenv s n1 b). 
        apply successor_fuel_aImp_Lang in Eqaexp2. apply IHaexp2 in Eqaexp2.
        assumption.
        all: discriminate. 
      * inversion H. unfold option_map_map in H1. unfold option_map in H1.
        destruct (eval_aImp_Lang aexp1 fuel dbenv fenv nenv) eqn:Eqaexp1.
        destruct (eval_aImp_Lang aexp2 fuel dbenv fenv nenv) eqn:Eqaexp2.
        inversion H1.
        constructor.
          
        specialize (IHaexp1 bexp fenv nenv s n0 b). 
        apply successor_fuel_aImp_Lang in Eqaexp1. apply IHaexp1 in Eqaexp1.
        assumption.
        specialize (IHaexp2 bexp fenv nenv s n1 b). 
        apply successor_fuel_aImp_Lang in Eqaexp2. apply IHaexp2 in Eqaexp2.
        assumption.
        all: discriminate. 
      * inversion H. unfold option_map, option_bind, option_map_map in H1.
        destruct (eval_args_Imp_Lang aexps fuel dbenv fenv nenv) eqn:fargs; [ | inversion H1].
        destruct (eval_fuel_Imp_Lang (Body (fenv f)) fuel l fenv init_nenv) eqn:body; [ | inversion H1].
        invc H1.
        econstructor.
        -- remember (fenv f) as FUNC.
           eauto.
        -- eauto. 
           destruct (Datatypes.length aexps =? Args (fenv f)) eqn:rememberme; try discriminate. 
          pose proof Nat.eqb_eq (Datatypes.length aexps) (Args (fenv f)). destruct H0. specialize (H0 rememberme). symmetry. assumption.   
        -- specialize_ihfuel_args_imp_lang IHfuel aexps dbenv fenv nenv l.
           eassumption.
        -- specialize_ihfuel_iimp_lang IHfuel (Body (fenv f)) l fenv init_nenv n0.
           eassumption.
        --destruct (Datatypes.length aexps =? Args (fenv f)); try assumption; try discriminate. inversion H2; subst.    
          reflexivity.
        --destruct (Datatypes.length aexps =? Args (fenv f)); discriminate. 
        --destruct (Datatypes.length aexps =? Args (fenv f)); discriminate. 
    + intro. intro. dependent induction bexp; intros; try inversion H; try econstructor.
      * unfold option_map in H1.
        destruct (eval_bImp_Lang bexp fuel dbenv fenv nenv); [| simpl in H1; discriminate].
        inversion H1.
        econstructor.
        inversion H.
        unfold option_map in H3.
        destruct (eval_bImp_Lang bexp fuel dbenv fenv nenv) eqn:bimp; [| discriminate].
        specialize_ihfuel_bimp IHfuel bexp dbenv fenv nenv b0.
        assert (b1 = b0) by (destruct b0, b1; subst; auto; inversion H3).
        rewrite <- H0 in *.
        apply IHbImp_Lang in bimp.
        assumption.
      * unfold option_map_map in H1.
        destruct_discrim (eval_bImp_Lang bexp1 fuel dbenv fenv nenv) eqn bimp.
        unfold option_map in H1.
        destruct_discrim (eval_bImp_Lang bexp2 fuel dbenv fenv nenv) eqn bimp2.
        inversion H1.
        econstructor.
        -- specialize_ihfuel_bimp IHfuel bexp1 dbenv fenv nenv b0.
           assumption.
        -- specialize_ihfuel_bimp IHfuel bexp2 dbenv fenv nenv b1.
           assumption.
      * unfold option_map_map in H1.
        destruct_discrim (eval_bImp_Lang bexp1 fuel dbenv fenv nenv) eqn bimp1.
        unfold option_map in H1.
        destruct_discrim (eval_bImp_Lang bexp2 fuel dbenv fenv nenv) eqn bimp2.
        inversion H1.
        econstructor.
        -- specialize_ihfuel_bimp IHfuel bexp1 dbenv fenv nenv b0.
           assumption.
        -- specialize_ihfuel_bimp IHfuel bexp2 dbenv fenv nenv b1.
           assumption.
      * unfold option_map_map in H1.
        destruct_discrim (eval_aImp_Lang a1 fuel dbenv fenv nenv) eqn aimp_lang1.
        unfold option_map in H1.
        destruct_discrim (eval_aImp_Lang a2 fuel dbenv fenv nenv) eqn aimp_lang2.
        invc H1.
        econstructor.
        -- specialize_ihfuel_aimp_lang IHfuel a1 dbenv fenv nenv n0.
           assumption.
        -- specialize_ihfuel_aimp_lang IHfuel a2 dbenv fenv nenv n1.
           assumption.
    + intros.
      dependent induction args.
      * simpl in H. inversion H. constructor.
      * destruct dbenv'.
        -- simpl in H. destruct (eval_aImp_Lang a fuel dbenv fenv nenv).
           ++ destruct (eval_args_Imp_Lang args fuel dbenv fenv nenv); inversion H.
           ++ inversion H.
        -- eapply args_cons.
           ++ simpl in H. specialize_ihfuel_aimp_lang IHfuel a dbenv fenv nenv n0.
              apply IHaImp_Lang.
              destruct (eval_aImp_Lang a fuel dbenv fenv nenv) eqn:aImp_Lang.
              destruct (eval_args_Imp_Lang args fuel dbenv fenv nenv); inversion H.
              reflexivity.
              discriminate.
           ++ eapply IHargs; try eassumption.
              simpl in H.
              destruct (eval_aImp_Lang a fuel dbenv fenv nenv) eqn:aImp_Lang.
              destruct (eval_args_Imp_Lang args fuel dbenv fenv nenv) eqn:argsImp_Lang; inversion H.
              apply successor_fuel_args_Imp_Lang in argsImp_Lang.
              rewrite H2 in argsImp_Lang.
              eassumption.
              inversion H.
Qed.

Check i_Imp_Lang_mutind.

(* eval_fuel_Imp_Lang i1 x0 dbenv fenv nenv = Some nenv' *)

Ltac elim_geq :=
  match goal with
  | [ H1 : eval_fuel_Imp_Lang ?i ?fuel ?dbenv ?fenv ?nenv = Some ?nenv',  H2 : ?fuel <= ?fuel' |- _ ] =>
      apply (geq_fuel_imp_Imp_Lang i fuel fuel' dbenv fenv nenv nenv' H2) in H1
  | [ H1 : eval_bImp_Lang ?b ?fuel ?dbenv ?fenv ?nenv = Some ?b', H2 : ?fuel <= ?fuel' |- _ ] =>
      apply (geq_fuel_bImp_Lang b fuel fuel' dbenv fenv nenv b' H2) in H1
  | [ H1 : eval_aImp_Lang ?a ?fuel ?dbenv ?fenv ?nenv = Some ?a', H2 : ?fuel <= ?fuel' |- _ ] =>
      apply (geq_fuel_aImp_Lang a fuel fuel' dbenv fenv nenv a' H2) in H1
  | [ H1 : eval_args_Imp_Lang ?args ?fuel ?dbenv ?fenv ?nenv = Some ?args', H2 : ?fuel <= ?fuel' |- _ ] =>
      apply (geq_fuel_args_Imp_Lang args fuel fuel' dbenv fenv nenv args' H2) in H1
  (* | [ H: eval_fuel_Imp_Lang ?i ?fuel ?dbenv ?fenv ?nenv = Some ?nenv' |- _ ] => *)
      (* idtac "found something else" *)
  end.


Lemma really_adequate_backward_i :
  (* forall i aexp bexp dbenv fenv nenv s n b args dbenv', *)
  (forall i dbenv fenv nenv s,
      i_Imp_Lang i dbenv fenv nenv s ->
      exists fuel, eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some s) /\
    (forall aexp dbenv fenv nenv n,
        a_Imp_Lang aexp dbenv fenv nenv n ->
        exists fuel, eval_aImp_Lang aexp fuel dbenv fenv nenv = Some n) /\
    (forall bexp dbenv fenv nenv b,
        b_Imp_Lang bexp dbenv fenv nenv b ->
        exists fuel, eval_bImp_Lang bexp fuel dbenv fenv nenv = Some b) /\
    (forall args dbenv fenv nenv dbenv',
        args_Imp_Lang args dbenv fenv nenv dbenv' ->
        exists fuel, eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv').
Proof.
  pose (fun i db f n n0 => fun H: i_Imp_Lang i db f n n0 => exists fuel, eval_fuel_Imp_Lang i fuel db f n = Some n0) as P.
  pose (fun a db f n n0 => fun Ha: a_Imp_Lang a db f n n0 => exists fuel, eval_aImp_Lang a fuel db f n = Some n0) as P0.
  pose (fun b db f n n0 => fun Hb: b_Imp_Lang b db f n n0 => exists fuel, eval_bImp_Lang b fuel db f n = Some n0) as P1.
  pose (fun args db f n n0 => fun Hargs: args_Imp_Lang args db f n n0 => exists fuel, eval_args_Imp_Lang args fuel db f n = Some n0) as P2.
  apply (i_Imp_Lang_mutind P P0 P1 P2); unfold P, P0, P1, P2 in *; intros.
  - exists 0. simpl. reflexivity.
  - destruct H, H0.
    exists (S(x + x0)).
    destruct (S(x + x0)) eqn:Hx.
    assert (x = 0) by lia.
    assert (x0 = 0) by lia.
    rewrite H1, H2 in *.
    simpl in Hx. discriminate.
    simpl.
    unfold option_bind, option_map.
    assert (x <= n) by lia.
    elim_geq.
    rewrite H.
    assert (x0 <= n) by lia.
    elim_geq.
    eassumption.
  - destruct H, H0.
    remember (S (x + x0)) as n.
    exists n.
    destruct n eqn:Hn.
    + assert (x = 0) by lia. assert (x0 = 0) by lia.
      rewrite H1, H2 in *.
      simpl in Heqn. discriminate.
    + assert (x <= n0) by lia. assert (x0 <= n0) by lia.
      simpl.
      unfold option_bind, option_map.
      repeat elim_geq.
      rewrite H. eassumption.
  - destruct H.
    exists (S x0).
    simpl.
    unfold option_map.
    assert (print_id x = x) by (simpl; reflexivity).
    rewrite H0.
    rewrite H.
    f_equal.
  - destruct H.
    exists (S x).
    simpl.
    unfold option_bind.
    rewrite H.
    reflexivity.
  - destruct H, H0, H1.
    exists (S (x + x0 + x1)).
    simpl.
    remember (x + x0 + x1) as n.
    assert (x <= n) by lia. assert (x0 <= n) by lia. assert (x1 <= n) by lia.
    repeat elim_geq.
    unfold option_bind.
    rewrite H.
    rewrite H0.
    eassumption.
  - destruct H, H0.
    remember (x + x0) as n.
    exists (S n).
    simpl.
    unfold option_bind.
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    repeat elim_geq.
    rewrite H, H0. reflexivity.
  - exists 0. simpl. reflexivity.
  - exists 0. simpl. rewrite e. reflexivity.
  - exists 0. simpl. assumption.
  - destruct H, H0.
    remember (x + x0) as n.
    exists (S n).
    simpl.
    unfold option_map_map. unfold option_map.
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    repeat elim_geq.
    rewrite H, H0.
    reflexivity.
  - destruct H, H0.
    remember (x + x0) as n.
    exists (S n).
    simpl. unfold option_map_map. unfold option_map.
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    repeat elim_geq.
    rewrite H, H0.
    reflexivity.
  - destruct H, H0.
    remember (x + x0) as fuel'.
    exists (S fuel').
    simpl.
    unfold option_map, option_bind.
    assert (x <= fuel') by lia. assert (x0 <= fuel') by lia.
    repeat elim_geq.
    rewrite e.
    rewrite H. rewrite H0.
    rewrite e1.
    destruct (Datatypes.length aexps =? Args func) eqn:rememberus. 
    reflexivity. symmetry in e0. rewrite e0 in *. pose proof Nat.eqb_refl (Args func). rewrite H3 in rememberus. discriminate. 
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. reflexivity.
  - destruct H. exists (S x). simpl. unfold option_map. rewrite H.
    reflexivity.
  - destruct H, H0.
    remember (x + x0) as n.
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    exists (S n).
    simpl. unfold option_map_map. unfold option_map.
    repeat elim_geq.
    rewrite H, H0. reflexivity.
  - destruct H, H0.
    remember (x + x0) as n.
    exists (S n).
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    simpl. unfold option_map_map. unfold option_map.
    repeat elim_geq.
    rewrite H, H0. reflexivity.
  - destruct H, H0.
    remember (x + x0) as n.
    exists (S n).
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    simpl. unfold option_map_map. unfold option_map.
    repeat elim_geq.
    rewrite H, H0. reflexivity.
  - exists 1. simpl. reflexivity.
  - destruct H, H0.
    remember (x + x0) as n.
    exists (S n).
    assert (x <= n) by lia. assert (x0 <= n) by lia.
    simpl. unfold option_map_map. unfold option_map.
    repeat elim_geq.
    rewrite H, H0. reflexivity.
Qed.

Lemma really_adequate_backward_i_human_version :
  forall i aexp bexp dbenv fenv nenv s n b args dbenv',
    (i_Imp_Lang i dbenv fenv nenv s ->
     exists fuel, eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some s) /\
      (a_Imp_Lang aexp dbenv fenv nenv n ->
       exists fuel, eval_aImp_Lang aexp fuel dbenv fenv nenv = Some n) /\
      (b_Imp_Lang bexp dbenv fenv nenv b ->
       exists fuel, eval_bImp_Lang bexp fuel dbenv fenv nenv = Some b) /\
      (args_Imp_Lang args dbenv fenv nenv dbenv' ->
       exists fuel, eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv').
Proof.
  intros.
  pose proof really_adequate_backward_i as UGLY.
  destruct UGLY as [iUgly [aUgly [bUgly argsUgly]]].
  split; [| split;  [| split ]].
  - eapply iUgly.
  - eapply aUgly.
  - eapply bUgly.
  - eapply argsUgly.
Qed.


Ltac asapply H :=
  apply H; try assumption.

Lemma imp_lang_trick_adequacy :
  forall i aexp bexp dbenv fenv nenv s n b args dbenv',
    (i_Imp_Lang i dbenv fenv nenv s <->
       exists fuel, eval_fuel_Imp_Lang i fuel dbenv fenv nenv = Some s) /\
      (a_Imp_Lang aexp dbenv fenv nenv n <->
         exists fuel, eval_aImp_Lang aexp fuel dbenv fenv nenv = Some n) /\
      (b_Imp_Lang bexp dbenv fenv nenv b <->
         exists fuel, eval_bImp_Lang bexp fuel dbenv fenv nenv = Some b) /\
      (args_Imp_Lang args dbenv fenv nenv dbenv' <->
         exists fuel, eval_args_Imp_Lang args fuel dbenv fenv nenv = Some dbenv').
Proof.
  intros.
  pose proof (really_adequate_backward_i_human_version i aexp bexp dbenv fenv nenv s n b args dbenv')  as BACK.
  pose proof really_adequate_forward_i as FOR.
  destruct BACK as [iBACK [aBACK [bBACK argsBACK]]].
  split; [| split; [|split]]; (split; [| intros; destruct H; specialize (FOR x i aexp bexp dbenv fenv nenv s n b args dbenv')]).
  - exact iBACK.
  - destruct FOR as [iFOR _].
    asapply iFOR.
  - exact aBACK.
  - destruct FOR as [_ [aFOR _]].
    asapply aFOR.
  - exact bBACK.
  - destruct FOR as [_ [_ [bFOR _]]].
    asapply bFOR.
  - exact argsBACK.
  - destruct FOR as (_ & _ & _ & argsFOR).
    asapply argsFOR.
Qed.

    
  
  
