From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang ProofCompAutoAnother Imp_LangLogHoare FunctionWellFormed Imp_LangHoareWF StackLangTheorems.

Local Open Scope list_scope.
Local Open Scope string_scope.

Definition fraction_addition_numerator_fun_body :=
  (* a / b + c / d *)
  let a := PARAM_Imp_Lang 0  in
  let b := PARAM_Imp_Lang 1 in
  let c := PARAM_Imp_Lang 2 in
  let d := PARAM_Imp_Lang 3 in
  ASSIGN_Imp_Lang "ret" (PLUS_Imp_Lang (APP_Imp_Lang "mult" (a :: d :: nil)) (APP_Imp_Lang "mult" (c :: b :: nil))).

(* Helper for making functions, so don't have to use annoying record syntax *)
Definition make_fun_imp_lang (name: ident) (args: nat) (body: imp_Imp_Lang) (ret: ident) :=
  {| Imp_LangTrickLanguage.Name := name
  ; Imp_LangTrickLanguage.Args := args
  ; Imp_LangTrickLanguage.Body := body
  ; Ret := ret |}.

Definition fraction_addition_numerator_fun :=
  make_fun_imp_lang "frac_add_numerator" 4 fraction_addition_numerator_fun_body "ret".

Definition fraction_subtraction_numerator_body :=
  let a := PARAM_Imp_Lang 0 in
  let b := PARAM_Imp_Lang 1 in
  let c := PARAM_Imp_Lang 2 in
  let d := PARAM_Imp_Lang 3 in
  ASSIGN_Imp_Lang "ret" (MINUS_Imp_Lang (APP_Imp_Lang "mult" (a :: d :: nil)) (APP_Imp_Lang "mult" (c :: b :: nil))).

Definition fraction_subtraction_numerator_fun :=
  make_fun_imp_lang "frac_sub_numerator" 4 fraction_subtraction_numerator_body "ret".

Definition fraction_addition_denominator_fun_body :=
  (* a / b + c / d *)
  let b := PARAM_Imp_Lang 0 in
  let d := PARAM_Imp_Lang 1 in
  ASSIGN_Imp_Lang "ret" (APP_Imp_Lang "mult" (b :: d :: nil)).

Definition fraction_addition_denominator_fun :=
  make_fun_imp_lang "frac_add_denominator" 2 fraction_addition_denominator_fun_body "ret".

Fixpoint imp_seq_ifier (cmds: list imp_Imp_Lang) : imp_Imp_Lang :=
  match cmds with
  | nil => SKIP_Imp_Lang
  | cmd :: cmds' =>
      match imp_seq_ifier cmds' with
      | SKIP_Imp_Lang => cmd
      | second_cmd => SEQ_Imp_Lang cmd second_cmd
      end
  end.

From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.

Fixpoint imp_fenv_ify (funs : list fun_Imp_Lang) : fun_env :=
  match funs with
  | nil => init_fenv
  | f :: funs' =>
      update (Name f) f (imp_fenv_ify funs')
  end.

Lemma exp_aexp_wrapper' : 
   forall fenv dbenv nenv a1 a2 n1 n2 n, 
      fenv "mult" = prod_function -> 
      fenv "exp" = exp_function -> 
      a_Imp_Lang a1 dbenv fenv nenv n1 ->
      a_Imp_Lang a2 dbenv fenv nenv n2 ->
      a_Imp_Lang (APP_Imp_Lang "exp" (a1::a2::nil)) dbenv fenv nenv n ->
      n = n2^n1. 
Proof.
  intros. pose proof (EXP := exp_aexp_wrapper).
  specialize (EXP fenv dbenv nenv a1 a2 n1 n2 H H0 H1 H2).
  pose proof (DET := a_Imp_Lang_deterministic).
  specialize (DET _ _ _ _ _ _ H3 EXP).
  assumption.
Qed.

Lemma mult_aexp_wrapper' :
  forall fenv dbenv nenv a1 a2 n1 n2 n, 
    fenv "mult" = prod_function -> 
    a_Imp_Lang a1 dbenv fenv nenv n1 ->
    a_Imp_Lang a2 dbenv fenv nenv n2 ->
    a_Imp_Lang (APP_Imp_Lang "mult" (a1::a2::nil)) dbenv fenv nenv n ->
    n = n1 * n2.
Proof.
  intros. pose proof (MULT := mult_aexp_wrapper).
  specialize (MULT fenv dbenv nenv a1 a2 n1 n2 H H0 H1).
  pose proof (DET := a_Imp_Lang_deterministic).
  specialize (DET _ _ _ _ _ _ H2 MULT).
  assumption.
Qed.

Definition construct_eq_imp (n1 n2: nat) :=
  andb (Nat.leb n1 n2) (Nat.leb n2 n1).

Definition construct_neq_imp (n1 n2: nat) :=
  negb (construct_eq_imp n1 n2).

Definition construct_lt_imp (n1 n2: nat) :=
  andb (Nat.leb n1 n2) (construct_neq_imp n1 n2).


(* Ltac hl_imp_lang_wf_assign_helper := *)
(*   match goal with *)
(*   | [ |- hl_Imp_Lang_wf ?fenv ?func_list ?idents ?num_args ?d ?d' (ASSIGN_Imp_Lang ?x ?a) ?facts (hl_Imp_Lang_assign ?d'' ?facts' ?fenv' ?x' ?a') ] => *)
(*       let Hsubst := fresh "Hsubst" in *)
(*       let Heq := fresh "Heq" in *)
(*       assert (Hsubst : Imp_LangLogSubst.subst_AbsEnv x a d' = d) by reflexivity || enough (Hsubst : Imp_LangLogSubst.subst_AbsEnv x a d' = d); *)
(*       assert (Heq : ASSIGN_Imp_Lang x a = ASSIGN_Imp_Lang x' a') by reflexivity || enough (Heq: ASSIGN_Imp_Lang x a = ASSIGN_Imp_Lang x' a'); *)
(*       pose proof (Hsubstrefl := Imp_LangLogPropDec.UIP_AbsEnv_refl _ Hsubst); *)
(*       pose proof (Heqrefl := UIP_imp_refl _ Heq); *)
(*       eapply HLImp_LangWFAssign with (Heq := Heq) (Hsubst := Hsubst); *)
(*       try rewrite Hsubstrefl; try rewrite Heqrefl *)
(*   end. *)

(* Ltac hl_imp_lang_wf_seq_helper := *)
(*    match goal with *)
(*    | [ |- hl_Imp_Lang_wf _ _ _ _ _ _ _ _ ?hl' ] =>  *)
(*       eapply HLImp_LangWFSeq with (Heq := eq_refl) (hlseq := hl') *)
(*    end.  *)

Ltac hl_Imp_Lang_assign_helper :=
  match goal with
  | [ |- hl_Imp_Lang ?R (ASSIGN_Imp_Lang ?x ?e) _ _ _ ] =>
      match R with
      | context P [ e ] =>
          let R' := context P [ (VAR_Imp_Lang x) ] in
          replace R with
            (Imp_LangLogSubst.subst_AbsEnv x e R') by reflexivity;
          econstructor
      | _ =>
          replace R with
          (Imp_LangLogSubst.subst_AbsEnv x e R) by reflexivity;
          econstructor
      end
  end.



Lemma frac_add_numerator_wrapper : 
  forall fenv dbenv nenv a1 a2 a3 a4 n1 n2 n3 n4 n, 
  fenv "mult" = prod_function ->
  fenv "frac_add_numerator" = fraction_addition_numerator_fun -> 
  a_Imp_Lang a1 dbenv fenv nenv n1 ->
  a_Imp_Lang a2 dbenv fenv nenv n2 ->
  a_Imp_Lang a3 dbenv fenv nenv n3 ->
  a_Imp_Lang a4 dbenv fenv nenv n4 ->
  a_Imp_Lang (APP_Imp_Lang "frac_add_numerator" (a1::a2::a3::a4::nil)) dbenv fenv nenv n
  ->
  n = (n1 * n4) + (n2 * n3).
Proof. 
  intros. invs H5. simpl in *. rewrite H0 in H11. invs H10. invs H16. invs H18. invs H20. 
  rewrite H0 in *. simpl in *.
  invs H11. invs H23. invs H15. rewrite H in *. simpl in *. invs H21. invs H30.
  invs H17. simpl in H27. invs H27.
  invs H26. simpl in H29. invs H29.    
  pose proof mult_aexp_wrapper' fenv (v3 :: v0 :: v1 :: v4 :: vals0) init_nenv (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 3) v3 v4 (nenv'' "y") H H17 H26 H15. rewrite H6 in *. 
  invs H25. rewrite H in *; simpl in *.
  invs H36. invs H42.
  invs H34. simpl in H39. invs H39.
  invs H38. simpl in H41. invs H41. 
  pose proof mult_aexp_wrapper' fenv (v3 :: v2 :: v :: v4 :: vals0) init_nenv (PARAM_Imp_Lang 2) (PARAM_Imp_Lang 1) v v2 (nenv''0 "y") H H34 H38 H25. rewrite H31 in *.
  rewrite update_same.
  assert (v3 = n1) by (erewrite a_Imp_Lang_deterministic;
  try exists; eassumption).
  rewrite H43.
  assert (v4 = n4) by (erewrite a_Imp_Lang_deterministic;
  try exists; eassumption).
  rewrite H45.
  assert (v2 = n2). 
  erewrite a_Imp_Lang_deterministic;
  try exists; eassumption; eassumption.
  rewrite H46.
  assert (v = n3) by (erewrite a_Imp_Lang_deterministic;
  try exists; eassumption).
  rewrite H47. lia.
Qed.   

Lemma frac_sub_numerator_wrapper : 
  forall fenv dbenv nenv a1 a2 a3 a4 n1 n2 n3 n4, 
  fenv "mult" = prod_function ->
  fenv "frac_sub_numerator" = fraction_subtraction_numerator_fun -> 
  a_Imp_Lang a1 dbenv fenv nenv n1 ->
  a_Imp_Lang a2 dbenv fenv nenv n2 ->
  a_Imp_Lang a3 dbenv fenv nenv n3 ->
  a_Imp_Lang a4 dbenv fenv nenv n4 ->
  a_Imp_Lang (APP_Imp_Lang "frac_sub_numerator" (a1::a2::a3::a4::nil)) dbenv fenv nenv ((n1 * n4) - (n3 * n2)).
Proof. 
  intros. econstructor; try rewrite H0 in *. reflexivity.
  simpl. reflexivity.
  repeat econstructor; try eassumption.  
  simpl. unfold fraction_subtraction_numerator_body.
  econstructor. econstructor.
  eapply mult_aexp_wrapper; try rewrite H0; try econstructor; simpl; try lia; 
  try exists; try rewrite H; reflexivity.     
  eapply mult_aexp_wrapper; try rewrite H0; try econstructor; simpl; try lia; 
  try exists; try rewrite H; reflexivity.
  simpl. apply update_same.       
Qed.   

Lemma frac_add_denominator_wrapper : 
  forall fenv dbenv nenv a1 a2 n1 n2, 
  fenv "mult" = prod_function ->
  fenv "frac_add_denominator" = fraction_addition_denominator_fun -> 
  a_Imp_Lang a1 dbenv fenv nenv n1 ->
  a_Imp_Lang a2 dbenv fenv nenv n2 ->
  a_Imp_Lang (APP_Imp_Lang "frac_add_denominator" (a1::a2::nil)) dbenv fenv nenv (n1 * n2).
Proof.
  intros. econstructor; try rewrite H0 in *. reflexivity.
  simpl. reflexivity.
  repeat econstructor; try eassumption.  
  simpl. unfold fraction_addition_denominator_fun_body.
  econstructor. 
  eapply mult_aexp_wrapper; try rewrite H0; try econstructor; simpl; try lia; 
  try exists; try rewrite H; reflexivity.     
  simpl. apply update_same.       
Qed.      


Section BackToNats.
      Local Open Scope nat_scope.

      Lemma frac_add_numerator_wrapper' :
        forall (fenv : string -> fun_Imp_Lang) (dbenv : list nat)
          (nenv : nat_env) (a1 a2 a3 a4 : aexp_Imp_Lang)
          (n1 n2 n3 n4 n : nat),
          fenv "mult" = prod_function ->
          fenv "frac_add_numerator" = fraction_addition_numerator_fun ->
          a_Imp_Lang a1 dbenv fenv nenv n1 ->
          a_Imp_Lang a2 dbenv fenv nenv n2 ->
          a_Imp_Lang a3 dbenv fenv nenv n3 ->
          a_Imp_Lang a4 dbenv fenv nenv n4 ->
          n = n1 * n4 + n2 * n3 ->
          a_Imp_Lang
            (APP_Imp_Lang "frac_add_numerator" (a1 :: a2 :: a3 :: a4 :: nil))
            dbenv fenv nenv n.
      Proof.
        intros. meta_smash; try rewrite H0. reflexivity. eassumption. eassumption. eassumption. eassumption. simpl. unfold fraction_addition_numerator_fun_body.
        econstructor. econstructor.
        eapply mult_aexp_wrapper; [ eassumption | try meta_smash .. ].
        eapply mult_aexp_wrapper; [ eassumption | try meta_smash .. ].
        unfold update. simpl. symmetry. rewrite H5. f_equal. rewrite Nat.mul_comm. reflexivity.
      Qed.

      Check frac_add_denominator_wrapper.

      Lemma frac_add_denominator_wrapper' :
        forall (fenv : string -> fun_Imp_Lang) (dbenv : list nat)
          (nenv : nat_env) (a1 a2 : aexp_Imp_Lang) 
          (n n1 n2 : nat),
          fenv "mult" = prod_function ->
          fenv "frac_add_denominator" = fraction_addition_denominator_fun ->
          a_Imp_Lang a1 dbenv fenv nenv n1 ->
          a_Imp_Lang a2 dbenv fenv nenv n2 ->
          n = n1 * n2 ->
          a_Imp_Lang (APP_Imp_Lang "frac_add_denominator" (a1 :: a2 :: nil))
                     dbenv fenv nenv n.
      Proof.
        intros. econstructor.
        eassumption. reflexivity. meta_smash. eassumption. eassumption.
        simpl. unfold fraction_addition_denominator_fun_body. econstructor. eapply mult_aexp_wrapper. eassumption. meta_smash. meta_smash.
        simpl. symmetry. unfold update. simpl. eassumption.
      Qed.

      Lemma frac_add_denominator_wrapper'' :
        forall (fenv : string -> fun_Imp_Lang) (dbenv : list nat)
          (nenv : nat_env) (a1 a2 : aexp_Imp_Lang) 
          (n n1 n2 : nat),
          fenv "mult" = prod_function ->
          fenv "frac_add_denominator" = fraction_addition_denominator_fun ->
          a_Imp_Lang a1 dbenv fenv nenv n1 ->
          a_Imp_Lang a2 dbenv fenv nenv n2 ->
          a_Imp_Lang (APP_Imp_Lang "frac_add_denominator" (a1 :: a2 :: nil))
                     dbenv fenv nenv n ->
          n = n1 * n2.
      Proof.
        intros.
        invc H3. rewrite H0 in *. simpl in H9. unfold fraction_addition_denominator_fun_body in H9. invc H9.
        eapply mult_aexp_wrapper' in H12; [ | eapply H | .. ].
        simpl. unfold update. simpl. eassumption.
        invs H12. invs H9. invs H16.
        invs H8. invs H20.
        repeat Imp_LangLogicHelpers.a_Imp_Lang_same.
        meta_smash.
        invs H8. invs H13.
        repeat Imp_LangLogicHelpers.a_Imp_Lang_same.
        all: meta_smash.
      Qed.
    End BackToNats.
