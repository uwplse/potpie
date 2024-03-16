From Coq Require Import Psatz Arith String List ZArith.
From Coq Require Import QArith_base.
From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang.
From Imp_LangTrick Require Import ImpExampleHelpers ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems Imp_LangLogProp LogicProp.
From Imp_LangTrick Require Import Imp_LangLogHoare ProofCompMod SeriesExample ProofCompilableCodeCompiler EnvToStackLTtoLEQ ProofCompCodeCompAgnosticMod NotTerribleBImpLangInversion StackLanguage SeriesHelperCompilation.

From Imp_LangTrick.Tactics Require Import SemanTactics MiscTactics.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.


Section DivisionByTwo.
  Let const n := CONST_Imp_Lang n.
  Let assign x' e' := ASSIGN_Imp_Lang x' e'.
  Let var x := VAR_Imp_Lang x.
  Let p k := PARAM_Imp_Lang k.

  (** This one does something fancy by first finding the the largest power oof two greater than the desired divisor. Then searches linearly between the second largest power and the desired divisor. *)
  Definition div2_body_fancy :=
    let p0 := PARAM_Imp_Lang 0 in
    IF_Imp_Lang
      (lt_Imp_Lang p0 (const 2))
      (assign "divisor" (const 0))
      (IF_Imp_Lang
         (eq_Imp_Lang p0 (const 2))
         (assign "divisor" (const 1))
         (imp_seq_ifier
            ((assign "p_new" (const 4))
               :: (assign "p_old" (const 2))
               :: (WHILE_Imp_Lang
                    (lt_Imp_Lang (var "p_new") p0)
                    (imp_seq_ifier
                       ((assign "p_old" (var "p_new"))
                          :: (assign "p_new" (APP_Imp_Lang "mult" ((var "p_old") :: (const 2) :: nil)))
                          :: nil)))
               :: (assign "divisor" (var "p_old"))
               :: (assign "div_times_two" (APP_Imp_Lang "mult" ((var "p_old") :: (const 2) :: nil)))
               :: (WHILE_Imp_Lang
                    (AND_Imp_Lang
                       (neq_Imp_Lang (var "div_times_two") p0)
                       (neq_Imp_Lang (PLUS_Imp_Lang (var "div_times_two") (const 1)) p0))
                    (imp_seq_ifier
                       ((assign "div_times_two" (PLUS_Imp_Lang (var "div_times_two") (const 2)))
                          :: (assign "divisor" (PLUS_Imp_Lang (var "divisor") (const 1)))
                          :: nil)))
               :: nil))).

  Definition div2_body_plain :=
    let p0 := PARAM_Imp_Lang 0 in
    imp_seq_ifier
      ((assign "divisor" (const 0))
         :: (assign "divisor_times_two" (const 0))
         :: (WHILE_Imp_Lang
              (AND_Imp_Lang
                 (neq_Imp_Lang
                    (var "divisor_times_two")
                    p0)
                 (neq_Imp_Lang
                    (PLUS_Imp_Lang
                       (var "divisor_times_two")
                       (const 1))
                    p0))
              (imp_seq_ifier
                 ((assign "divisor_times_two" (PLUS_Imp_Lang (var "divisor_times_two") (const 2)))
                    :: (assign "divisor" (PLUS_Imp_Lang (var "divisor") (const 1)))
                    :: nil)))
         :: nil).


  Definition div2_function :=
    make_fun_imp_lang "div2" 1 div2_body_plain "divisor".

  Let div2_fenv := imp_fenv_ify (div2_function :: nil).


  Let funapply f args := (APP_Imp_Lang f args).

  Lemma bexp_replace_result_value :
    forall b dbenv fenv nenv bval boolexpr (EQ : boolexpr = bval),
      b_Imp_Lang b dbenv fenv nenv bval <-> b_Imp_Lang b dbenv fenv nenv boolexpr.
  Proof.
    intros. split; intros.
    - rewrite EQ. assumption.
    - rewrite <- EQ. assumption.
  Qed.
  
  Example div2_4 :
    a_Imp_Lang (funapply "div2" ((const 4) :: nil)) nil div2_fenv init_nenv 2.
  Proof.
    smarter_a_Imp_Lang_econstructor.
    simpl. unfold div2_body_plain.
    simpl. smarter_imp_econstructor.
    econstructor.
    econstructor.
    all: try simpl; try lia; try reflexivity.
    eapply negb_false_iff. reflexivity. eapply negb_false_iff. reflexivity.
    simpl.
    eexists.
    split.
    - (* the sequence before *)
      smarter_imp_econstructor.
      smarter_a_Imp_Lang_econstructor.
    - smarter_imp_econstructor.
      all: try simpl; try lia; try reflexivity. eapply negb_false_iff. reflexivity. eapply negb_false_iff. reflexivity. simpl.
      eexists.
      split; smarter_imp_econstructor.
      smarter_a_Imp_Lang_econstructor.
      all: try simpl; try lia; try reflexivity. eapply negb_true_iff. reflexivity. eapply negb_false_iff. reflexivity. simpl. reflexivity.
    - unfold update. simpl. reflexivity.
  Qed.  
End DivisionByTwo.

Section SquareRootProgram.
  Let const n := CONST_Imp_Lang n.
  Let assign x' e' := ASSIGN_Imp_Lang x' e'.
  Let var x := VAR_Imp_Lang x.
  Let nary_mult :=
        fix n_ary_mult (arg1: aexp_Imp_Lang) (arg2: aexp_Imp_Lang) (args: list aexp_Imp_Lang): aexp_Imp_Lang :=
          match args with
          | nil =>
              APP_Imp_Lang "mult" (arg1 :: arg2 :: nil)
          | arg3 :: nil =>
              (APP_Imp_Lang "mult"
                            ((APP_Imp_Lang "mult" (arg1 :: arg2 :: nil))
                               :: arg3
                               :: nil))
          | arg3 :: arg4 :: args' =>
              (APP_Imp_Lang "mult"
                            ((APP_Imp_Lang "mult" (arg1 :: arg2 :: nil))
                               :: (n_ary_mult arg3 arg4 args')
                               :: nil))
          end.
  Let loop_condition a b epsilon_n epsilon_d x_expr y_expr :=
        let A := (nary_mult y_expr y_expr ((const a) :: (const epsilon_d) :: nil)) in
        let B := (nary_mult x_expr x_expr ((const b) :: (const epsilon_d) :: nil)) in
        let C := (nary_mult y_expr y_expr ((const b) :: (const epsilon_n) :: nil)) in
        OR_Imp_Lang
          (lt_Imp_Lang
             C
             (MINUS_Imp_Lang                B                A))
          (lt_Imp_Lang
             C
             (MINUS_Imp_Lang                A                B)).
  Let if_condition a b epsilon_d x_expr y_expr :=
        let A := (nary_mult y_expr y_expr ((const a) :: (const epsilon_d) :: nil)) in
        let B := (nary_mult x_expr x_expr ((const b) :: (const epsilon_d) :: nil)) in
        let C := (CONST_Imp_Lang 0) in
        (* (nary_mult y_expr y_expr ((const b) :: (const epsilon_n) :: nil)) in *)
        LEQ_Imp_Lang (MINUS_Imp_Lang A B) C.


  Definition square_root_program (a b epsilon_n epsilon_d: nat) :=
    (* let div2 expr := APP_Imp_Lang "div2" (expr :: nil) in *)
    imp_seq_ifier
      ((assign "x" (const a))
         :: (assign "y" (const (2 * b)))
         :: (assign "inc_n" (const a))
         :: (assign "inc_d" (const (2 * b)))
         :: (WHILE_Imp_Lang
              (loop_condition a b epsilon_n epsilon_d (var "x") (var "y"))
              ((IF_Imp_Lang
                  (if_condition a b epsilon_d (var "x") (var "y"))
                  (imp_seq_ifier ((assign "inc_d" (APP_Imp_Lang "mult" ((const 2) :: (var "inc_d") :: nil)))
                                    ::
                                    ((assign "x" (APP_Imp_Lang "frac_sub_numerator" ((var "x") :: (var "y") :: (var "inc_n") :: (var "inc_d") :: nil))))
                                    ::
                                    (assign "y" (APP_Imp_Lang "frac_add_denominator" ((var "y") :: (var "inc_d") :: nil)))
                                    ::
                                    nil
                  ))
                  (imp_seq_ifier ((assign "inc_d" (APP_Imp_Lang "mult" ((const 2) :: (var "inc_d") :: nil)))
                                    ::
                                    (assign "x" (APP_Imp_Lang "frac_add_numerator" ((var "x") :: (var "y") :: (var "inc_n") :: (var "inc_d") :: nil)))
                                    ::
                                    (assign "y" (APP_Imp_Lang "frac_add_denominator" ((var "y") :: (var "inc_d") :: nil)))
                                    ::
                                    nil
           )))))::nil).

  

  (** Calculates the square root of the rational number a/b *)
  (* Definition square_root_program (a b epsilon_n epsilon_d: nat) :=
    (* let div2 expr := APP_Imp_Lang "div2" (expr :: nil) in *)
    imp_seq_ifier
      ((assign "x" (const a))
         :: (assign "y" (const (2 * b)))
         :: (assign "inc_n" (const a))
         :: (assign "inc_d" (const (2 * b)))
         :: (WHILE_Imp_Lang
              (loop_condition a b epsilon_n epsilon_d (var "x") (var "y"))
              (imp_seq_ifier
                 ((assign "inc_d" (APP_Imp_Lang "mult" ((const 2) :: (var "inc_d") :: nil)))
                    :: (IF_Imp_Lang
                         (if_condition a b epsilon_d (var "x") (var "y"))
                         (assign "x" (APP_Imp_Lang "frac_sub_numerator" ((var "x") :: (var "y") :: (var "inc_n") :: (var "inc_d") :: nil)))
                         (assign "x" (APP_Imp_Lang "frac_add_numerator" ((var "x") :: (var "y") :: (var "inc_n") :: (var "inc_d") :: nil))))
                    :: (assign "y" (APP_Imp_Lang "frac_add_denominator" ((var "y") :: (var "inc_d") :: nil)))
                    (* :: (assign "y" (PLUS_Imp_Lang (var "y") (var "y"))) *)
                    :: nil)))
         :: nil). *)

  Let sqrt_funcs := (prod_function :: fraction_addition_denominator_fun :: fraction_addition_numerator_fun :: fraction_subtraction_numerator_fun :: nil).
  (* (div2_function :: prod_function :: nil). *)
  Let sqrt_fenv := imp_fenv_ify sqrt_funcs.

  Lemma imp_if :
    forall b i1 i2 dbenv nenv fenv nenv' bval,
      b_Imp_Lang b dbenv fenv nenv bval ->
      (if bval then i_Imp_Lang i1 dbenv fenv nenv nenv' else i_Imp_Lang i2 dbenv fenv nenv nenv') ->
      i_Imp_Lang (IF_Imp_Lang b i1 i2) dbenv fenv nenv nenv'.
  Proof.
    intros. destruct bval.
    - eapply Imp_Lang_if_true; eassumption.
    - eapply Imp_Lang_if_false; eassumption.
  Qed.

  Lemma imp_while :
    forall b i dbenv nenv fenv nenv' bval,
      b_Imp_Lang b dbenv fenv nenv bval ->
      (if bval then (exists nenv'', i_Imp_Lang i dbenv fenv nenv nenv'' /\ i_Imp_Lang (WHILE_Imp_Lang b i) dbenv fenv nenv'' nenv')
       else nenv = nenv') ->
      i_Imp_Lang (WHILE_Imp_Lang b i) dbenv fenv nenv nenv'.
  Proof.
    intros. destruct bval.
    - destruct H0.
      destruct H0.
      eapply Imp_Lang_while_step; eassumption.
    - subst. eapply Imp_Lang_while_done. eassumption.
  Qed.
  
  
  Example square_root16 :
    exists nenv, i_Imp_Lang (square_root_program 16 1 1 3) nil sqrt_fenv init_nenv nenv.
  Proof.
    eexists. cbn.
    unfold assign. unfold if_condition. unfold loop_condition. unfold nary_mult.
    smarter_imp_econstructor.
    all: simpl; try reflexivity; try simpl. eapply negb_false_iff; reflexivity. eapply negb_false_iff; reflexivity.
    simpl.
    eexists; split; smarter_imp_econstructor; [ simpl; reflexivity | simpl; smarter_imp_econstructor | simpl; try reflexivity .. ].
    eapply negb_false_iff. reflexivity. eapply negb_false_iff. reflexivity.
  Qed.
  


  Definition square_root_invariant_prop := 
    (* fun x => fun y => fun a => fun b => fun inc_n => fun inc_d => *)

    fun lst =>
      let x := (List.nth 0 lst Nat.zero) in 
      let y := (List.nth 1 lst Nat.zero) in 
      let a := (List.nth 2 lst Nat.zero) in 
      let b := (List.nth 3 lst Nat.zero) in 
      let inc_n := (List.nth 4 lst Nat.zero) in
      let inc_d := (List.nth 5 lst Nat.zero) in
      (* this term is (x/y + inc_n/inc_d)^2 - i.e.
      (x^2 + 2(inc_n)x + inc_n^2)/ (y^2)(inc_d^2). 
      multiplying through all of the denominators it becomes
      (x^2)(inc_d^2)b + (y^2)(inc_n^2)b + 2bxy(inc_n)(inc_d) 
      where the b's come from the other side of the quality*)

      (* (x^2)(inc_d^2)b *)
      (((b * x * x * inc_d * inc_d)  + 
          (* (y^2)(inc_n^2)b *)
          (b * y * y * inc_n * inc_n)) + 
         (* 2bxy(inc_n)(inc_d) *)
         (b * x * y * inc_n * inc_d * 2) 
       >= 
         (* a/b defractionalized into
      a(inc_d^2)y^2 *)
         (a * inc_d * inc_d * y * y)) 

      /\

        (* this term is (x/y - inc_n/inc_d)^2 - i.e.
      (x^2 + 2(inc_n)x + inc_n^2)/ (y^2)(inc_d^2). 
      multiplying through all of the denominators it becomes
      (x^2)(inc_d^2)b + (y^2)(inc_n^2)b - 2bxy(inc_n)(inc_d) 
      where the b's come from the other side of the quality*)

        (* (x^2)(inc_d^2)b *)
        ((((b * x * x * inc_d * inc_d) + 
             (* (y^2)(inc_n^2)b *)
             (b * y * y * inc_n * inc_n)) 
          (* - 2bxy(inc_n)(inc_d)  *)
          - (b * x * y * inc_n * inc_d * 2)) 
         <= 
           (* a/b defractionalized into
      a(inc_d^2)y^2 *)
           (a * inc_d * inc_d * y * y))
      /\
        a < b
  . 

  Definition square_root_invariant :=
    fun a => fun b =>
      AbsEnvLP (Imp_Lang_lp_arith (NaryProp _ _ square_root_invariant_prop ((VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::(CONST_Imp_Lang a)::(CONST_Imp_Lang b)::(VAR_Imp_Lang "inc_n")::(VAR_Imp_Lang "inc_d")::nil))). 

  (* Wrapper for backwards reasoning: *)
  Definition hl_seq P Q R fact_env fenv i1 i2 C2 C1 :=
    hl_Imp_Lang_seq P Q R fact_env fenv i1 i2 C1 C2.

  Definition sqrt_facts (a b epsilon_n epsilon_d: nat) : implication_env := 
    (atrueImp_Lang (if_condition a b epsilon_d (var "x") (var "y"))
                   (atrueImp_Lang
                      (loop_condition a b epsilon_n epsilon_d (var "x") (var "y"))
                      (square_root_invariant a b)),
      Imp_LangLogSubst.subst_AbsEnv "inc_d"
                                    (APP_Imp_Lang "mult" (const 2 :: var "inc_d" :: nil))
                                    (Imp_LangLogSubst.subst_AbsEnv "x"
                                                                   (APP_Imp_Lang "frac_sub_numerator"
                                                                                 (var "x" :: var "y" :: var "inc_n" :: var "inc_d" :: nil))
                                                                   (Imp_LangLogSubst.subst_AbsEnv "y"
                                                                                                  (APP_Imp_Lang "frac_add_denominator"
                                                                                                                (var "y" :: var "inc_d" :: nil))
                                                                                                  (square_root_invariant a b))))::
                                                                                                                                nil.



  Let square_root_precondition (a b epsilon_n epsilon_d : nat) (result_n result_d: aexp_Imp_Lang) :=
        AbsEnvLP
          (Imp_Lang_lp_arith
             (BinaryProp _ _
                         (fun rn_val rd_val =>
                            rn_val = a /\ rd_val = b /\ b <> 0 /\ epsilon_n <> 0 /\ epsilon_d <> 0)
                         result_n result_d)).


  Definition sqrt_postcond_prop a b epsilon_n epsilon_d := 
    fun x => fun y => 
      let A := y * y * a * epsilon_d in
      let B := x * x * b * epsilon_d in
      let C := y * y * b * epsilon_n in
      (C >= (B - A) /\ C >= (A - B)).

  Definition sqrt_postcond a b epsilon_n epsilon_d := 
    AbsEnvLP
      (Imp_Lang_lp_arith
         (BinaryProp _ _ (sqrt_postcond_prop a b epsilon_n epsilon_d)
                     (VAR_Imp_Lang "x")
                     (VAR_Imp_Lang "y"))).


  Definition sqrt_facts'' (a b epsilon_n epsilon_d : nat) :  implication_env := 
    (afalseImp_Lang
       (loop_condition a b epsilon_n epsilon_d (var "x") (var "y")) 
       (AbsEnvLP
          (Imp_Lang_lp_arith (TrueProp _ _ ))), sqrt_postcond a b epsilon_n epsilon_d)
      ::
      (atrueImp_Lang (if_condition a b epsilon_d (var "x") (var "y"))
                     (atrueImp_Lang
                        (loop_condition a b epsilon_n epsilon_d (var "x") (var "y"))
                        (AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)))), 
        (AbsEnvLP
           (Imp_Lang_lp_arith (TrueProp _ _ ))))
      ::
      (afalseImp_Lang (if_condition a b epsilon_d (var "x") (var "y"))
                      (atrueImp_Lang
                         (loop_condition a b epsilon_n epsilon_d (var "x") (var "y"))
                         (AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)))), 
        (AbsEnvLP
           (Imp_Lang_lp_arith (TrueProp _ _ ))))
      ::
      nil. 

  Lemma implication : 
    forall a b epsilon_n epsilon_d, 
      aimpImp_Lang
        (afalseImp_Lang
           (loop_condition a b epsilon_n epsilon_d (var "x") (var "y"))
           (AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang))))
        (sqrt_postcond a b epsilon_n epsilon_d) series_fenv.
  Proof.  

    intros.
    unfold aimpImp_Lang. intros.
    unfold loop_condition in H. unfold lt_Imp_Lang in H.  unfold neq_Imp_Lang in H.  unfold eq_Imp_Lang in H. AbsEnv_rel_inversion.
    eapply mult_aexp_wrapper' in A5, H7, H16; [ | try reflexivity; smarter_imp_econstructor; try reflexivity .. ].
    subst n17 n10 n4.
    unfold sqrt_postcond.
    unfold sqrt_postcond_prop.
    econstructor; econstructor; econstructor; try smarter_a_Imp_Lang_econstructor.
    symmetry in H_or.
    rewrite Bool.orb_false_iff in H_or.
    destruct H_or as (P1, P2).
    rewrite Bool.andb_false_iff in P1, P2.    
    destruct P1; destruct P2.
    - rewrite leb_iff_conv in H, H0.
      split; lia. 
    - rewrite Bool.negb_false_iff in H0.
      rewrite Bool.andb_true_iff in H0. destruct H0.
      rewrite leb_iff_conv in H.
      eapply leb_complete in H0.
      eapply leb_complete in H1.
      split; lia. 
    - rewrite leb_iff_conv in H0.
      rewrite Bool.negb_false_iff in H.
      rewrite Bool.andb_true_iff in H. destruct H.
      eapply leb_complete in H.
      eapply leb_complete in H1.
      split; lia.
    - rewrite Bool.negb_false_iff in H.
      rewrite Bool.andb_true_iff in H. destruct H.
      rewrite Bool.negb_false_iff in H0.
      rewrite Bool.andb_true_iff in H0. destruct H0.
      eapply leb_complete in H.
      eapply leb_complete in H1.
      eapply leb_complete in H0.
      eapply leb_complete in H2.
      split; lia. 
  Qed. 

  Definition hl_pre_nice P Q P' c n fact_env fenv nth aimp hlPQ :=
    hl_Imp_Lang_consequence_pre P Q P' c n fact_env fenv hlPQ nth aimp.


  Definition hl_post_nice P Q Q' c n fact_env fenv nth aimp hlPQ :=
    hl_Imp_Lang_consequence_post P Q Q' c n fact_env fenv hlPQ nth aimp.

  Lemma anything_implies_true_prop :
    forall (A: AbsEnv) (fenv: fun_env),
      aimpImp_Lang
        A
        (AbsEnvLP (Imp_Lang_lp_arith (TrueProp nat aexp_Imp_Lang)))
        fenv.
  Proof.
    unfold aimpImp_Lang. intros. repeat econstructor.
  Qed.
  
  Lemma sqrt_triple : 
    forall a b epsilon_n epsilon_d, 
      hl_Imp_Lang (AbsEnvLP
                     (Imp_Lang_lp_arith (TrueProp _ _ )))
                  (square_root_program a b epsilon_n epsilon_d)
                  (sqrt_postcond a b epsilon_n epsilon_d) (sqrt_facts'' a b epsilon_n epsilon_d) series_fenv.
  Proof.
    intros.
    repeat eapply hl_seq; unfold assign; simpl.
    - eapply hl_post_nice with (n := 0); try reflexivity.
      + apply implication.
      + eapply hl_Imp_Lang_while. econstructor.
        * econstructor.
          -- hl_Imp_Lang_assign_helper.
          -- eapply hl_seq.
             ++ econstructor.
             ++ eapply hl_pre_nice with (n := 1); try reflexivity.
                ** eapply anything_implies_true_prop.
                ** hl_Imp_Lang_assign_helper.
        * eapply hl_pre_nice with (n := 2); try reflexivity.
          -- eapply anything_implies_true_prop.
          -- repeat (eapply hl_seq; try hl_Imp_Lang_assign_helper).
    - econstructor.
    - econstructor.
    - econstructor.
    - hl_Imp_Lang_assign_helper.
  Defined.

  (* Print sqrt_triple. *)




  
  
  
  Section WithZScope.
    Local Open Scope Z_scope.
    Let nat2z := Z.of_nat.
    (* Want: |a/b - rn^2/rd^2| < epsilon_n/epsilon_d
     *       - epsilon_n / epsilon_d < a / b - rn^2 / rd^2 < epsilon_n / epsilon_d
     *       - epsilon_n / epsilon_d + rn^2 / rd^2 < a / b < epsilon_n / epsilon_d + rn^2 / rd^2
     *       - rd^2 * epsilon_n / epsilon_d  + rn^2 < rd^2 * a / b < rd^2 epsilon_n / epsilon_d + rn^2
     *       - rd^2 * epsilon_n + rn^2 * epsilon_d < rd^2 * epsilon_d * a / b < rd^2 epsilon_n + rn^2 * epsilon_d
     *       - rd^2 * b * epsilon_n + rn^2 * b * epsilon_d < rd^2 * a * epsilon_d < rd^2 * b * epsilon_n + rn^2 * b * epsilon_d
     *         |__________________|   |__________________|   |__________________|   |__________________|   |__________________|
     *                  B                      A                      C                      B                       A
     *)
    
    Let square_root_postcondition (a b epsilon_n epsilon_d : nat) (result_n result_d: aexp_Imp_Lang) :=
          AbsEnvLP
            (Imp_Lang_lp_arith
               (BinaryProp _ _
                           (fun rn_val rd_val =>
                              let zrn := nat2z rn_val in
                              let zrd := nat2z rd_val in
                              let zen := nat2z epsilon_n in
                              let zed := nat2z epsilon_d in
                              let za := nat2z a in
                              let zb := nat2z b in
                              let B := (zrd ^ 2) * zb * zen in
                              let A := (zrn ^ 2) * zb * zed in
                              let C := (zrd ^ 2) * za * zed in
                              (- B) + A < C < B + A)
                           result_n result_d)).


    (* Want: (x/y + inc_n / inc_d)^2 >= a/b /\ (x/y - inc_n / inc_d)^2 <= a/b 
     *       x^2/y^2 + 2 * x * inc_n / (y * inc_d) inc_n^2/inc_d^2 >= a/b
     *       b * x^2 / y^2 + 2 * b * x * inc_n / (y * inc_d) + b * inc_n^2 / inc_d^2 >= a
     *       b * x^2 + 2 * b * x * y * inc_n / inc_d + b * y^2 inc_n^2 / inc_d^2 >= a * y^2
     *       b * x^2 * inc_d^2 + 2 * b * x * y * inc_n * inc_d + b * y^2 * inc_n^2 >= a * y^2 * inc_d^2
     * and
     *       b * x^2 * inc_d^2 - 2 * b * x * y * inc_n * inc_d + b * y^2 * inc_n^2 >= a * y^2 * inc_d^2 *)

    (* Let square_root_invariant (a b epsilon_n epsilon_d : nat) (result_n result_d inc_n inc_d : aexp_Imp_Lang) := *)
    (*       let A := (nary_mult result_d result_d ((const a) :: (const epsilon_d) :: nil)) in *)
    (*       let B := (nary_mult result_n result_n ((const b) :: (const epsilon_d) :: nil)) in *)
    (*       let C := (nary_mult result_d result_d ((const b) :: (const epsilon_n) :: nil)) in *)
    (*       let A' nrd := (nrd * nrd * a * epsilon_d)%nat in *)
    (*       let B' nrn := (nrn * nrn * b * epsilon_d)%nat in *)
    (*       let C' nrd := (nrd * nrd * b * epsilon_n)%nat in *)
    (*       AbsEnvLP *)
    (*         (Imp_Lang_lp_arith *)
    (*            (BinaryProp _ _ *)
    (*                        ())) *)

    
    
    Definition sqrt_facts' a b epsilon_n epsilon_d : implication_env :=
      (square_root_precondition a b epsilon_n epsilon_d
                                (const a) (const b),
        AbsEnvAnd
          (square_root_precondition a b epsilon_n epsilon_d
                                    (const a) (const b))
          (AbsEnvLP
             (Imp_Lang_lp_arith
                (UnaryProp nat aexp_Imp_Lang
                           (fun xval : nat =>
                              (xval + xval)%nat = a \/
                                (xval + xval + 1)%nat = a)
                           (APP_Imp_Lang "div2" (const a :: nil))))))
        :: nil.



    (* Lemma square_root_hoare_triple :
      forall a b epsilon_n epsilon_d,
        hl_Imp_Lang (square_root_precondition a b epsilon_n epsilon_d (const a) (const b))
                    (square_root_program a b epsilon_n epsilon_d)
                    (square_root_postcondition a b epsilon_n epsilon_d (var "x") (var "y"))
                    (sqrt_facts' a b epsilon_n epsilon_d)
                    series_fenv.
    Proof.
      intros. unfold square_root_program. simpl.
      eapply hl_Imp_Lang_seq.
      - eapply hl_Imp_Lang_consequence_pre with (P :=
                                     AbsEnvAnd (square_root_precondition a b epsilon_n epsilon_d (const a) (const b))
                                               (AbsEnvLP (Imp_Lang_lp_arith (UnaryProp _ _ (fun xval => (xval + xval = a)%nat \/ (xval + xval + 1 = a)%nat) (APP_Imp_Lang "div2" (const a :: nil)))))) (n := 0%nat).
        (* unfold const. *)
        + unfold assign.
          hl_Imp_Lang_assign_helper.
        + reflexivity.
        + admit.
      - eapply hl_Imp_Lang_seq.
        + unfold assign. hl_Imp_Lang_assign_helper.
        + eapply hl_Imp_Lang_consequence_pre.
    Admitted. *)

    Definition sqrt_postcond' a b epsilon_n epsilon_d := square_root_postcondition a b epsilon_n epsilon_d (var "x") (var "y").
  End WithZScope.

  Definition sqrt_program := square_root_program.
  Definition sqrt_precond a b epsilon_n epsilon_d := square_root_precondition a b epsilon_n epsilon_d (const a) (const b).
  Definition square_root_fenv := series_fenv.
  Definition square_root_facts := sqrt_facts.
  Definition square_root_funcs := sqrt_funcs.
  
End SquareRootProgram.
