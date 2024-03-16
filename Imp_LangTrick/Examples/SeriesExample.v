From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang.
From Imp_LangTrick Require Export ImpExampleHelpers.

Local Open Scope list_scope.
Local Open Scope string_scope.


(* want |\frac{1}{x-1} - \sum_{i=1}^n \frac{1}{x^i}| > \frac{delta_numerator}{delta_denominator}
 *      \frac{1}{x-1} > \frac{delta_numerator}{delta_denominator} + \sum_{i=1}^n \frac{1}{x^i}
 *      delta_denominator \frac{1}{x-1} > delta_numerator + delta_denominator \sum_{i=1}^n \frac{1}{x^i}
 *      delta_denominator > delta_numerator (x - 1) + delta_denominator (x - 1) \frac{result_numerator}{result_denominator}

 *      delta_denominator result_denominator > delta_numerator (x - 1) result_denominator + delta_denominator (x - 1) result_numerator
        |_______________|                      |_____________________|                      |_______________________|
                 a                                        c                                              b
*)
Ltac invc H := inversion H; subst; clear H.

Local Open Scope nat_scope.

Definition series_calculation_program (x delta_numerator delta_denominator : nat) :=
  let const n := CONST_Imp_Lang n in
  let assign x' e' := ASSIGN_Imp_Lang x' e' in
  let a := const delta_denominator in
  let b := const (Nat.mul delta_denominator (Nat.sub x 1)) in
  let c := const (Nat.mul delta_numerator (Nat.sub x 1)) in
  let var x' := VAR_Imp_Lang x' in
  let fraction_less_than rn rd := lt_Imp_Lang
                                    (PLUS_Imp_Lang
                                       (APP_Imp_Lang "mult" (rn :: b :: nil))
                                       (APP_Imp_Lang "mult" (rd :: c :: nil)))
                                    (APP_Imp_Lang "mult" (rd :: a :: nil)) in
  let cmds_list := (assign "x" (const x))
                     :: (assign "dn" (const delta_numerator)) (* TODO: Delete, not used, but will have to fix proofs *)
                     :: (assign "dd" (const delta_denominator)) (* TODO: Delete, not used, but will have to fix proofs *)
                     :: (assign "rn" (const 1)) (* result numerator *)
                     :: (assign "rd" (const x)) (* result denominator, we start with i = 1 *)
                     :: (assign "i" (const 2)) (* the exponent *)
                     :: (WHILE_Imp_Lang
                          (fraction_less_than (var "rn") (var "rd"))
                          (imp_seq_ifier
                             ((assign "d" (APP_Imp_Lang "exp" ((var "i") :: (var "x") :: nil)))
                                :: (assign "rn" (APP_Imp_Lang "frac_add_numerator" ((var "rn") :: (var "rd") :: (const 1) :: (var "d") :: nil)))
                                :: (assign "rd" (APP_Imp_Lang "frac_add_denominator" ((var "rd") :: (var "d") :: nil)))
                                :: (assign "i" (PLUS_Imp_Lang (var "i") (const 1)))
                                :: nil)))
                     :: nil in
  imp_seq_ifier cmds_list.

Eval compute in series_calculation_program.

From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.

Ltac invs H :=
  inversion H; subst. 



Section SeriesFenvAndFuncs.
  (* Avoid having to unfold a million things by using a Let in a section.  *)
  Let funcs_list := (prod_function :: exp_function :: fraction_addition_denominator_fun :: fraction_addition_numerator_fun ::fraction_subtraction_numerator_fun ::(init_fenv "id"):: nil).
 

  Definition series_funcs :=
    funcs_list.
  Definition series_fenv :=
    imp_fenv_ify funcs_list.
End SeriesFenvAndFuncs.

Example series_with_x_equal2 :
  exists nenv, i_Imp_Lang (series_calculation_program 2 1 4) nil series_fenv init_nenv nenv.
Proof.
  eexists. unfold series_calculation_program. meta_smash.
Admitted.

From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare.

From Coq Require Import ZArith.



Section SeriesHoareTriple.
  Let const x' := CONST_Imp_Lang x'.
  Let var x' := VAR_Imp_Lang x'.
  Let series_pre_first x dn dd x' dn' dd' := (AbsEnvLP (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang (fun a b c => 2 <= a /\ a = x /\ b <> 0 /\ b = dn /\ c <> 0 /\ c = dd) x' dn' dd'))).
  Let series_pre_second x rn rd i := (AbsEnvLP (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang (fun a b c => a = 1 /\ b = x /\ c = 2) rn rd i))).
  Let series_precondition x_nat dn_nat dd_nat x dn dd rn rd i :=
        (AbsEnvAnd
           (series_pre_first x_nat dn_nat dd_nat x dn dd)
           (series_pre_second x_nat rn rd i)).

  Definition series_loop_condition x delta_numerator delta_denominator :=
    let a := const delta_denominator in
    let b := const (Nat.mul delta_denominator (Nat.sub x 1)) in
    let c := const (Nat.mul delta_numerator (Nat.sub x 1)) in
    let fraction_less_than rn rd :=
      lt_Imp_Lang
        (PLUS_Imp_Lang
           (APP_Imp_Lang "mult" (rn :: b :: nil)) (APP_Imp_Lang "mult" (rd :: c :: nil)))
        (APP_Imp_Lang "mult" (rd :: a :: nil)) in
    fraction_less_than.
    

  Let series_postcondition x dn dd rn_expr rd_expr := AbsEnvLP (Imp_Lang_lp_arith (BinaryProp nat aexp_Imp_Lang (fun x1 x2 =>  dd * x2 <= dn * (x - 1) * x2 + dd * (x - 1) * x1) rn_expr rd_expr)).

  Let nat2z := Z.of_nat.

  Ltac hl_Imp_Lang_assign_helper :=
        match goal with
        | [ |- hl_Imp_Lang ?R (ASSIGN_Imp_Lang ?x ?e) _ _ _ ] =>
            match R with
            | context P [ e ] =>
                let R' := context P [ (var x) ] in
                replace R with
                  (Imp_LangLogSubst.subst_AbsEnv x e R') by reflexivity;
                econstructor
            | _ =>
                replace R with
                (Imp_LangLogSubst.subst_AbsEnv x e R) by reflexivity;
                econstructor
            end
        end.

  Local Open Scope Z_scope.
  
  Let series_loop_invariant x dd rn_expr rd_expr x_expr i_expr dd_expr :=
        AbsEnvLP
          (Imp_Lang_lp_arith
             (NaryProp
                nat aexp_Imp_Lang
                (fun args =>
                   match args with
                   | rn :: rd :: x' :: i :: dd' :: nil =>
                       let rnz := nat2z rn in
                       let rdz := nat2z rd in
                       let xz := nat2z x' in
                       let iz := nat2z i in
                       rnz * (Z.pow xz iz) - (rnz * (Z.pow xz (iz -1))) = rdz * (Z.pow xz (iz - 1)) - rdz /\ x' = x /\ 2 <= xz /\ 2 <= iz /\ dd' = dd /\ (dd <> 0)%nat
                   | _ => False
                   end)
                (rn_expr :: rd_expr :: x_expr :: i_expr :: dd_expr :: nil))).
  Local Open Scope imp_langtrick_scope.
  Let series_facts x dn dd: implication_env :=
        (series_precondition x dn dd (var "x") (var "dn") (var "dd") (var "rn") (var "rd") (var "i"),
          series_loop_invariant x dd (var "rn") (var "rd") (var "x") (var "i") (var "dd"))
          ::
          ((atrueImp_Lang
              (series_loop_condition x dn dd (var "rn") (var "rd"))
              (series_loop_invariant x dd (var "rn") (var "rd") 
                                     (var "x") (var "i") (var "dd"))),
            Imp_LangLogSubst.subst_AbsEnv
              "d" ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil)
              (Imp_LangLogSubst.subst_AbsEnv
                 "rn"
                 ("frac_add_numerator" @d VAR_Imp_Lang "rn" :: VAR_Imp_Lang "rd" :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil)
                 (AbsEnvLP
                    (Imp_Lang_lp_arith
                       (NaryProp nat aexp_Imp_Lang
                                 (fun args : list nat =>
                                    match args with
                                    | nil => False
                                    | rn :: nil => False
                                    | rn :: rd :: nil => False
                                    | rn :: rd :: x' :: nil => False
                                    | rn :: rd :: x' :: i :: nil => False
                                    | rn :: rd :: x' :: i :: dd' :: nil =>
                                        nat2z rn * nat2z x' ^ nat2z i - nat2z rn * nat2z x' ^ (nat2z i - 1) =
                                          nat2z rd * nat2z x' ^ (nat2z i - 1) - nat2z rd /\
                                          x' = x /\ 2 <= nat2z x' /\ 2 <= nat2z i /\ dd' = dd /\ dd <> 0%nat
                                    | rn :: rd :: x' :: i :: dd' :: _ :: _ => False
                                    end)
                                 ((VAR_Imp_Lang "rn")
                                    :: ("frac_add_denominator" @d VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil)
                                    :: VAR_Imp_Lang "x" :: (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1) :: VAR_Imp_Lang "dd" :: nil))))))
          :: (afalseImp_Lang
               (series_loop_condition x dn dd (var "rn") (var "rd"))
               (series_loop_invariant x dd (var "rn") (var "rd") (var "x") (var "i") (var "dd")),
              series_postcondition x dn dd (var "rn") (var "rd")) :: nil.


  Lemma invariant_still_holds_proof_general (x dn dd : nat)
        (nrd : nat)
        (nrn : nat)
        (nx : nat)
        (ni : nat)
        (INV : nat2z nrn * nat2z nx ^ nat2z ni -
                                        nat2z nrn * nat2z nx ^ (nat2z ni - 1) =
                 nat2z nrd * nat2z nx ^ (nat2z ni - 1) - nat2z nrd)
        (EQ_x : nx = x)
        (LEQx : 2 <= nat2z nx)
        (LEQi : 2 <= nat2z ni)
        (ndd : nat)
        (DD : ndd = dd /\ dd <> 0%nat):
    nat2z (nrn * nx ^ ni + (nrd + 0)) * nat2z nx ^ nat2z (ni + 1) -
                                                     nat2z (nrn * nx ^ ni + (nrd + 0)) * nat2z nx ^ (nat2z (ni + 1) - 1) =
      nat2z (nrd * nx ^ ni) * nat2z nx ^ (nat2z (ni + 1) - 1) -
                                           nat2z (nrd * nx ^ ni) /\
      nx = x /\
      2 <= nat2z nx /\ 2 <= nat2z (ni + 1) /\ ndd = dd /\ dd <> 0%nat.
  Proof.
    split; [ | split; [ | split;  [ | split ]]].
     - simpl. rewrite Nat.add_0_r.
      repeat rewrite Nat2Z.inj_add. repeat rewrite Nat2Z.inj_mul. repeat rewrite Nat2Z.inj_pow.
      simpl. fold (nat2z nrn). fold (nat2z nrd). fold (nat2z nx). fold (nat2z ni).
      rewrite <- Z.add_sub_assoc. simpl. rewrite Z.add_0_r. rewrite Z.add_1_r.
      remember (nat2z nrn) as rnz. remember (nat2z nx) as xz. remember (nat2z ni) as iz. remember (nat2z nrd) as rdz.
      rewrite Z.pow_succ_r.
      replace (rdz * xz ^ iz) with ((xz ^ iz) * rdz) by lia.
      rewrite <- Z.mul_assoc.
      replace (xz * xz ^ iz) with ((xz ^ iz) * xz) by lia.
      repeat rewrite <- Z.mul_sub_distr_l.
      remember (xz^iz) as x_to_i.
      replace (x_to_i * xz - x_to_i) with (x_to_i * xz - x_to_i * 1) by lia.
      rewrite <- Z.mul_sub_distr_l.
      rewrite Z.mul_assoc.
      replace ((rnz * x_to_i + rdz) * x_to_i * (xz - 1)) with (x_to_i * (rnz * x_to_i + rdz) * (xz - 1)) by lia.
      rewrite <- Z.mul_assoc.
      f_equal.
      rewrite Z.mul_add_distr_r.
      repeat rewrite Z.mul_sub_distr_l. repeat rewrite Z.mul_1_r.
      rewrite Z.add_sub_assoc.
      eapply Z.sub_cancel_r. subst x_to_i.
      replace (rnz * xz ^ iz * xz) with (rnz * xz * xz ^ iz) by lia.
      enough (exists j, iz = Z.succ j).
      destruct H. rewrite H.
      rewrite Z.pow_succ_r. repeat rewrite Z.mul_assoc.
      replace (rnz * xz) with (xz * rnz) by lia. replace (rdz * xz) with (xz * rdz) by lia.
      repeat rewrite <- Z.mul_assoc.
      rewrite <- Z.mul_sub_distr_l. rewrite <- Z.mul_add_distr_l. f_equal.
      rewrite H in INV. rewrite Z.sub_1_r in INV. rewrite Z.pred_succ in INV.
      rewrite <- Z.pow_succ_r. rewrite INV. rewrite Z.sub_add. reflexivity. lia. lia.

      assert (2 <= ni)%nat.
      {
        rewrite <- Nat2Z.id. fold (nat2z ni). rewrite <- Heqiz. lia.
      }
      destruct (ni) eqn:N.
      lia.
      exists (nat2z n). rewrite Heqiz.
      unfold nat2z. rewrite Nat2Z.inj_succ. reflexivity.
      lia.
    - assumption.
    - assumption.
    - 
      unfold nat2z. rewrite Nat2Z.inj_add. unfold nat2z in LEQi. lia.
    - assumption.
  Qed.

  

  Lemma invariant_still_holds_proof (x dn dd : nat)
        (dbenv : list nat)
        (nenv : nat_env)
        (INV : nat2z (nenv "rn") * nat2z (nenv "x") ^ nat2z (nenv "i") - nat2z (nenv "rn") * nat2z (nenv "x") ^ (nat2z (nenv "i") - 1) =
                 nat2z (nenv "rd") * nat2z (nenv "x") ^ (nat2z (nenv "i") - 1) - nat2z (nenv "rd"))
        (EQ_x : nenv "x" = x)
        (LEQx : 2 <= nat2z (nenv "x"))
        (LEQi : 2 <= nat2z (nenv "i"))
        (DD : nenv "dd" = dd /\ dd <> 0%nat) :
  nat2z (update "ret" (nenv "rn" * nenv "x" ^ nenv "i" + (nenv "rd" + 0))%nat init_nenv "ret") * nat2z (nenv "x") ^ nat2z (nenv "i" + 1) -
  nat2z (update "ret" (nenv "rn" * nenv "x" ^ nenv "i" + (nenv "rd" + 0))%nat init_nenv "ret") *
  nat2z (nenv "x") ^ (nat2z (nenv "i" + 1) - 1) =
  nat2z (update "ret" (nenv "rd" * nenv "x" ^ nenv "i")%nat init_nenv "ret") * nat2z (nenv "x") ^ (nat2z (nenv "i" + 1) - 1) -
  nat2z (update "ret" (nenv "rd" * nenv "x" ^ nenv "i")%nat init_nenv "ret") /\
    nenv "x" = x /\ 2 <= nat2z (nenv "x") /\ 2 <= nat2z (nenv "i" + 1) /\ nenv "dd" = dd /\ dd <> 0%nat.
  Proof.
    eapply invariant_still_holds_proof_general; eassumption.
  Qed.


  Lemma first_implication_proof_arithmetic_proof
        (x dn dd : nat)
        (nx : nat)
        (Hxleq : (2 <= nx)%nat)
        (Hx : nx = x)
        (ndn : nat)
        (Hdn_nonzero : ndn <> 0%nat)
        (Hdn : ndn = dn)
        (ndd : nat)
        (Hdd_nonzero : ndd <> 0%nat)
        (Hdd : ndd = dd)
        (nrn : nat)
        (Hrn : nrn = 1%nat)
        (nrd : nat)
        (Hrd : nrd = x)
        (ni : nat)
        (Hi : ni = 2%nat):
    nat2z nrn * nat2z nx ^ nat2z ni - nat2z nrn * nat2z nx ^ (nat2z ni - 1) =
      nat2z nrd * nat2z nx ^ (nat2z ni - 1) - nat2z nrd /\
      nx = x /\ 2 <= nat2z nx /\ 2 <= nat2z ni /\ ndd = dd /\ dd <> 0%nat.
  Proof.
    split; [ | split; [ | split; [ | split ]] ].
    - rewrite Hrd. rewrite Hrn. remember (nat2z 1) as z1. simpl in Heqz1.  rewrite Heqz1.  rewrite Z.mul_1_l.  rewrite Hi.
      rewrite Hx. remember (nat2z 2) as z2. simpl in Heqz2. rewrite Heqz2. rewrite Z.sub_1_r.
      remember (Z.pred 2) as p2.
      simpl in Heqp2. rewrite Heqp2. rewrite Z.pow_1_r. rewrite Z.mul_1_l. replace (nat2z x * nat2z x - nat2z x) with (nat2z x * ((nat2z x) ^ 1) - nat2z x) by lia. assert (Z.succ 0 = 1) by lia. rewrite <- H. rewrite <- Z.pow_succ_r.
      replace (Z.succ (Z.succ 0)) with 2 by lia.
      reflexivity. lia.
    - assumption.
    - assert (2 <= nat2z x).
      {
        eapply Nat2Z.inj_le in Hxleq.
        assert (2 = Z.of_nat 2) by lia.
        rewrite H. rewrite Hx in Hxleq. assumption.
      }
      rewrite Hx. assumption.
    - rewrite Hi. simpl. reflexivity.
    - split. assumption. rewrite <- Hdd. assumption.
  Qed.

  Lemma first_implication_proof :
    forall (x dn dd : nat),
      aimpImp_Lang (series_precondition x dn dd (var "x") (var "dn") (var "dd") (var "rn") (var "rd") (var "i"))
                   (series_loop_invariant x dd (var "rn") (var "rd") (var "x") (var "i") (var "dd")) series_fenv.
  Proof.
    {
        unfold series_precondition. unfold series_loop_invariant. unfold series_pre_first. unfold series_pre_second. unfold aimpImp_Lang. intros.
        
        invc H. invc H2. invc H6. invc H0. invc H1. invc H2. invc H0. invc H6. invc H7. invc H8. invc H5. invc H10. invc H11.
        destruct H9 as (Hxleq & Hx & Hdn_nonzero & Hdn & Hdd_nonzero & Hdd).
        destruct H12 as (Hrn & Hrd & Hi).
        econstructor. econstructor. econstructor; try meta_smash.
        repeat econstructor.
        simpl.
        eapply first_implication_proof_arithmetic_proof; eassumption.
    }
  Qed.

  Lemma second_implication_proof :
    forall (x dn dd : nat),
      aimpImp_Lang
        (atrueImp_Lang
           (series_loop_condition x dn dd (VAR_Imp_Lang "rn") (VAR_Imp_Lang "rd"))
       (series_loop_invariant x dd (var "rn") (var "rd") 
          (var "x") (var "i") (var "dd")))
    (Imp_LangLogSubst.subst_AbsEnv "d"
       ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil)
       (Imp_LangLogSubst.subst_AbsEnv "rn"
          ("frac_add_numerator" @d
           VAR_Imp_Lang "rn"
           :: VAR_Imp_Lang "rd"
              :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil)
          (AbsEnvLP
             (Imp_Lang_lp_arith
                (NaryProp nat aexp_Imp_Lang
                   (fun args : list nat =>
                    match args with
                    | nil => False
                    | rn :: nil => False
                    | rn :: rd :: nil => False
                    | rn :: rd :: x' :: nil => False
                    | rn :: rd :: x' :: i :: nil => False
                    | rn :: rd :: x' :: i :: dd' :: nil =>
                        nat2z rn * nat2z x' ^ nat2z i -
                        nat2z rn * nat2z x' ^ (nat2z i - 1) =
                        nat2z rd * nat2z x' ^ (nat2z i - 1) - nat2z rd /\
                        x' = x /\
                        2 <= nat2z x' /\
                        2 <= nat2z i /\ dd' = dd /\ dd <> 0%nat
                    | rn :: rd :: x' :: i :: dd' :: _ :: _ => False
                    end)
                   (VAR_Imp_Lang "rn"
                    :: ("frac_add_denominator" @d
                        VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil)
                       :: VAR_Imp_Lang "x"
                          :: (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1)
                             :: VAR_Imp_Lang "dd" :: nil)))))) series_fenv.
  Proof.
    simpl. unfold aimpImp_Lang. intros.
    (* Break up the abstract state, down to the constituent parts *)
    repeat match goal with
    | [ H: AbsEnv_rel _ _ _ _ |- _ ] =>
        invc H
           end.
    repeat match goal with
           | [ H: Imp_Lang_lp_rel _ _ _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: eval_prop_rel _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: eval_prop_args_rel _ _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: b_Imp_Lang _ _ _ _ _ |- _ ] =>
               invc H
           end.
    rewrite H1 in *.
    repeat match goal with
           | [ H: a_Imp_Lang (PLUS_Imp_Lang _ _ ) _ _ _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: a_Imp_Lang (APP_Imp_Lang "mult" _) _ _ _ _ |- _ ] =>
               eapply mult_aexp_wrapper' in H; [ | meta_smash .. ]
           end.
    repeat match goal with
           | [ H: a_Imp_Lang (var _) _ _ _ _ |- _ ] =>
               invc H
           end.
    destruct H5 as (INV & EQ_x & LEQx & LEQi & DD).
    
    econstructor. econstructor. econstructor. econstructor.
    {
      econstructor.
      - reflexivity.
      - reflexivity.
      - econstructor. econstructor. econstructor. econstructor. econstructor. econstructor. econstructor. meta_smash.
      econstructor; [ | econstructor ]. eapply exp_aexp_wrapper; try meta_smash.
      - simpl. unfold fraction_addition_numerator_fun_body.
        econstructor. econstructor; eapply mult_aexp_wrapper; meta_smash.
      - reflexivity.
    }
    econstructor.
    {
      econstructor. reflexivity. reflexivity. econstructor. econstructor. econstructor. econstructor; [ | econstructor ].
      eapply exp_aexp_wrapper; try meta_smash.
      simpl. unfold fraction_addition_denominator_fun_body. econstructor. eapply mult_aexp_wrapper; meta_smash.
      reflexivity.
    }
    econstructor. meta_smash. econstructor; meta_smash. econstructor; meta_smash. econstructor. 
    simpl. eapply invariant_still_holds_proof; eassumption.
    all: reflexivity.
  Qed.


  Lemma third_implication_proof_arithmetic_proof
        (x dn dd : nat)
        (nrd : nat)
        (nrn : nat)
        (nx : nat)
        (ni : nat)
        (INV : nat2z nrn * nat2z nx ^ nat2z ni -
                                        nat2z nrn * nat2z nx ^ (nat2z ni - 1) =
                 nat2z nrd * nat2z nx ^ (nat2z ni - 1) - nat2z nrd)
        (Hx : nx = x)
        (LEQx : 2 <= nat2z nx)
        (LEQi : 2 <= nat2z ni)
        (ndd : nat)
        (DD : ndd = dd /\ dd <> 0%nat)
        (H1 : ((nrn * (dd * (x - 1)) + nrd * (dn * (x - 1)) <=? nrd * dd)%nat &&
        negb
          ((nrn * (dd * (x - 1)) + nrd * (dn * (x - 1)) <=? nrd * dd)%nat &&
           (nrd * dd <=? nrn * (dd * (x - 1)) + nrd * (dn * (x - 1)))%nat))%bool =
       false):
    (dd * nrd <= dn * (x - 1) * nrd + dd * (x - 1) * nrn)%nat.
  Proof.
    eapply Bool.andb_false_iff in H1.
    rewrite Nat.add_comm. rewrite Nat.mul_comm.
    assert (2 <= x)%nat as LEQx_nat.
    {
      rewrite <- Nat2Z.id. fold (nat2z nx). rewrite <- Hx. unfold nat2z in LEQx. lia.
    }
    destruct H1.
    -- eapply Nat.leb_gt in H.
      rewrite Nat.add_comm.
       rewrite Nat.mul_assoc in H.
       lia.
    -- eapply Bool.negb_false_iff in H. eapply Bool.andb_true_iff in H. destruct H.
       eapply Nat.leb_le in H0.
       replace (dn * (x - 1) * nrd)%nat with (nrd* (dn * (x - 1)))%nat by lia.
       assert (nrd * dd <= dd * x * nrd)%nat.
       {
         rewrite Nat.mul_comm. induction x.
         lia. replace (dd * S x * nrd)%nat with (S x * dd * nrd)%nat by lia.
         destruct x.
         lia. destruct DD. rewrite <- H1 in H2. lia.
       }
       lia.
  Qed.
    

  Lemma third_implication_proof :
    forall (x dn dd : nat),
      aimpImp_Lang
        (afalseImp_Lang
           (series_loop_condition x dn dd (VAR_Imp_Lang "rn") (VAR_Imp_Lang "rd"))
           (series_loop_invariant x dd (var "rn") (var "rd") 
                                  (var "x") (var "i") (var "dd")))
        (series_postcondition x dn dd (var "rn") (var "rd")) series_fenv.
  Proof.
    unfold aimpImp_Lang. unfold series_loop_invariant. unfold series_loop_condition. unfold series_postcondition. intros.
    repeat match goal with
    | [ H: AbsEnv_rel _ _ _ _ |- _ ] =>
        invc H
           end.
    repeat match goal with
           | [ H: Imp_Lang_lp_rel _ _ _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: eval_prop_rel _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: eval_prop_args_rel _ _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: b_Imp_Lang _ _ _ _ _ |- _ ] =>
               invc H
           end.
    rewrite H1 in *.
    repeat match goal with
           | [ H: a_Imp_Lang (PLUS_Imp_Lang _ _ ) _ _ _ _ |- _ ] =>
               invc H
           end.
    repeat match goal with
           | [ H: a_Imp_Lang (APP_Imp_Lang "mult" _) _ _ _ _ |- _ ] =>
               eapply mult_aexp_wrapper' in H; [ | meta_smash .. ]
           end.
    repeat match goal with
           | [ H: a_Imp_Lang (var _) _ _ _ _ |- _ ] =>
               invc H
           end.
                    
    destruct H5 as (INV & Hx & LEQx & LEQi & DD).
    econstructor. econstructor. econstructor. meta_smash. meta_smash.
    remember (nenv "rd") as nrd. remember (nenv "rn") as nrn. remember (nenv "x") as nx. remember (nenv "i") as ni. remember (nenv "dd") as ndd.
    eapply third_implication_proof_arithmetic_proof; eassumption.
  Qed.

  Definition series_precond x dn dd := series_precondition x dn dd (const x) (const dn) (const dd) (const 1) (const x) (const 2).
  Definition series_postcond x dn dd := series_postcondition x dn dd (var "rn") (var "rd").
  Definition series_program_facts := series_facts.

  Lemma fact_cert :
    forall x dn dd,
      fact_env_valid (series_facts x dn dd) series_fenv.
  Proof.
    unfold fact_env_valid. unfold series_facts.
    (* unfold series_program_facts. *)
    intros.
    simpl in H. destruct H as [H1 | [H2 | [H3 | H4]]].
    - invc H1. eapply first_implication_proof.
    - invc H2. eapply second_implication_proof.
    - invc H3. eapply third_implication_proof.
    - invc H4.
  Qed.

  (* Convenience lemma for doing SEQ backwards, since
   * we like backwards reasoning more usually *)
  Lemma hl_Imp_Lang_seq_backwards :
    forall P Q R fact_env fenv i1 i2,
      hl_Imp_Lang R i2 Q fact_env fenv ->
      hl_Imp_Lang P i1 R fact_env fenv ->
      hl_Imp_Lang P (SEQ_Imp_Lang i1 i2) Q fact_env fenv.
  Proof.
    intros.
    eapply hl_Imp_Lang_seq; eassumption.
  Qed.

  (* Included for convenience when proving all the assumptions needed
   * for proof compilation *)
  Lemma second_implication_hoare_triple :
    forall (x dn dd: nat),
      hl_Imp_Lang
    (Imp_LangLogSubst.subst_AbsEnv "d"
       ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil)
       (Imp_LangLogSubst.subst_AbsEnv "rn"
          ("frac_add_numerator" @d
           VAR_Imp_Lang "rn"
           :: VAR_Imp_Lang "rd"
              :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil)
          (AbsEnvLP
             (Imp_Lang_lp_arith
                (NaryProp nat aexp_Imp_Lang
                   (fun args : list nat =>
                    match args with
                    | nil => False
                    | rn :: nil => False
                    | rn :: rd :: nil => False
                    | rn :: rd :: x' :: nil => False
                    | rn :: rd :: x' :: i :: nil => False
                    | rn :: rd :: x' :: i :: dd' :: nil =>
                        nat2z rn * nat2z x' ^ nat2z i -
                        nat2z rn * nat2z x' ^ (nat2z i - 1) =
                        nat2z rd * nat2z x' ^ (nat2z i - 1) - nat2z rd /\
                        x' = x /\
                        2 <= nat2z x' /\
                        2 <= nat2z i /\ dd' = dd /\ dd <> 0%nat
                    | rn :: rd :: x' :: i :: dd' :: _ :: _ => False
                    end)
                   (VAR_Imp_Lang "rn"
                    :: ("frac_add_denominator" @d
                        VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil)
                       :: VAR_Imp_Lang "x"
                          :: (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1)
                             :: VAR_Imp_Lang "dd" :: nil))))))
    ("d" <- ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil))
    (Imp_LangLogSubst.subst_AbsEnv "rn"
       ("frac_add_numerator" @d
        VAR_Imp_Lang "rn"
        :: VAR_Imp_Lang "rd"
           :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil)
       (Imp_LangLogSubst.subst_AbsEnv "rd"
          ("frac_add_denominator" @d
           VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil)
          (Imp_LangLogSubst.subst_AbsEnv "i"
             (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1)
             (series_loop_invariant x dd (var "rn") 
                (var "rd") (var "x") (var "i") (var "dd")))))
    (series_facts x dn dd) series_fenv.
  Proof.
    intros. econstructor.
  Defined.

  Lemma while_body_proof :
    forall (x dn dd: nat),
      hl_Imp_Lang
        (atrueImp_Lang
           (series_loop_condition x dn dd (VAR_Imp_Lang "rn") (VAR_Imp_Lang "rd"))
       (series_loop_invariant x dd (var "rn") (var "rd") 
          (var "x") (var "i") (var "dd")))
        ("d" <- ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil);;
         ("rn" <-
            ("frac_add_numerator" @d
                                  VAR_Imp_Lang "rn"
                                  :: VAR_Imp_Lang "rd" :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil);;
          ("rd" <-
             ("frac_add_denominator" @d
                                     VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil);;
           "i" <- (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1))))
        (series_loop_invariant x dd (var "rn") (var "rd") 
                               (var "x") (var "i") (var "dd")) (series_facts x dn dd) series_fenv.
  Proof.
    intros.
    econstructor; [ shelve | ].
    econstructor; [ shelve | ].
    econstructor; [ shelve | ].
    econstructor.
    Unshelve.
    1-4: shelve.
    econstructor.
    Unshelve.
    1-2: shelve.
    econstructor.
    Unshelve.
    eapply hl_Imp_Lang_consequence_pre with (n := 1%nat);
    [ eapply second_implication_hoare_triple | reflexivity | eapply second_implication_proof ].
  Defined.

  Lemma third_implication_hoare_triple :
    forall (x dn dd: nat),
      hl_Imp_Lang
        (series_loop_invariant x dd (var "rn") (var "rd") 
                               (var "x") (var "i") (var "dd"))
        (while
           (series_loop_condition x dn dd (var "rn") (var "rd"))
           loop "d" <- ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil);;
         ("rn" <-
            ("frac_add_numerator" @d
                                  VAR_Imp_Lang "rn"
                                  :: VAR_Imp_Lang "rd"
                                  :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil);;
          ("rd" <-
             ("frac_add_denominator" @d
                                     VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil);;
           "i" <- (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1))) done)
        (afalseImp_Lang
           (series_loop_condition x dn dd (var "rn") (var "rd"))
           (series_loop_invariant x dd (var "rn") (var "rd") 
                                  (var "x") (var "i") (var "dd"))) (series_facts x dn dd)
        series_fenv.
  Proof.
    (* Apply the while rule *)
    econstructor.
    eapply while_body_proof.
  Defined.

  Lemma first_implication_hoare_triple :
    forall (x dn dd : nat),
      hl_Imp_Lang
        (series_loop_invariant x dd (var "rn") (var "rd") 
                               (var "x") (var "i") (var "dd"))
        (while
           (series_loop_condition x dn dd (var "rn") (var "rd"))
           loop "d" <- ("exp" @d VAR_Imp_Lang "i" :: VAR_Imp_Lang "x" :: nil);;
         ("rn" <-
            ("frac_add_numerator" @d
                                  VAR_Imp_Lang "rn"
                                  :: VAR_Imp_Lang "rd"
                                  :: CONST_Imp_Lang 1 :: VAR_Imp_Lang "d" :: nil);;
          ("rd" <-
             ("frac_add_denominator" @d
                                     VAR_Imp_Lang "rd" :: VAR_Imp_Lang "d" :: nil);;
           "i" <- (VAR_Imp_Lang "i" +d CONST_Imp_Lang 1))) done)
        (series_postcondition x dn dd (var "rn") (var "rd"))
        (series_facts x dn dd) series_fenv.
  Proof.
    intros.
    eapply hl_Imp_Lang_consequence_post. shelve. shelve. shelve.
    Unshelve.
    shelve. eapply 2%nat. shelve.
    reflexivity. eapply third_implication_proof.
    Unshelve.
    eapply third_implication_hoare_triple.
  Defined.

  Lemma series_hoare_triple :
    forall (x dn dd: nat),
      hl_Imp_Lang (series_precondition x dn dd (const x) (const dn) (const dd) (const 1) (const x) (const 2)) (series_calculation_program x dn dd) (series_postcondition x dn dd (var "rn") (var "rd")) (series_facts x dn dd) series_fenv.
  Proof.
    intros. econstructor.
    - 
      fold (const x).
      hl_Imp_Lang_assign_helper.
    - econstructor; [ fold (const dn); hl_Imp_Lang_assign_helper | ].
      econstructor; [ fold (const dd); hl_Imp_Lang_assign_helper | ].
      econstructor; [ fold (const 1); hl_Imp_Lang_assign_helper | ].
      econstructor; [ fold (const x); hl_Imp_Lang_assign_helper | ].
      econstructor; [ fold (const 2); hl_Imp_Lang_assign_helper | ].
      match goal with
      | [ |- hl_Imp_Lang _ (WHILE_Imp_Lang _ (imp_seq_ifier ?l)) _ _ _ ] =>
          remember (imp_seq_ifier l) as sequence
      end.      simpl in Heqsequence. subst sequence.
 
      econstructor.
      shelve. shelve.
      assert (aimpImp_Lang (series_precondition x dn dd (var "x") (var "dn") (var "dd") (var "rn") (var "rd") (var "i")) (series_loop_invariant x (*dn*) dd (var "rn") (var "rd") (var "x") (var "i") (var "dd")) series_fenv).
      eapply first_implication_proof.
      eapply H.
      Unshelve.
      + eapply 0%nat.
      + eapply first_implication_hoare_triple.
      + reflexivity.
  Defined.
End SeriesHoareTriple.
          
                                       
