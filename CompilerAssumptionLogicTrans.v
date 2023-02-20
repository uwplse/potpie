From Coq Require Import String List Peano Arith Program.Equality Nat
Psatz Arith.PeanoNat Program.Equality.

From DanTrick Require Import StackLogic DanLogHoare DanTrickLanguage EnvToStack StackLanguage DanLogProp LogicProp StackLangTheorems StackLogicBase.
From DanTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From DanTrick Require Export ProofSubstitution ImpVarMapTheorems DanLogSubstAdequate.
From DanTrick Require Import DanImpHigherOrderRel DanImpHigherOrderRelTheorems CompilerCorrect StackFrame1
StackExtensionDeterministic FunctionWellFormed LogicTranslationBase ParamsWellFormed
DanLogSubst.

(*
 * 
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.
Print a_Dan. 

Definition aexp_terminates_always fenv num_args a :=
  forall nenv dbenv,
    num_args <= Datatypes.length dbenv ->
  exists x,
    a_Dan a dbenv fenv nenv x. 

Definition aexp_args_terminates_always fenv num_args :=
  prop_args_rel (V := nat) (aexp_terminates_always fenv num_args). 

Definition bexp_terminates_always fenv num_args a :=
  forall nenv dbenv,
    num_args <= Datatypes.length dbenv ->
  exists x,
    b_Dan a dbenv fenv nenv x. 

Definition bexp_args_terminates_always fenv num_args :=
  prop_args_rel (V := bool) (bexp_terminates_always fenv num_args). 

Definition arith_lp_terminates_always fenv num_args :=
  prop_rel (V := nat) (aexp_terminates_always fenv num_args). 

Definition bool_lp_terminates_always fenv num_args :=
  prop_rel (V := bool) (bexp_terminates_always fenv num_args). 

Definition lp_terminates_always fenv num_args :=
  Dan_lp_prop_rel (aexp_terminates_always fenv num_args) (bexp_terminates_always fenv num_args).

Definition log_terminates_always fenv num_args :=
  AbsEnv_prop_rel (aexp_terminates_always fenv num_args) (bexp_terminates_always fenv num_args).

Fixpoint terminator (f: fun_env) (num_args: nat) (P P': AbsEnv) (i: imp_Dan)
(s: hl_Dan P i P' f) := 
  match s with
  | (hl_Dan_skip P fenv) => 
  log_terminates_always fenv num_args P
  | (hl_Dan_assign P fenv x a) => 
  (log_terminates_always fenv num_args (subst_AbsEnv x a P)) /\ (log_terminates_always fenv num_args P)
  | (hl_Dan_seq P Q R i1 i2 fenv p1 p2) => 
  (terminator fenv num_args P R i1 p1) /\ (terminator fenv num_args R Q i2 p2) /\ log_terminates_always fenv num_args P /\ log_terminates_always fenv num_args Q /\ log_terminates_always fenv num_args R
  | (hl_Dan_if P Q b i1 i2 fenv p1 p2) => (terminator fenv num_args (atrueDan b P) Q i1 p1) /\ (terminator fenv num_args (afalseDan b P) Q i2 p2) /\ log_terminates_always fenv num_args (atrueDan b P) /\ log_terminates_always fenv num_args (afalseDan b P) /\ log_terminates_always fenv num_args Q /\ log_terminates_always fenv num_args P
  | (hl_Dan_while P b i fenv p) => 
  (terminator fenv num_args (atrueDan b P) P i p) /\ log_terminates_always fenv num_args (atrueDan b P) /\ log_terminates_always fenv num_args P /\ log_terminates_always fenv num_args (afalseDan b P)
  | (hl_Dan_consequence P Q P' Q' c fenv p i1 i2) => 
    (terminator fenv num_args P Q c p) /\
    log_terminates_always fenv num_args P /\
    log_terminates_always fenv num_args P' /\
    log_terminates_always fenv num_args Q /\
    log_terminates_always fenv num_args Q' 
  end. 

Definition aexp_args_wf_map (map : list ident) :=
  prop_args_rel (V := nat) (var_map_wf_wrt_aexp map). 

Definition bexp_args_wf_map (map : list ident) :=
  prop_args_rel (V := bool) (var_map_wf_wrt_bexp map). 

Definition lp_arith_wf_map map :=
  prop_rel (V := nat) (var_map_wf_wrt_aexp map). 
  
Definition lp_bool_wf_map map :=
  prop_rel (V := bool) (var_map_wf_wrt_bexp map). 

Definition lp_Dan_wf_map map :=
  Dan_lp_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map). 

Definition log_Dan_wf_map map := 
  AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map). 

Definition aexp_args_wf func_list fenv :=
  prop_args_rel (V := nat) (FunctionWellFormed.fun_app_well_formed fenv func_list). 

Definition bexp_args_wf func_list fenv :=
  prop_args_rel (V := bool) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list). 

Definition lp_arith_wf func_list fenv :=
  prop_rel (V := nat) (FunctionWellFormed.fun_app_well_formed fenv func_list). 

Definition lp_bool_wf func_list fenv :=
  prop_rel (V := bool) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list).

Definition lp_Dan_wf func_list fenv :=
  Dan_lp_prop_rel (FunctionWellFormed.fun_app_well_formed fenv func_list) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list).

Definition log_Dan_wf func_list fenv :=
  AbsEnv_prop_rel (FunctionWellFormed.fun_app_well_formed fenv func_list) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list).

Lemma aexp_compiler_term_assump_backwards : 
  forall n_args idents fenv_d fenv_s func_list,
    fenv_well_formed' func_list fenv_d ->
    fenv_s = compile_fenv fenv_d -> 
    forall aD aS,
        aS = compile_aexp
              aD
              (fun x => one_index_opt x idents)
              (List.length idents) ->
        fun_app_well_formed fenv_d func_list aD ->
        var_map_wf_wrt_aexp idents aD ->
        forall nenv dbenv stk n rho, 
          List.length dbenv = n_args -> 
          state_to_stack idents nenv dbenv stk ->
          (exists x, 
          a_Dan aD dbenv fenv_d nenv x) ->
          aexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
          a_Dan aD dbenv fenv_d nenv n.
Proof.
  intros. invs H6. 
  pose proof aexp_compiler_sound (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H eq_refl aD
  (compile_aexp aD (fun x : ident => one_index_opt x idents)
          (Datatypes.length idents))
  eq_refl H2 H3 nenv dbenv stk x rho eq_refl H5 H8.
  pose proof aexp_stack_sem_det (compile_fenv fenv_d) (stk++rho) (compile_aexp aD (fun x : ident => one_index_opt x idents)
  (Datatypes.length idents)) ((stk++rho), n) ((stk++rho), x) H7 H0.
  invs H1. assumption.
Qed.  

Lemma bexp_compiler_term_assump_backwards : 
  forall n_args idents fenv_d fenv_s func_list,
    fenv_well_formed' func_list fenv_d ->
    fenv_s = compile_fenv fenv_d -> 
    forall aD aS,
        aS = compile_bexp
              aD
              (fun x => one_index_opt x idents)
              (List.length idents) ->
        fun_app_bexp_well_formed fenv_d func_list aD ->
        var_map_wf_wrt_bexp idents aD ->
        forall nenv dbenv stk n rho, 
          List.length dbenv = n_args -> 
          state_to_stack idents nenv dbenv stk ->
          (exists x, 
          b_Dan aD dbenv fenv_d nenv x) ->
          bexp_stack_sem aS fenv_s (stk ++ rho) (stk ++ rho, n) ->
          b_Dan aD dbenv fenv_d nenv n.
Proof.
  intros. invs H6. 
  pose proof bexp_compiler_sound (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H eq_refl aD
  (compile_bexp aD (fun x : ident => one_index_opt x idents)
          (Datatypes.length idents))
  eq_refl H2 H3 nenv dbenv stk x rho eq_refl H5 H8.
  pose proof bexp_stack_sem_det (compile_fenv fenv_d) (stk++rho) (compile_bexp aD (fun x : ident => one_index_opt x idents)
  (Datatypes.length idents)) ((stk++rho), n) ((stk++rho), x) H7 H0.
  invs H1. assumption.
Qed. 
  
Lemma aexp_args_sound_backwards : 
forall dargs vals sargs n_args idents func_list, 
  compile_arith_args n_args idents dargs sargs -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      aexp_args_wf func_list fenv_d dargs ->
      aexp_args_wf_map idents dargs ->
      aexp_args_terminates_always fenv_d n_args dargs ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
          (eval_prop_args_rel
          (fun (boolexpr : aexp_stack) (boolval : nat) =>
             aexp_stack_sem boolexpr (compile_fenv fenv_d) 
                            (stk ++ rho) (stk ++ rho, boolval)) sargs vals) ->
          (eval_prop_args_rel
          (fun (b : aexp_Dan) (v : nat) =>
             a_Dan b dbenv fenv_d nenv v) dargs vals). 
Proof.
  induction dargs; intros. 
  - invs H. invs H8. invs H7. constructor.
  - invs H. invs H2. invs H3. invs H4. invs H6. invs H7; invs H8. 
    econstructor.
    + eapply aexp_compiler_term_assump_backwards.
      * apply H1.
      * exists.
      * exists.
      * assumption.
      * apply H12.
      * exists.
      * exists.
      * unfold aexp_terminates_always in H14.
        apply (H14 nenv dbenv).
        lia.
      * apply H0.
    + pose proof CompiledArithArgs idents (List.length dbenv) dargs args H17. 
      apply (IHdargs vals0 args (List.length dbenv) idents func_list H9 fenv_d (compile_fenv fenv_d) eq_refl H1 H11 H13 H15 nenv dbenv eq_refl (map nenv idents ++ dbenv) H6 rho H5). 
Qed. 

Lemma bexp_args_sound_backwards : 
forall dargs vals sargs n_args idents func_list, 
  compile_bool_args n_args idents dargs sargs -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      bexp_args_wf func_list fenv_d dargs ->
      bexp_args_wf_map idents dargs ->
      bexp_args_terminates_always fenv_d n_args dargs ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
          (eval_prop_args_rel
          (fun (boolexpr : bexp_stack) (boolval : bool) =>
             bexp_stack_sem boolexpr (compile_fenv fenv_d) 
                            (stk ++ rho) (stk ++ rho, boolval)) sargs vals) ->
          (eval_prop_args_rel
          (fun (b : bexp_Dan) (v : bool) =>
             b_Dan b dbenv fenv_d nenv v) dargs vals). 
Proof.
  induction dargs; intros. 
  - invs H. invs H8. invs H7. constructor.
  - invs H. invs H2. invs H3. invs H4. invs H6. invs H7; invs H8. 
    econstructor.
    + eapply bexp_compiler_term_assump_backwards.
      * apply H1.
      * exists.
      * exists.
      * assumption.
      * apply H12.
      * exists.
      * exists.
      * unfold bexp_terminates_always in H14.
        apply (H14 nenv dbenv).
        lia.
      * apply H0.
    + pose proof CompiledBoolArgs idents (List.length dbenv) dargs args H17. 
      apply (IHdargs vals0 args (List.length dbenv) idents func_list H9 fenv_d (compile_fenv fenv_d) eq_refl H1 H11 H13 H15 nenv dbenv eq_refl (map nenv idents ++ dbenv) H6 rho H5). 
Qed.

Lemma arith_lp_sound_backwards : 
forall sl dl n_args idents func_list, 
compile_prop_rel (comp_arith idents) dl sl ->
  forall fenv_d fenv_s,
    fenv_s = compile_fenv fenv_d -> 
    FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
    lp_arith_wf func_list fenv_d dl ->
    lp_arith_wf_map idents dl ->
    arith_lp_terminates_always fenv_d n_args dl ->
    forall nenv dbenv,
      List.length dbenv = n_args ->
      forall stk,
        state_to_stack idents nenv dbenv stk -> 
        forall rho, 
          (eval_prop_rel (fun b v => aexp_stack_sem b fenv_s (stk ++ rho) (stk ++ rho, v)) sl) ->
          eval_prop_rel (fun b v => a_Dan b dbenv fenv_d nenv v) dl.
Proof.
  induction sl; intros.
  - invs H. constructor.
  - invs H7.
  - invs H. invs H4. unfold aexp_terminates_always in H8.
    specialize (H8 nenv dbenv (le_n (Datatypes.length dbenv))). invs H8. invs H7. invs H2. invs H3. 
    pose proof aexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a0 (compile_aexp a0 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H10 H13 nenv dbenv stk v rho eq_refl H6 H8 H11. econstructor.
    + apply H5.
    + apply H12.
  - invs H. invs H4. unfold aexp_terminates_always in H9. unfold aexp_terminates_always in H11. 
    specialize (H9 nenv dbenv (le_n (Datatypes.length dbenv))). specialize (H11 nenv dbenv (le_n (Datatypes.length dbenv))). invs H7. invs H2. invs H3. 
    econstructor. 
    + apply (aexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a0 (compile_aexp a0 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H10 H15 nenv dbenv stk v1 rho eq_refl H6 H9 H12).
    + apply (aexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a3 (compile_aexp a3 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H16 H18 nenv dbenv stk v2 rho eq_refl H6 H11 H13).
    + apply H14.
  - invs H; invs H4; invs H3; invs H2; invs H7; constructor.
    + apply (IHsl1 p1 (List.length dbenv) idents func_list H12 fenv_d (compile_fenv fenv_d) eq_refl H1 H15 H11 H9 nenv dbenv eq_refl stk H6 rho H17).
    + apply (IHsl2 p2 (List.length dbenv) idents func_list H13 fenv_d (compile_fenv fenv_d) eq_refl H1 H16 H14 H10 nenv dbenv eq_refl stk H6 rho H18).
  - invs H; invs H4; invs H3; invs H2; invs H7.
    + apply RelOrPropLeft.   
      apply (IHsl1 p1 (List.length dbenv) idents func_list H12 fenv_d (compile_fenv fenv_d) eq_refl H1 H15 H11 H9 nenv dbenv eq_refl stk H6 rho H8).
    + apply RelOrPropRight. 
      apply (IHsl2 p2 (List.length dbenv) idents func_list H13 fenv_d (compile_fenv fenv_d) eq_refl H1 H16 H14 H10 nenv dbenv eq_refl stk H6 rho H8).
  - invs H. invs H4. unfold aexp_terminates_always in *. invs H7. invs H2. invs H3. econstructor.
    + apply (aexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a0 (compile_aexp a0 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H11 H18 nenv dbenv stk v1 rho eq_refl H6 (H10 nenv dbenv (le_n _)) H14).
    + apply (aexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a4 (compile_aexp a4 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H19 H22 nenv dbenv stk v2 rho eq_refl H6 (H12 nenv dbenv (le_n _)) H15).
    + apply (aexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a5 (compile_aexp a5 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H20 H23 nenv dbenv stk v3 rho eq_refl H6 (H13 nenv dbenv (le_n _)) H16).
    + apply H17.
  - invs H. invs H4. unfold aexp_args_terminates_always in *. invs H7. invs H2. invs H3. invs H7. econstructor.
    + eapply aexp_args_sound_backwards.
      * constructor. apply H11.
      * exists.
      * apply H1.
      * apply H9.
      * apply H13.
      * invs H4. apply H14.
      * exists.
      * apply H6.
      * apply H15.
    + apply H16.
Qed.         

Lemma bool_lp_sound_backwards : 
forall sl dl n_args idents func_list, 
compile_prop_rel (comp_bool idents) dl sl ->
  forall fenv_d fenv_s,
    fenv_s = compile_fenv fenv_d -> 
    FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
    lp_bool_wf func_list fenv_d dl ->
    lp_bool_wf_map idents dl ->
    bool_lp_terminates_always fenv_d n_args dl ->
    forall nenv dbenv,
      List.length dbenv = n_args ->
      forall stk,
        state_to_stack idents nenv dbenv stk -> 
        forall rho, 
          (eval_prop_rel (fun b v => bexp_stack_sem b fenv_s (stk ++ rho) (stk ++ rho, v)) sl) ->
          eval_prop_rel (fun b v => b_Dan b dbenv fenv_d nenv v) dl.
Proof.
  induction sl; intros.
  - invs H. constructor.
  - invs H7.
  - invs H. invs H4. unfold bexp_terminates_always in H8.
    specialize (H8 nenv dbenv (le_n _ )). invs H8. invs H7. invs H2. invs H3. 
    pose proof bexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a0 (compile_bexp a0 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H10 H13 nenv dbenv stk v rho eq_refl H6 H8 H11. econstructor.
    + apply H5.
    + apply H12.
  - invs H. invs H4. unfold bexp_terminates_always in H9. unfold bexp_terminates_always in H11. 
    specialize (H9 nenv dbenv (le_n _)). specialize (H11 nenv dbenv (le_n _)). invs H7. invs H2. invs H3. 
    econstructor. 
    + apply (bexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a0 (compile_bexp a0 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H10 H15 nenv dbenv stk v1 rho eq_refl H6 H9 H12).
    + apply (bexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a3 (compile_bexp a3 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H16 H18 nenv dbenv stk v2 rho eq_refl H6 H11 H13).
    + apply H14.
  - invs H; invs H4; invs H3; invs H2; invs H7; constructor.
    + apply (IHsl1 p1 (List.length dbenv) idents func_list H12 fenv_d (compile_fenv fenv_d) eq_refl H1 H15 H11 H9 nenv dbenv eq_refl stk H6 rho H17).
    + apply (IHsl2 p2 (List.length dbenv) idents func_list H13 fenv_d (compile_fenv fenv_d) eq_refl H1 H16 H14 H10 nenv dbenv eq_refl stk H6 rho H18).
  - invs H; invs H4; invs H3; invs H2; invs H7.
    + apply RelOrPropLeft.   
      apply (IHsl1 p1 (List.length dbenv) idents func_list H12 fenv_d (compile_fenv fenv_d) eq_refl H1 H15 H11 H9 nenv dbenv eq_refl stk H6 rho H8).
    + apply RelOrPropRight. 
      apply (IHsl2 p2 (List.length dbenv) idents func_list H13 fenv_d (compile_fenv fenv_d) eq_refl H1 H16 H14 H10 nenv dbenv eq_refl stk H6 rho H8).
  - invs H. invs H4. unfold bexp_terminates_always in *. invs H7. invs H2. invs H3. econstructor.
    + apply (bexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a0 (compile_bexp a0 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H11 H18 nenv dbenv stk v1 rho eq_refl H6 (H10 nenv dbenv (le_n _)) H14).
    + apply (bexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a4 (compile_bexp a4 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H19 H22 nenv dbenv stk v2 rho eq_refl H6 (H12 nenv dbenv (le_n _)) H15).
    + apply (bexp_compiler_term_assump_backwards (List.length dbenv) idents fenv_d (compile_fenv fenv_d) func_list H1 eq_refl a5 (compile_bexp a5 (fun x : ident => one_index_opt x idents)(Datatypes.length idents)) eq_refl H20 H23 nenv dbenv stk v3 rho eq_refl H6 (H13 nenv dbenv (le_n _)) H16).
    + apply H17.
  - invs H. invs H4. unfold bexp_args_terminates_always in *. invs H7. invs H2. invs H3. invs H7. econstructor.
    + eapply bexp_args_sound_backwards.
      * constructor. apply H11.
      * exists.
      * apply H1.
      * apply H9.
      * apply H13.
      * invs H4. apply H14.
      * exists.
      * apply H6.
      * apply H15.
    + apply H16.
Qed.

Lemma lp_sound_backwards : 
forall dan_lp state n_args idents func_list, 
  lp_transrelation n_args idents dan_lp state -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      lp_Dan_wf func_list fenv_d dan_lp ->
      lp_Dan_wf_map idents dan_lp ->
      lp_terminates_always fenv_d n_args dan_lp ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
          meta_match_rel state fenv_s (stk ++ rho) ->
          Dan_lp_rel dan_lp fenv_d dbenv nenv.
Proof.
  induction dan_lp; intros; invs H; invs H2; invs H3; invs H4. 
  - constructor. invs H11; invs H7; eapply arith_lp_sound_backwards.
    + apply H0.
    + exists.
    + apply H1.
    + apply H9.
    + apply H10.
    + apply H12.
    + exists.
    + apply H6.
    + apply H8. 
    - constructor. invs H11; invs H7; eapply bool_lp_sound_backwards.
      + apply H0.
      + exists.
      + apply H1.
      + apply H9.
      + apply H10.
      + apply H12.
      + exists.
      + apply H6.
      + apply H8. 
Qed.   

Lemma log_sound_backwards : 
  forall dan_log state n_args idents func_list, 
    logic_transrelation n_args idents dan_log state -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      log_Dan_wf func_list fenv_d dan_log ->
      log_Dan_wf_map idents dan_log ->
      log_terminates_always fenv_d n_args dan_log->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
            absstate_match_rel state fenv_s (stk ++ rho) ->
            AbsEnv_rel dan_log fenv_d dbenv nenv.
Proof.
  induction dan_log; intros; invs H; invs H2; invs H3; invs H4. 
  - constructor. 
    pose proof lp_sound_backwards s s0 (Datatypes.length dbenv) idents func_list H11 fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H10 H12 nenv dbenv eq_refl stk H6 rho.
    apply H0. invs H7. apply H16.  
  - constructor.
    + invs H7. apply (IHdan_log1 s1 (Datatypes.length dbenv) idents func_list H12 fenv_d (compile_fenv fenv_d) eq_refl H1 H10 H13 H16 nenv dbenv eq_refl stk H6 rho H8).
    + invs H7. apply (IHdan_log2 s2 (Datatypes.length dbenv) idents func_list H14 fenv_d (compile_fenv fenv_d) eq_refl H1 H11 H15 H17 nenv dbenv eq_refl stk H6 rho H19).
  - invs H7.
    + apply AbsEnv_or_left. apply (IHdan_log1 s1 (Datatypes.length dbenv) idents func_list H12 fenv_d (compile_fenv fenv_d) eq_refl H1 H10 H13 H16 nenv dbenv eq_refl stk H6 rho H18).
    + apply AbsEnv_or_right. apply (IHdan_log2 s2 (Datatypes.length dbenv) idents func_list H14 fenv_d (compile_fenv fenv_d) eq_refl H1 H11 H15 H17 nenv dbenv eq_refl stk H6 rho H18).
Qed. 

Lemma args_sound_forward : 
forall dargs vals sargs n_args idents func_list, 
  compile_arith_args n_args idents dargs sargs -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      aexp_args_wf func_list fenv_d dargs ->
      aexp_args_wf_map idents dargs ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
          (eval_prop_args_rel
          (fun (b : aexp_Dan) (v : nat) =>
             a_Dan b dbenv fenv_d nenv v) dargs vals) ->
            eval_prop_args_rel
            (fun (boolexpr : aexp_stack) (boolval : nat) =>
               aexp_stack_sem boolexpr (compile_fenv fenv_d) 
                              (stk ++ rho) (stk ++ rho, boolval)) sargs vals. 
Proof. 
induction dargs; intros.
  - invs H. invs H7. invs H6. constructor.
  - invs H. invs H2. invs H3. invs H7. invs H6. 
    econstructor.
    + eapply aexp_compiler_sound.
      * apply H1.
      * apply eq_refl.
      * apply eq_refl.
      * apply H9.
      * apply H11.
      * apply eq_refl.
      * apply H5.
      * apply H13. 
    + eapply IHdargs.
      * exists. apply H14.
      * apply eq_refl. 
      * apply H1.
      * apply H10.
      * apply H12.
      * exists.
      * apply H5.
      * apply H16.
Qed. 

Lemma bexp_args_sound_forward : 
forall dargs vals sargs n_args idents func_list, 
  compile_bool_args n_args idents dargs sargs -> 
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      bexp_args_wf func_list fenv_d dargs ->
      bexp_args_wf_map idents dargs ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
          (eval_prop_args_rel
          (fun (b : bexp_Dan) (v : bool) =>
             b_Dan b dbenv fenv_d nenv v) dargs vals) ->
            eval_prop_args_rel
            (fun (boolexpr : bexp_stack) (boolval : bool) =>
               bexp_stack_sem boolexpr (compile_fenv fenv_d) 
                              (stk ++ rho) (stk ++ rho, boolval)) sargs vals. 
Proof. 
induction dargs; intros.
  - invs H. invs H7. invs H6. constructor.
  - invs H. invs H2. invs H3. invs H7. invs H6. 
    econstructor.
    + eapply bexp_compiler_sound.
      * apply H1.
      * apply eq_refl.
      * apply eq_refl.
      * apply H9.
      * apply H11.
      * apply eq_refl.
      * apply H5.
      * apply H13. 
    + eapply IHdargs.
      * exists. apply H14.
      * apply eq_refl. 
      * apply H1.
      * apply H10.
      * apply H12.
      * exists.
      * apply H5.
      * apply H16.
Qed. 

Lemma bool_lp_sound_forward : 
forall sl dl n_args idents func_list, 
  compile_prop_rel (comp_bool idents) dl sl ->
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      lp_bool_wf func_list fenv_d dl ->
      lp_bool_wf_map idents dl ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
            eval_prop_rel (fun b v => b_Dan b dbenv fenv_d nenv v) dl ->
            eval_prop_rel (fun b v => bexp_stack_sem b fenv_s (stk ++ rho) (stk ++ rho, v)) sl.
Proof. 
  induction sl; intros; 
  pose proof bexp_compiler_sound n_args idents fenv_d fenv_s func_list H1 H0.
  - constructor.
  - invs H. invs H6.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6. 
    econstructor.
    + specialize (H7 a0 (comp_bool idents a0) eq_refl).
      eapply H7.
      * apply H8.
      * apply H9.
      * exists.
      * apply H5.
      * apply H11.
    + apply H12.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    econstructor.
    + specialize (H7 a0 (comp_bool idents a0) eq_refl).
      eapply H7.
      * apply H9.
      * apply H10.
      * exists.
      * apply H5. 
      * apply H14.
    + apply (H7 a3 (comp_bool idents a3) eq_refl H11 H13 
      nenv dbenv stk v2 rho eq_refl H5 H15).
    + assumption.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    econstructor.
    + apply (IHsl1 p1 (Datatypes.length dbenv) idents func_list H12
      fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H11 nenv dbenv
      eq_refl stk H5 rho H15).
    + apply (IHsl2 p2 (Datatypes.length dbenv) idents func_list H13
      fenv_d (compile_fenv fenv_d) eq_refl H1 H10 H14 nenv dbenv
      eq_refl stk H5 rho H16).
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    + apply RelOrPropLeft. 
      apply (IHsl1 p1 (Datatypes.length dbenv) idents func_list H12
      fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H11 nenv dbenv
      eq_refl stk H5 rho H8).
    + apply RelOrPropRight. 
      apply (IHsl2 p2 (Datatypes.length dbenv) idents func_list H13
      fenv_d (compile_fenv fenv_d) eq_refl H1 H10 H14 nenv dbenv
      eq_refl stk H5 rho H8).
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    econstructor.
    + apply (H7 a0 (comp_bool idents a0) eq_refl H10 H11 
      nenv dbenv stk v1 rho eq_refl H5 H17).
    + apply (H7 a4 (comp_bool idents a4) eq_refl H12 H15 
      nenv dbenv stk v2 rho eq_refl H5 H18).
    + apply (H7 a5 (comp_bool idents a5) eq_refl H13 H16 
      nenv dbenv stk v3 rho eq_refl H5 H19).
    + apply H20.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    pose proof bexp_args_sound_forward alist vals a_list (Datatypes.length dbenv) idents 
    func_list (CompiledBoolArgs idents (Datatypes.length dbenv) alist a_list H11)
    fenv_d (compile_fenv fenv_d) eq_refl H1 H8 H9 nenv dbenv eq_refl stk H5 rho
    H12.
    econstructor.
    + apply H0. 
    + apply H13.
Qed. 

Lemma arith_lp_sound_forward : 
forall sl dl n_args idents func_list, 
  compile_prop_rel (comp_arith idents) dl sl ->
    forall fenv_d fenv_s,
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      lp_arith_wf func_list fenv_d dl ->
      lp_arith_wf_map idents dl ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          forall rho, 
            eval_prop_rel (fun b v => a_Dan b dbenv fenv_d nenv v) dl ->
            eval_prop_rel (fun b v => aexp_stack_sem b fenv_s (stk ++ rho) (stk ++ rho, v)) sl.
Proof. 
  induction sl; intros; 
  pose proof aexp_compiler_sound n_args idents fenv_d fenv_s func_list H1 H0.
  - constructor.
  - invs H. invs H6.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6. 
    econstructor.
    + specialize (H7 a0 (comp_arith idents a0) eq_refl).
      eapply H7.
      * apply H8.
      * apply H9.
      * exists.
      * apply H5.
      * apply H11.
    + apply H12.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    econstructor.
    + specialize (H7 a0 (comp_arith idents a0) eq_refl).
      eapply H7.
      * apply H9.
      * apply H10.
      * exists.
      * apply H5. 
      * apply H14.
    + apply (H7 a3 (comp_arith idents a3) eq_refl H11 H13 
      nenv dbenv stk v2 rho eq_refl H5 H15).
    + assumption.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    econstructor.
    + apply (IHsl1 p1 (Datatypes.length dbenv) idents func_list H12
      fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H11 nenv dbenv
      eq_refl stk H5 rho H15).
    + apply (IHsl2 p2 (Datatypes.length dbenv) idents func_list H13
      fenv_d (compile_fenv fenv_d) eq_refl H1 H10 H14 nenv dbenv
      eq_refl stk H5 rho H16).
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    + apply RelOrPropLeft. 
      apply (IHsl1 p1 (Datatypes.length dbenv) idents func_list H12
      fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H11 nenv dbenv
      eq_refl stk H5 rho H8).
    + apply RelOrPropRight. 
      apply (IHsl2 p2 (Datatypes.length dbenv) idents func_list H13
      fenv_d (compile_fenv fenv_d) eq_refl H1 H10 H14 nenv dbenv
      eq_refl stk H5 rho H8).
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    econstructor.
    + apply (H7 a0 (comp_arith idents a0) eq_refl H10 H11 
      nenv dbenv stk v1 rho eq_refl H5 H17).
    + apply (H7 a4 (comp_arith idents a4) eq_refl H12 H15 
      nenv dbenv stk v2 rho eq_refl H5 H18).
    + apply (H7 a5 (comp_arith idents a5) eq_refl H13 H16 
      nenv dbenv stk v3 rho eq_refl H5 H19).
    + apply H20.
  - invs H. 
    invs H2. 
    invs H3. 
    invs H6.
    pose proof args_sound_forward alist vals a_list (Datatypes.length dbenv) idents 
    func_list (CompiledArithArgs idents (Datatypes.length dbenv) alist a_list H11)
    fenv_d (compile_fenv fenv_d) eq_refl H1 H8 H9 nenv dbenv eq_refl stk H5 rho
    H12.
    econstructor.
    + apply H0. 
    + apply H13.
Qed. 

Lemma lp_sound_forward : 
forall dan_lp state n_args idents func_list, 
  lp_transrelation n_args idents dan_lp state -> 
  forall fenv_d fenv_s,
  forall (OKfuncs: funcs_okay_too func_list (compile_fenv fenv_d))
    (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list),
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      lp_Dan_wf func_list fenv_d dan_lp ->
      lp_Dan_wf_map idents dan_lp ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          Dan_lp_rel dan_lp fenv_d dbenv nenv ->
          forall rho, 
            meta_match_rel state fenv_s (stk ++ rho).
Proof.
  induction dan_lp; intros; invs H; invs H10; invs H2; invs H3; invs H6. 
  - pose proof arith_lp_sound_forward s l (List.length dbenv) idents func_list 
    H0 fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H11 nenv dbenv eq_refl
    stk H5 rho H7. 
    constructor.
    + apply H4.
    + Tactics.revert_until s. revert l. induction s; intros. 
      * invs H. invs H15. invs H8. constructor.
      * invs H. invs H15. invs H8. constructor.
      * invs H. invs H15. invs H8. 
        eapply arith_compile_prop_rel_implies_pure'. 
        --apply H8.
        -- eassumption.
        -- eassumption.
        --apply H1.
        --apply H9.
        --apply eq_refl. 
        * invs H. invs H15. invs H8. 
          eapply arith_compile_prop_rel_implies_pure'. 
          --apply H8.
          -- eassumption.
          -- eassumption.
          --apply H1.
          --apply H9.
          --apply eq_refl. 
        * invs H. invs H15. invs H8. 
          eapply arith_compile_prop_rel_implies_pure'. 
          --apply H8.
          -- eassumption.
          -- eassumption.
          --apply H1.
          --apply H9.
          --apply eq_refl. 
        * invs H. invs H15. eapply arith_compile_prop_rel_implies_pure'; eauto.
        * invs H. invs H15. invs H8. 
          eapply arith_compile_prop_rel_implies_pure'. 
          --apply H8.
          -- eassumption.
          -- eassumption.
          --apply H1.
          --apply H9.
          --apply eq_refl.
        * invs H. invs H15. invs H8. invs H9. constructor. 
          eapply arith_compile_prop_args_rel_implies_pure'; eauto. 
  - pose proof bool_lp_sound_forward s l (List.length dbenv) idents func_list 
    H0 fenv_d (compile_fenv fenv_d) eq_refl H1 H9 H11 nenv dbenv eq_refl
    stk H5 rho H7. 
    constructor.
    + apply H4.
    + Tactics.revert_until s. revert l. induction s; intros. 
      * invs H. invs H15. invs H8. constructor.
      * invs H. invs H15. invs H8. constructor.
      * invs H. invs H15. invs H8. 
        eapply bool_compile_prop_rel_implies_pure'; eauto. 
      * invs H. invs H15. invs H8. 
        eapply bool_compile_prop_rel_implies_pure'; eauto. 
      * invs H. invs H15. invs H8. 
      eapply bool_compile_prop_rel_implies_pure'; eauto. 
      * invs H. invs H15. eapply bool_compile_prop_rel_implies_pure'; eauto.
      * invs H. invs H15. invs H8. 
        eapply bool_compile_prop_rel_implies_pure'; eauto. 
      * invs H. invs H15. invs H8. invs H9. constructor. 
        eapply bool_compile_prop_args_rel_implies_pure'; eauto. 
Qed. 

Lemma log_sound_forward : 
forall dan_log state n_args idents func_list, 
  logic_transrelation n_args idents dan_log state -> 
  forall fenv_d fenv_s
    (OKfuncs: funcs_okay_too func_list (compile_fenv fenv_d))
    (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list),
      fenv_s = compile_fenv fenv_d -> 
      FunctionWellFormed.fenv_well_formed' func_list fenv_d ->
      log_Dan_wf func_list fenv_d dan_log ->
      log_Dan_wf_map idents dan_log ->
      forall nenv dbenv,
        List.length dbenv = n_args ->
        forall stk,
          state_to_stack idents nenv dbenv stk -> 
          AbsEnv_rel dan_log fenv_d dbenv nenv ->
          forall rho, 
            absstate_match_rel state fenv_s (stk ++ rho).
Proof.
  induction dan_log; intros.
  - invs H. invs H2. invs H3. invs H6.
    pose proof (lp_sound_forward s s0 (Datatypes.length dbenv) idents func_list
                                 H10
                                 fenv_d _
                                 OKfuncs
                                 OKparams
                                 eq_refl
    H1 H8 H9 nenv dbenv eq_refl stk H5 H4 rho).
    constructor.
    + constructor.
      invs H5.
      repeat rewrite app_length.
      rewrite map_length.
      lia.
    + apply H0.
  - invs H. invs H2. invs H3. invs H6.
    constructor.
    + eapply IHdan_log1; eauto.
    + eapply IHdan_log2; eauto.
  - invs H. invs H2. invs H3. invs H6.
    + apply RelAbsOrLeft; eauto.
    + apply RelAbsOrRight; eauto. 
Qed. 

