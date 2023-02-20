From Coq Require Import String List Peano Arith Program.Equality Nat
Psatz Arith.PeanoNat Program.Equality.

From DanTrick Require Import StackLogic DanLogHoare DanTrickLanguage EnvToStack StackLanguage DanLogProp LogicProp StackLangTheorems StackLogicBase.
From DanTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From DanTrick Require Export ProofSubstitution ImpVarMapTheorems DanLogSubstAdequate.
From DanTrick Require Import DanImpHigherOrderRel DanImpHigherOrderRelTheorems CompilerCorrect StackFrame1
StackExtensionDeterministic FunctionWellFormed LogicTranslationBase ParamsWellFormed
DanLogSubst CompilerAssumptionLogicTrans.

Lemma stupid_list_nat : 
  forall n (e : nat) lst, 
  List.length (e::lst) = S n ->
  List.length (lst) = n.
Proof.
  intros. 
  unfold length in *.
  lia.   
Qed. 

Lemma stupid_list_ident : 
  forall n (e : DanTrickLanguage.ident) lst, 
  List.length (e::lst) = S n ->
  List.length (lst) = n.
Proof.
  intros. 
  unfold length in *.
  lia.   
Qed. 

Lemma wf_map_update : 
forall map a x (n : nat),
  ~In a map ->
  NoDup map ->
  List.map x map = List.map (update a n x) map.
Proof.
  induction map.
  - intros. simpl. reflexivity.
  - intros. simpl.
    pose proof (IHmap a0 x n).
    pose proof (not_in_cons a0 a map). 
    destruct H2.
    pose proof H2 H.
    destruct H4.
    invs H0. 
    pose proof (H1 H5 H9).
    rewrite H6. 
    pose proof update_other nat a0 n x a H4.
    rewrite H7. reflexivity.  
Qed. 

Lemma stk_to_env : 
  forall map stk args, 
  List.length stk = List.length map + args ->
  List.NoDup map ->
  exists nenv dbenv, 
  state_to_stack map nenv dbenv stk
  /\ List.length dbenv = args.
Proof.
  induction map; intros.
  simpl in H.
  exists init_nenv. exists stk.
  split. constructor. apply H.
  destruct stk.
  - invs H.
  - assert (Datatypes.length stk = Datatypes.length map + args). 
    apply (stupid_list_nat (Datatypes.length (map) + args) n stk H).
    invs H0. 
    pose proof (IHmap stk args H1 H5).
    invs H2. invs H3. invs H6.
    exists (update a n x). exists x0.
    split.
    assert (update a n x a = n) by apply update_same.
    invs H7.
    assert ((n :: List.map x map ++ x0) = List.map (update a n x) (a::map) ++ x0).
    + simpl. rewrite H8. 
      pose proof wf_map_update map a x n H4 H5.
      rewrite H9. apply eq_refl.   
    + rewrite H9. constructor.
    + apply eq_refl.
Qed.    

Lemma weak_stack_aexp_determ : 
  forall fenv stk a stk' stk'' n n',
  aexp_stack_sem a fenv stk (stk', n)->
  aexp_stack_sem a fenv stk (stk'', n') ->
  n = n'.
Proof.
  intros. pose proof aexp_stack_sem_det fenv stk a (stk', n)
  (stk'', n') H H0. pose proof pair_equal_spec stk' stk'' n n'.
  destruct H2. apply H2; assumption.
Qed.      

Lemma weak_stack_bexp_determ : 
  forall fenv stk a stk' stk'' n n',
  bexp_stack_sem a fenv stk (stk', n)->
  bexp_stack_sem a fenv stk (stk'', n') ->
  n = n'.
Proof.
  intros. pose proof bexp_stack_sem_det fenv stk a (stk', n)
  (stk'', n') H H0. pose proof pair_equal_spec stk' stk'' n n'.
  destruct H2. apply H2; assumption.
Qed.      

Lemma list_chop_determ : 
forall x x0 (stk: list nat) n, 
  stk = x ++ x0 -> 
  Datatypes.length stk > n ->
  Datatypes.length x = n ->
  firstn n stk = x.
Proof.
  intros. pose proof firstn_app n x x0. 
  rewrite <- H in H2. rewrite H1 in H2. rewrite H2.
  assert (n - n = 0) by lia. rewrite H3. simpl. rewrite app_nil_r.
  pose proof firstn_all x. rewrite H1 in H4. assumption.
Qed.        

Lemma stk_truncate_aexp : 
  forall a a_stk stk n_args idents fenv v func_list
  (NO: NoDup idents)
  (COMP: a_stk = compile_aexp a
  (fun x => one_index_opt x idents)
  (List.length idents))
  (WF: var_map_wf_wrt_aexp idents a)
  (FAPPWF: fun_app_well_formed fenv func_list a)
  (SEM: aexp_stack_sem a_stk (compile_fenv fenv) stk (stk, v))
  (LEN: Datatypes.length stk > n_args + Datatypes.length idents)
  (TERM: aexp_terminates_always (fenv) n_args a)
  (OK2: funcs_okay_too func_list (compile_fenv fenv))
  (FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
  exists stk' stk'',
    stk = stk' ++ stk'' /\ 
    Datatypes.length stk' = n_args + Datatypes.length idents /\
    aexp_stack_sem a_stk (compile_fenv fenv) stk' (stk', v). 
Proof.
  intros; unfold aexp_terminates_always in TERM; 
  exists (firstn (n_args + Datatypes.length idents) stk);
  exists (skipn ((n_args + Datatypes.length idents)) stk); split; 
  try split.
- pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
  apply eq_refl.
- pose proof firstn_length_le stk. 
  specialize (H (n_args + Datatypes.length idents)). 
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H H0). apply H.
- simpl in COMP; rewrite COMP in *.
  pose proof firstn_length (n_args + Datatypes.length idents) stk. 
  simpl in H. 
  pose proof stk_to_env idents (firstn (n_args + Datatypes.length idents) stk) n_args. 
  pose proof firstn_length (n_args + Datatypes.length idents) stk. 
  pose proof min_l (n_args + Datatypes.length idents) (Datatypes.length stk).
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H2 H3). rewrite H2 in *.
  rewrite H1 in *.
  rewrite Nat.add_comm in H0. 
  specialize (H0 eq_refl NO). invs H0. invs H4. destruct H5. 
  assert (n_args <= Datatypes.length x0) by lia. 
  specialize (TERM x x0 H7). 
  invs TERM.
  pose proof aexp_compiler_sound (Datatypes.length x0) idents fenv 
  (compile_fenv fenv) func_list FWF eq_refl a
  (compile_aexp a (fun x2 : ident => one_index_opt x2 idents)
  (Datatypes.length idents)).
  simpl in H6.
  specialize (H6 eq_refl FAPPWF WF x x0 
  (firstn (Datatypes.length idents + Datatypes.length x0) stk)
  x1).
  pose proof H6.
  specialize (H6 nil eq_refl H5 H8).
  specialize (H9 (skipn ((Datatypes.length idents + Datatypes.length x0)) stk)
  eq_refl H5 H8).
  rewrite firstn_skipn in H9.    
  rewrite app_nil_r in H6.
  pose proof weak_stack_aexp_determ (compile_fenv fenv) stk 
  (compile_aexp a (fun x2 : ident => one_index_opt x2 idents)
  (Datatypes.length idents)) stk stk x1 v H9 SEM. 
  rewrite H10 in *. 
  pose proof Nat.add_comm (Datatypes.length idents) (Datatypes.length x0). 
  rewrite H11 in H6. apply H6.
Qed. 

Lemma stk_truncate_aexp_args : 
forall a a_stk stk n_args idents fenv v func_list
(NO: NoDup idents)
(COMP: compile_arith_args n_args idents a a_stk)
(WF: aexp_args_wf func_list fenv a)
(FAPPWF: aexp_args_wf_map idents a)
(SEM: (eval_prop_args_rel
  (fun (boolexpr : aexp_stack) (boolval : nat) =>
   aexp_stack_sem boolexpr (compile_fenv fenv) 
                  (stk) (stk, boolval)) a_stk v))
(LEN: Datatypes.length stk > n_args + Datatypes.length idents)
(TERM: aexp_args_terminates_always fenv n_args a)
(OK2: funcs_okay_too func_list (compile_fenv fenv))
(FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
exists stk' stk'',
  stk = stk' ++ stk'' /\ 
  Datatypes.length stk' = n_args + Datatypes.length idents /\
  (eval_prop_args_rel
  (fun (boolexpr : aexp_stack) (boolval : nat) =>
   aexp_stack_sem boolexpr (compile_fenv fenv) 
                  (stk') (stk', boolval)) a_stk v).
Proof.
induction a; intros; exists (firstn (n_args + Datatypes.length idents) stk);
exists (skipn ((n_args + Datatypes.length idents)) stk); split; 
try split.
- pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
  apply eq_refl.
- pose proof firstn_length_le stk. 
  specialize (H (n_args + Datatypes.length idents)). 
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H H0). apply H.
- invs COMP. invs H. invs SEM. constructor.
- pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
  apply eq_refl.
- pose proof firstn_length_le stk. 
  specialize (H (n_args + Datatypes.length idents)). 
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H H0). apply H.
- invs COMP. invs H. invs SEM. invs TERM. invs H. invs WF. invs FAPPWF. constructor.
  + pose proof stk_truncate_aexp a (comp_arith idents a) stk n_args idents
    fenv val func_list NO eq_refl H11 H9 H3 LEN H5 OK2 FWF.
    invs H0. invs H1. destruct H8. destruct H13. 
    pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H8 LEN H13.  
    rewrite H15. apply H14.
  + specialize (IHa args' stk n_args idents fenv vals func_list NO 
    (CompiledArithArgs idents n_args a0 args' H4) H10 H12 H6 LEN H7
    OK2 FWF).
    invs IHa. invs H0. destruct H1. destruct H8. 
    pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H8.  
    rewrite H14. apply H13.
Qed. 

Lemma stk_truncate_bexp : 
  forall a a_stk stk n_args idents fenv v func_list
  (NO: NoDup idents)
  (COMP: a_stk = compile_bexp a
  (fun x => one_index_opt x idents)
  (List.length idents))
  (WF: var_map_wf_wrt_bexp idents a)
  (FAPPWF: fun_app_bexp_well_formed fenv func_list a)
  (SEM: bexp_stack_sem a_stk (compile_fenv fenv) stk (stk, v))
  (LEN: Datatypes.length stk > n_args + Datatypes.length idents)
  (TERM: bexp_terminates_always (fenv) n_args a)
  (OK2: funcs_okay_too func_list (compile_fenv fenv))
  (FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
  exists stk' stk'',
    stk = stk' ++ stk'' /\ 
    Datatypes.length stk' = n_args + Datatypes.length idents /\
    bexp_stack_sem a_stk (compile_fenv fenv) stk' (stk', v). 
Proof.
  intros; unfold bexp_terminates_always in TERM; 
  exists (firstn (n_args + Datatypes.length idents) stk);
  exists (skipn ((n_args + Datatypes.length idents)) stk); split; 
  try split.
- pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
  apply eq_refl.
- pose proof firstn_length_le stk. 
  specialize (H (n_args + Datatypes.length idents)). 
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H H0). apply H.
- simpl in COMP; rewrite COMP in *.
  pose proof firstn_length (n_args + Datatypes.length idents) stk. 
  simpl in H. 
  pose proof stk_to_env idents (firstn (n_args + Datatypes.length idents) stk) n_args. 
  pose proof firstn_length (n_args + Datatypes.length idents) stk. 
  pose proof min_l (n_args + Datatypes.length idents) (Datatypes.length stk).
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H2 H3). rewrite H2 in *.
  rewrite H1 in *.
  rewrite Nat.add_comm in H0. 
  specialize (H0 eq_refl NO). invs H0. invs H4. destruct H5. 
  assert (n_args <= Datatypes.length x0) by lia. 
  specialize (TERM x x0 H7). 
  invs TERM.
  pose proof bexp_compiler_sound (Datatypes.length x0) idents fenv 
  (compile_fenv fenv) func_list FWF eq_refl a
  (compile_bexp a (fun x2 : ident => one_index_opt x2 idents)
  (Datatypes.length idents)).
  simpl in H6.
  specialize (H6 eq_refl FAPPWF WF x x0 
  (firstn (Datatypes.length idents + Datatypes.length x0) stk)
  x1).
  pose proof H6.
  specialize (H6 nil eq_refl H5 H8).
  specialize (H9 (skipn ((Datatypes.length idents + Datatypes.length x0)) stk)
  eq_refl H5 H8).
  rewrite firstn_skipn in H9.    
  rewrite app_nil_r in H6.
  pose proof weak_stack_bexp_determ (compile_fenv fenv) stk 
  (compile_bexp a (fun x2 : ident => one_index_opt x2 idents)
  (Datatypes.length idents)) stk stk x1 v H9 SEM. 
  rewrite H10 in *. 
  pose proof Nat.add_comm (Datatypes.length idents) (Datatypes.length x0). 
  rewrite H11 in H6. apply H6.
Qed.

Lemma stk_truncate_bexp_args : 
forall a a_stk stk n_args idents fenv v func_list
(NO: NoDup idents)
(COMP: compile_bool_args n_args idents a a_stk)
(WF: bexp_args_wf func_list fenv a)
(FAPPWF: bexp_args_wf_map idents a)
(SEM: (eval_prop_args_rel
  (fun (boolexpr : bexp_stack) (boolval : bool) =>
   bexp_stack_sem boolexpr (compile_fenv fenv) 
                  (stk) (stk, boolval)) a_stk v))
(LEN: Datatypes.length stk > n_args + Datatypes.length idents)
(TERM: bexp_args_terminates_always fenv n_args a)
(OK2: funcs_okay_too func_list (compile_fenv fenv))
(FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
exists stk' stk'',
  stk = stk' ++ stk'' /\ 
  Datatypes.length stk' = n_args + Datatypes.length idents /\
  (eval_prop_args_rel
  (fun (boolexpr : bexp_stack) (boolval : bool) =>
   bexp_stack_sem boolexpr (compile_fenv fenv) 
                  (stk') (stk', boolval)) a_stk v).
Proof.
induction a; intros; exists (firstn (n_args + Datatypes.length idents) stk);
exists (skipn ((n_args + Datatypes.length idents)) stk); split; 
try split.
- pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
  apply eq_refl.
- pose proof firstn_length_le stk. 
  specialize (H (n_args + Datatypes.length idents)). 
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H H0). apply H.
- invs COMP. invs H. invs SEM. constructor.
- pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
  apply eq_refl.
- pose proof firstn_length_le stk. 
  specialize (H (n_args + Datatypes.length idents)). 
  assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
  specialize (H H0). apply H.
- invs COMP. invs H. invs SEM. invs TERM. invs H. invs WF. invs FAPPWF. constructor.
  + pose proof stk_truncate_bexp a (comp_bool idents a) stk n_args idents
    fenv val func_list NO eq_refl H11 H9 H3 LEN H5 OK2 FWF.
    invs H0. invs H1. destruct H8. destruct H13. 
    pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H8 LEN H13.  
    rewrite H15. apply H14.
  + specialize (IHa args' stk n_args idents fenv vals func_list NO 
    (CompiledBoolArgs idents n_args a0 args' H4) H10 H12 H6 LEN H7
    OK2 FWF).
    invs IHa. invs H0. destruct H1. destruct H8. 
    pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H8.  
    rewrite H14. apply H13.
Qed. 

Lemma stk_truncate_arith_lp : 
  forall a a_stk stk n_args idents fenv func_list
  (NO: NoDup idents)
  (COMP: lp_arith_transrelation n_args idents a a_stk)
  (WF: prop_rel (var_map_wf_wrt_aexp idents) a)
  (FAPPWF: prop_rel (fun_app_well_formed fenv func_list) a)
  (SEM: eval_prop_rel (fun natexpr natval => aexp_stack_sem natexpr (compile_fenv fenv) stk (stk, natval)) a_stk)
  (LEN: Datatypes.length stk > n_args + Datatypes.length idents)
  (TERM: arith_lp_terminates_always (fenv) n_args a)
  (OK2: funcs_okay_too func_list (compile_fenv fenv))
  (FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
  exists stk' stk'',
    stk = stk' ++ stk'' /\ 
    Datatypes.length stk' = n_args + Datatypes.length idents /\
    eval_prop_rel (fun natexpr natval => aexp_stack_sem natexpr (compile_fenv fenv) stk' (stk', natval)) a_stk.
Proof.
  induction a; intros; exists (firstn (n_args + Datatypes.length idents) stk);
  exists (skipn ((n_args + Datatypes.length idents)) stk).
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. constructor.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor. 
      pose proof stk_truncate_aexp a (comp_arith idents a) stk n_args idents fenv
      v func_list NO eq_refl H2 H5 H3 LEN H6 OK2 FWF. 
      invs H0. invs H1. destruct H7. destruct H8.
      pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H7 LEN H8.  
      rewrite H10. apply H9.
      apply H4.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
      * pose proof stk_truncate_aexp a1 (comp_arith idents a1) stk n_args idents fenv
        v1 func_list NO eq_refl H3 H7 H4 LEN H9 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H11.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H11.  
        rewrite H14. apply H13.
      * pose proof stk_truncate_aexp a2 (comp_arith idents a2) stk n_args idents fenv
        v2 func_list NO eq_refl H8 H10 H5 LEN H12 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H11.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H11.  
        rewrite H14. apply H13.
      * apply H6.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. invs H. econstructor.
      * specialize (IHa1 q1 stk n_args idents fenv func_list NO 
        (CompiledArith idents n_args a1 q1 H14) H7 H9 H4 LEN H11 OK2 FWF).
        invs IHa1. invs H0. destruct H1. destruct H2.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H2.
        rewrite H15. apply H13.
      * specialize (IHa2 q2 stk n_args idents fenv func_list NO 
        (CompiledArith idents n_args a2 q2 H16) H8 H10 H6 LEN H12 OK2 FWF).
        invs IHa2. invs H0. destruct H1. destruct H2.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H2.
        rewrite H15. apply H13.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP; invs H; invs SEM; invs WF; invs FAPPWF; invs TERM; invs H.
      * apply RelOrPropLeft. specialize (IHa1 q1 stk n_args idents fenv func_list NO 
        (CompiledArith idents n_args a1 q1 H3) H6 H8 H2 LEN H10 OK2 FWF).
        invs IHa1. invs H0. destruct H1. destruct H4.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H4.
        rewrite H14. apply H12.
      * apply RelOrPropRight. specialize (IHa2 q2 stk n_args idents fenv func_list NO 
        (CompiledArith idents n_args a2 q2 H5) H7 H9 H2 LEN H11 OK2 FWF).
        invs IHa2. invs H0. destruct H1. destruct H4.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H4.
        rewrite H14. apply H12.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
      * pose proof stk_truncate_aexp a1 (comp_arith idents a1) stk n_args idents fenv
        v1 func_list NO eq_refl H4 H9 H5 LEN H12 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H3.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H3.  
        rewrite H18. apply H15.
      * pose proof stk_truncate_aexp a2 (comp_arith idents a2) stk n_args idents fenv
        v2 func_list NO eq_refl H10 H13 H6 LEN H16 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H3.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H3.  
        rewrite H18. apply H15.
      * pose proof stk_truncate_aexp a3 (comp_arith idents a3) stk n_args idents fenv
        v3 func_list NO eq_refl H11 H14 H7 LEN H17 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H3.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H3.  
        rewrite H18. apply H15.
      * apply H8.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
      * pose proof stk_truncate_aexp_args a_list blist stk n_args idents fenv
        vals func_list NO (CompiledArithArgs idents n_args a_list blist H4) H6
        H2 H3 LEN H7 OK2 FWF.
        invs H0. invs H1. destruct H8. destruct H9.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H8 LEN H9.  
        rewrite H11. apply H10.
      * apply H5. 
Qed. 

Lemma stk_truncate_bool_lp : 
  forall a a_stk stk n_args idents fenv func_list
  (NO: NoDup idents)
  (COMP: lp_bool_transrelation n_args idents a a_stk)
  (WF: prop_rel (var_map_wf_wrt_bexp idents) a)
  (FAPPWF: prop_rel (fun_app_bexp_well_formed fenv func_list) a)
  (SEM: eval_prop_rel (fun natexpr natval => bexp_stack_sem natexpr (compile_fenv fenv) stk (stk, natval)) a_stk)
  (LEN: Datatypes.length stk > n_args + Datatypes.length idents)
  (TERM: bool_lp_terminates_always (fenv) n_args a)
  (OK2: funcs_okay_too func_list (compile_fenv fenv))
  (FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
  exists stk' stk'',
    stk = stk' ++ stk'' /\ 
    Datatypes.length stk' = n_args + Datatypes.length idents /\
    eval_prop_rel (fun natexpr natval => bexp_stack_sem natexpr (compile_fenv fenv) stk' (stk', natval)) a_stk.
Proof.
  induction a; intros; exists (firstn (n_args + Datatypes.length idents) stk);
  exists (skipn ((n_args + Datatypes.length idents)) stk).
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. constructor.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor. 
      pose proof stk_truncate_bexp a (comp_bool idents a) stk n_args idents fenv
      v func_list NO eq_refl H2 H5 H3 LEN H6 OK2 FWF. 
      invs H0. invs H1. destruct H7. destruct H8.
      pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H7 LEN H8.  
      rewrite H10. apply H9.
      apply H4.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
      * pose proof stk_truncate_bexp a1 (comp_bool idents a1) stk n_args idents fenv
        v1 func_list NO eq_refl H3 H7 H4 LEN H9 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H11.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H11.  
        rewrite H14. apply H13.
      * pose proof stk_truncate_bexp a2 (comp_bool idents a2) stk n_args idents fenv
        v2 func_list NO eq_refl H8 H10 H5 LEN H12 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H11.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H11.  
        rewrite H14. apply H13.
      * apply H6.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. invs H. econstructor.
      * specialize (IHa1 q1 stk n_args idents fenv func_list NO 
        (CompiledBool idents n_args a1 q1 H14) H7 H9 H4 LEN H11 OK2 FWF).
        invs IHa1. invs H0. destruct H1. destruct H2.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H2.
        rewrite H15. apply H13.
      * specialize (IHa2 q2 stk n_args idents fenv func_list NO 
        (CompiledBool idents n_args a2 q2 H16) H8 H10 H6 LEN H12 OK2 FWF).
        invs IHa2. invs H0. destruct H1. destruct H2.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H2.
        rewrite H15. apply H13.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP; invs H; invs SEM; invs WF; invs FAPPWF; invs TERM; invs H.
      * apply RelOrPropLeft. specialize (IHa1 q1 stk n_args idents fenv func_list NO 
        (CompiledBool idents n_args a1 q1 H3) H6 H8 H2 LEN H10 OK2 FWF).
        invs IHa1. invs H0. destruct H1. destruct H4.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H4.
        rewrite H14. apply H12.
      * apply RelOrPropRight. specialize (IHa2 q2 stk n_args idents fenv func_list NO 
        (CompiledBool idents n_args a2 q2 H5) H7 H9 H2 LEN H11 OK2 FWF).
        invs IHa2. invs H0. destruct H1. destruct H4.    
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H1 LEN H4.
        rewrite H14. apply H12.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
      * pose proof stk_truncate_bexp a1 (comp_bool idents a1) stk n_args idents fenv
        v1 func_list NO eq_refl H4 H9 H5 LEN H12 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H3.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H3.  
        rewrite H18. apply H15.
      * pose proof stk_truncate_bexp a2 (comp_bool idents a2) stk n_args idents fenv
        v2 func_list NO eq_refl H10 H13 H6 LEN H16 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H3.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H3.  
        rewrite H18. apply H15.
      * pose proof stk_truncate_bexp a3 (comp_bool idents a3) stk n_args idents fenv
        v3 func_list NO eq_refl H11 H14 H7 LEN H17 OK2 FWF. 
        invs H0. invs H1. destruct H2. destruct H3.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H2 LEN H3.  
        rewrite H18. apply H15.
      * apply H8.
  - split; 
    try split.
    + pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
      apply eq_refl.
    + pose proof firstn_length_le stk. 
      specialize (H (n_args + Datatypes.length idents)). 
      assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
      specialize (H H0). apply H.
    + invs COMP. invs H. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
      * pose proof stk_truncate_bexp_args a_list blist stk n_args idents fenv
        vals func_list NO (CompiledBoolArgs idents n_args a_list blist H4) H6
        H2 H3 LEN H7 OK2 FWF.
        invs H0. invs H1. destruct H8. destruct H9.
        pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H8 LEN H9.  
        rewrite H11. apply H10.
      * apply H5. 
Qed. 
  
Lemma stk_truncate_lp : 
forall a a_stk stk n_args idents fenv func_list
(NO: NoDup idents)
(COMP: lp_transrelation n_args idents a a_stk)
(WF: Dan_lp_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) a)
(FAPPWF: Dan_lp_prop_rel (fun_app_well_formed fenv func_list) (fun_app_bexp_well_formed fenv func_list) a)
(OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
(SEM: meta_match_rel a_stk (compile_fenv fenv) stk)
(LEN: Datatypes.length stk > n_args + Datatypes.length idents)
(TERM: lp_terminates_always (fenv) n_args a)
(OK2: funcs_okay_too func_list (compile_fenv fenv))
(FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
exists stk' stk'',
  stk = stk' ++ stk'' /\ 
  Datatypes.length stk' = n_args + Datatypes.length idents /\
  (meta_match_rel a_stk (compile_fenv fenv) stk').
Proof.
  induction a; intros; exists (firstn (n_args + Datatypes.length idents) stk);
  exists (skipn ((n_args + Datatypes.length idents)) stk); split; try split.
  - pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
    apply eq_refl.
  - pose proof firstn_length_le stk. 
    specialize (H (n_args + Datatypes.length idents)). 
    assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
    specialize (H H0). apply H.
  - invs COMP. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
    + pose proof stk_truncate_arith_lp l s stk n_args idents fenv func_list NO
      H2 H5 H6 H0 LEN H7 OK2 FWF.
      invs H. invs H3. destruct H4. destruct H8. 
      pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H4 LEN H8.  
      rewrite H10. apply H9.
    + eapply arith_compile_prop_rel_implies_pure'.
      * invs H2. apply H.
      * apply OK2.
      * eassumption.
      * eassumption.
      * eassumption.
      * apply eq_refl.         
  - pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
    apply eq_refl.
  - pose proof firstn_length_le stk. 
    specialize (H (n_args + Datatypes.length idents)). 
    assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
    specialize (H H0). apply H.
  - invs COMP. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
    + pose proof stk_truncate_bool_lp l s stk n_args idents fenv func_list NO
      H2 H5 H6 H0 LEN H7 OK2 FWF.
      invs H. invs H3. destruct H4. destruct H8. 
      pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H4 LEN H8.  
      rewrite H10. apply H9.
    + eapply bool_compile_prop_rel_implies_pure'.
      * invs H2. apply H.
      * exists. 
      * apply OK2.
      * eassumption.
      * eassumption.
      * eassumption.
      * apply eq_refl.
Qed.  

Lemma stk_truncate : 
forall d1 s1 stk n_args idents fenv func_list
(NO: NoDup idents)
(COMP: logic_transrelation n_args idents d1 s1)
(WF: AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) 
    (var_map_wf_wrt_bexp idents) d1)
(FAPPWF: AbsEnv_prop_rel (fun_app_well_formed fenv func_list)  (fun_app_bexp_well_formed fenv func_list) d1)
(OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) func_list)
(SEM: absstate_match_rel s1 (compile_fenv fenv) stk)
(LEN: Datatypes.length stk > n_args + Datatypes.length idents)
(TERM: log_terminates_always (fenv) n_args d1)
(OK2: funcs_okay_too func_list (compile_fenv fenv))
(FWF: FunctionWellFormed.fenv_well_formed' func_list fenv),
  exists stk' stk'',
    stk = stk' ++ stk'' /\ 
    Datatypes.length stk' = n_args + Datatypes.length idents /\
    absstate_match_rel s1 (compile_fenv fenv) stk'. 
Proof.
  induction d1; intros; exists (firstn (n_args + Datatypes.length idents) stk);
  exists (skipn ((n_args + Datatypes.length idents)) stk); split; try split.
  - pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
    apply eq_refl.
  - pose proof firstn_length_le stk. 
    specialize (H (n_args + Datatypes.length idents)). 
    assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
    specialize (H H0). apply H.
  - invs COMP. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
    + constructor. rewrite firstn_length. lia.
    + pose proof stk_truncate_lp s s0 stk n_args idents fenv func_list NO H2 H4
      H6 OKparams H5 LEN H7 OK2 FWF. 
      invs H. invs H0. destruct H3. destruct H8. 
      pose proof list_chop_determ x x0 stk (n_args + Datatypes.length idents) H3 LEN H8.  
      rewrite H10. apply H9.
  - pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
    apply eq_refl.
  - pose proof firstn_length_le stk. 
    specialize (H (n_args + Datatypes.length idents)). 
    assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
    specialize (H H0). apply H.
  - invs COMP. invs SEM. invs WF. invs FAPPWF. invs TERM. econstructor.
    + specialize (IHd1_1 s0 stk n_args idents fenv func_list NO H3 H7 H9 
      OKparams H1 LEN H11 OK2 FWF).
      invs IHd1_1. invs H. invs H0. destruct H4. 
      pose proof list_chop_determ x x0 (x ++ x0) (n_args + Datatypes.length idents) eq_refl LEN H2.  
      rewrite H13. apply H4.
    + specialize (IHd1_2 s2 stk n_args idents fenv func_list NO H5 H8 H10 
      OKparams H6 LEN H12 OK2 FWF).
      invs IHd1_2. invs H. invs H0. destruct H4. 
      pose proof list_chop_determ x x0 (x ++ x0) (n_args + Datatypes.length idents) eq_refl LEN H2.  
      rewrite H13. apply H4.
  - pose proof firstn_skipn (n_args + Datatypes.length idents) stk; rewrite H.
    apply eq_refl.
  - pose proof firstn_length_le stk. 
    specialize (H (n_args + Datatypes.length idents)). 
    assert (n_args + Datatypes.length idents <= Datatypes.length stk) by lia.
    specialize (H H0). apply H.
  - invs COMP; invs SEM; invs WF; invs FAPPWF; invs TERM.
    + apply RelAbsOrLeft. specialize (IHd1_1 s0 stk n_args idents fenv func_list NO H3 H6 H8 
      OKparams H4 LEN H10 OK2 FWF).
      invs IHd1_1. invs H. invs H0. destruct H2. 
      pose proof list_chop_determ x x0 (x ++ x0) (n_args + Datatypes.length idents) eq_refl LEN H1.  
      rewrite H12. apply H2.
    + apply RelAbsOrRight. specialize (IHd1_2 s2 stk n_args idents fenv func_list NO H5 H7 H9 
      OKparams H4 LEN H11 OK2 FWF).
      invs IHd1_2. invs H. invs H0. destruct H2. 
      pose proof list_chop_determ x x0 (x ++ x0) (n_args + Datatypes.length idents) eq_refl LEN H1.  
      rewrite H12. apply H2.
Qed. 
