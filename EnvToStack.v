From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet ZArith.
From DanTrick Require Import DanTrickLanguage DanLogicHelpers StackLanguage StackLangEval StackLangTheorems.
From DanTrick Require Export ImpVarMap.


Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.




Fixpoint count_aexp (expr: aexp_Dan) : nat :=
  match expr with
  | CONST_Dan _ => 0
  | VAR_Dan _ => 0
  | PARAM_Dan _ => 0
  | PLUS_Dan a1 a2 => (count_aexp a1) + (count_aexp a2)
  | MINUS_Dan a1 a2 => (count_aexp a1) + (count_aexp a2)
  | APP_Dan _ args =>
      List.fold_left (fun sum arg => sum + (count_aexp arg)) args 0
  end.
    
(* Converts a DAN arithmetic expression [exp] with [args] number of arguments
and a given variable-to-index mapping [stack], converts Dan expression to 
the stack expression*)
Fixpoint compile_aexp (exp: aexp_Dan) (ident_to_index: ident -> nat) (num_local_vars: nat): aexp_stack :=
  match exp with
  | CONST_Dan n =>
      Const_Stk n
  | VAR_Dan x =>
      Var_Stk ((ident_to_index x))
  | PARAM_Dan n =>
      Var_Stk (num_local_vars + n + 1)
  | PLUS_Dan a1 a2 =>
      Plus_Stk (compile_aexp a1 ident_to_index num_local_vars)
               (compile_aexp a2 ident_to_index num_local_vars)
  | MINUS_Dan a1 a2 =>
      Minus_Stk (compile_aexp a1 ident_to_index num_local_vars)
                (compile_aexp a2 ident_to_index num_local_vars)
  | APP_Dan f aexps => 
      let comp_args :=
        List.map (fun x => compile_aexp x ident_to_index num_local_vars)
                 aexps in
      App_Stk f comp_args
  end.


Inductive rcompile_aexp : list ident -> aexp_Dan -> aexp_stack -> Prop :=
| RelCompConst :
  forall map n,
    rcompile_aexp map (CONST_Dan n) (Const_Stk n)
| RelCompVar :
  forall map x k,
    k = one_index_opt x map ->
    rcompile_aexp map (VAR_Dan x) (Var_Stk k)
| RelCompParam :
  forall map n k,
    k = Datatypes.length map + n + 1 ->
    rcompile_aexp map (PARAM_Dan n) (Var_Stk k)
| RelCompPlus :
  forall map a1 a2 a1' a2',
    rcompile_aexp map a1 a1' ->
    rcompile_aexp map a2 a2' ->
    rcompile_aexp map (PLUS_Dan a1 a2) (Plus_Stk a1' a2')
| RelCompMinus :
  forall map a1 a2 a1' a2',
    rcompile_aexp map a1 a1' ->
    rcompile_aexp map a2 a2' ->
    rcompile_aexp map (MINUS_Dan a1 a2) (Minus_Stk a1' a2')
| RelCompApp :
  forall map f exprs exprs',
    rcompile_args map exprs exprs' ->
    rcompile_aexp map (APP_Dan f exprs) (App_Stk f exprs')
with rcompile_args : list ident -> list aexp_Dan -> list aexp_stack -> Prop :=
| RelCompArgsNil :
  forall map,
    rcompile_args map nil nil
| RelCompArgsCons :
  forall map expr exprs expr' exprs',
    rcompile_aexp map expr expr' ->
    rcompile_args map exprs exprs' ->
    rcompile_args map (expr :: exprs) (expr' :: exprs')
with rcompile_bexp : list ident -> bexp_Dan -> bexp_stack -> Prop :=
| RelCompTrue :
  forall idents,
    rcompile_bexp idents TRUE_Dan True_Stk
| RelCompFalse :
  forall idents,
    rcompile_bexp idents FALSE_Dan False_Stk
| RelCompNeg :
  forall idents b b',
    rcompile_bexp idents b b' ->
    rcompile_bexp idents (NEG_Dan b) (Neg_Stk b')
| RelCompAnd :
  forall idents b1 b2 b1' b2',
    rcompile_bexp idents b1 b1' ->
    rcompile_bexp idents b2 b2' ->
    rcompile_bexp idents (AND_Dan b1 b2) (And_Stk b1' b2')
| RelCompOr :
  forall idents b1 b2 b1' b2',
    rcompile_bexp idents b1 b1' ->
    rcompile_bexp idents b2 b2' ->
    rcompile_bexp idents (OR_Dan b1 b2) (Or_Stk b1' b2')
| RelCompLeq :
  forall idents a1 a2 a1' a2',
    rcompile_aexp idents a1 a1' ->
    rcompile_aexp idents a2 a2' ->
    rcompile_bexp idents (LEQ_Dan a1 a2) (Leq_Stk a1' a2')
with rcompile_imp: list ident -> imp_Dan -> imp_stack -> Prop :=
| RelCompSkip :
  forall idents,
    rcompile_imp idents SKIP_Dan Skip_Stk
| RelCompAssign :
  forall idents x a k a',
    k = one_index_opt x idents ->
    rcompile_aexp idents a a' ->
    rcompile_imp idents (ASSIGN_Dan x a) (Assign_Stk k a')
| RelCompSeq :
  forall idents i1 i2 i1' i2',
    rcompile_imp idents i1 i1' ->
    rcompile_imp idents i2 i2' ->
    rcompile_imp idents (SEQ_Dan i1 i2) (Seq_Stk i1' i2')
| RelCompIf :
  forall idents b i1 i2 b' i1' i2',
    rcompile_bexp idents b b' ->
    rcompile_imp idents i1 i1' ->
    rcompile_imp idents i2 i2' ->
    rcompile_imp idents (IF_Dan b i1 i2) (If_Stk b' i1' i2')
| RelCompWhile :
  forall idents b i b' i',
    rcompile_bexp idents b b' ->
    rcompile_imp idents i i' ->
    rcompile_imp idents (WHILE_Dan b i) (While_Stk b' i').


Scheme rcompile_aexp_mut_ind := Induction for rcompile_aexp Sort Prop
    with rcompile_args_mut_ind := Induction for rcompile_args Sort Prop.

Combined Scheme rcompile_aexp_args_mut_ind from rcompile_aexp_mut_ind, rcompile_args_mut_ind.


Definition
  rcompile_aexp_args_mut_ind_theorem (P: list ident -> aexp_Dan -> aexp_stack -> Prop)
  (P0: list ident -> list aexp_Dan -> list aexp_stack -> Prop) : Prop :=
  (forall (map: list ident) (adan: aexp_Dan) (astk: aexp_stack),
      rcompile_aexp map adan astk ->
      P map adan astk) /\
    (forall (map: list ident) (adans: list aexp_Dan) (astks: list aexp_stack),
        rcompile_args map adans astks ->
        P0 map adans astks).

Local Definition rcompile_aexp_args_mut_ind_theorem_P (P: list ident -> aexp_Dan -> aexp_stack -> Prop):
  forall (l: list ident) (a: aexp_Dan) (a0: aexp_stack), rcompile_aexp l a a0 -> Prop :=
  fun (map: list ident) (adan: aexp_Dan) (astk: aexp_stack) =>
  fun (_: rcompile_aexp map adan astk) =>
    P map adan astk.

Local Definition rcompile_aexp_args_mut_ind_theorem_P0 (P0: list ident -> list aexp_Dan -> list aexp_stack -> Prop):
  forall (l: list ident) (l0: list aexp_Dan) (l1: list aexp_stack), rcompile_args l l0 l1 -> Prop :=
  fun (map: list ident) (adans: list aexp_Dan) (astks: list aexp_stack) =>
  fun (_: rcompile_args map adans astks) =>
    P0 map adans astks.

Ltac rcompile_aexp_args_mutual_induction P P0 P_def P0_def :=
  pose (rcompile_aexp_args_mut_ind_theorem_P P_def) as P;
  pose (rcompile_aexp_args_mut_ind_theorem_P0 P0_def) as P0;
  apply (rcompile_aexp_args_mut_ind P P0);
  unfold P, P0; unfold rcompile_aexp_args_mut_ind_theorem_P, rcompile_aexp_args_mut_ind_theorem_P0;
  unfold P_def, P0_def.

Local Definition rcompile_adequate_P (map: list ident) (adan: aexp_Dan) (astk: aexp_stack) : Prop :=
  astk = compile_aexp adan (fun x => one_index_opt x map) (List.length map).

Local Definition rcompile_adequate_P0 (map: list ident) (adans: list aexp_Dan) (astks: list aexp_stack) : Prop :=
  astks = List.map (fun x => compile_aexp x (fun x' => one_index_opt x' map) (List.length map)) adans.


Ltac unfold_everything_once :=
  match goal with
  | [ |- ?sth1 ?sth2 ?sth3 ] =>
      try (unfold sth1);
      try (unfold sth2);
      try (unfold sth3)
  end.

Lemma compile_aexp_args_adequate_forward :
  rcompile_aexp_args_mut_ind_theorem rcompile_adequate_P rcompile_adequate_P0.
Proof.
  unfold_everything_once.
  
  rcompile_aexp_args_mutual_induction P P0 rcompile_adequate_P rcompile_adequate_P0; intros.
  - simpl. reflexivity.
  - simpl. rewrite <- e. reflexivity.
  - simpl. rewrite e. reflexivity.
  - simpl. rewrite H, H0. reflexivity.
  - rewrite H, H0; simpl; reflexivity.
  - rewrite H. simpl; reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite H0, H. reflexivity.
Qed.

Lemma compile_aexp_args_adequate_forward' :
  (forall (map : list ident) (adan : aexp_Dan) (astk : aexp_stack),
      rcompile_aexp map adan astk ->
      astk =
        compile_aexp
          adan
          (fun x : ident => one_index_opt x map)
          (Datatypes.length map)) /\
  (forall (map : list ident) (adans : list aexp_Dan) (astks : list aexp_stack),
      rcompile_args map adans astks ->
      astks =
        List.map
          (fun x : aexp_Dan =>
             compile_aexp
               x
               (fun x' : ident => one_index_opt x' map)
               (Datatypes.length map))
          adans).
Proof.
  pose proof (compile_aexp_args_adequate_forward).
  eapply H.
Qed.

Lemma compile_aexp_adequate_forward :
  forall (map : list ident) (adan : aexp_Dan) (astk : aexp_stack),
      rcompile_aexp map adan astk ->
      astk =
        compile_aexp
          adan
          (fun x : ident => one_index_opt x map)
          (Datatypes.length map).
Proof.
  pose proof (COMP := compile_aexp_args_adequate_forward').
  destruct COMP as (AEXP & _).
  exact AEXP.
Qed.

Lemma compile_args_adequate_forward :
  forall (map : list ident) (adans : list aexp_Dan) (astks : list aexp_stack),
      rcompile_args map adans astks ->
      astks =
        List.map
          (fun x : aexp_Dan =>
             compile_aexp
               x
               (fun x' : ident => one_index_opt x' map)
               (Datatypes.length map))
          adans.
Proof.
  pose proof (COMP := compile_aexp_args_adequate_forward').
  destruct COMP as (_ & ARGS).
  exact ARGS.
Qed.



     


Lemma compile_aexp_args_adequate_backwards :
  forall (map: list ident) (adan: aexp_Dan) (astk: aexp_stack),
    astk = compile_aexp adan (fun x => one_index_opt x map) (List.length map) ->
    rcompile_aexp map adan astk.
Proof.
  intros map adan.
  revert map.
  apply (aexp_Dan_ind2
           (fun adan => forall (map : list ident) (astk : aexp_stack),
                astk =
                  compile_aexp adan
                               (fun x : DanTrickLanguage.ident => one_index_opt x map)
                               (Datatypes.length map) ->
                rcompile_aexp map adan astk));
    intros.
  - simpl in H. rewrite H. econstructor.
  - simpl in H. rewrite H. econstructor. reflexivity.
  - simpl in H. rewrite H. econstructor.
    reflexivity.
  - simpl in H1. rewrite H1. econstructor.
    + eapply H. reflexivity.
    + eapply H0; reflexivity.
  - simpl in H1; rewrite H1; econstructor; [eapply H | eapply H0 ]; reflexivity.
  - simpl in H0. subst.
    econstructor. induction H.
    + simpl. econstructor.
    + simpl. econstructor; eauto. 
Qed.

(* This version uses ident_list_to_map *)
Lemma compile_aexp_args_adequate_backwards' :
  forall (map: list ident) (n_args: nat) (adan: aexp_Dan) (astk: aexp_stack),
    astk = compile_aexp adan (ident_list_to_map map) (List.length map) ->
    rcompile_aexp map adan astk.
Proof.
  pose proof (compile_aexp_args_adequate_backwards) as H.
  unfold ident_list_to_map.
  intros. eapply H. assumption.
Qed.

Lemma compile_aexp_args_adequate :
  forall (idents: list ident) (adan: aexp_Dan) (astk: aexp_stack),
    rcompile_aexp idents adan astk <->
      astk = compile_aexp adan (fun x => one_index_opt x idents) (List.length idents).
Proof.
  split.
  - apply compile_aexp_args_adequate_forward.
  - apply compile_aexp_args_adequate_backwards.
Qed.




(* Converts a DAN boolean expression [exp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Dan expression to 
the stack expression*)
Fixpoint compile_bexp (exp: bexp_Dan) (map: ident -> nat) (num_local_vars: nat) := 
  match exp with
  | TRUE_Dan => True_Stk
  | FALSE_Dan => False_Stk
  | NEG_Dan b =>
      Neg_Stk (compile_bexp b map num_local_vars)
  | AND_Dan b1 b2 =>
      And_Stk (compile_bexp b1 map num_local_vars)
              (compile_bexp b2 map num_local_vars)
  | OR_Dan  b1 b2 =>
      Or_Stk (compile_bexp b1 map num_local_vars)
             (compile_bexp b2 map num_local_vars)
  | LEQ_Dan a1 a2 =>
      Leq_Stk (compile_aexp a1 map num_local_vars)
              (compile_aexp a2 map num_local_vars)
  end
.

  



Lemma compile_bexp_adequate_forward :
  forall (b: bexp_Dan) (idents: list ident) (b': bexp_stack),
    rcompile_bexp idents b b' ->
    b' = compile_bexp b (fun x => one_index_opt x idents) (List.length idents).
Proof.
  induction b; intros; invs H.
  - reflexivity.
  - reflexivity.
  - simpl. eapply IHb in H2. rewrite H2. reflexivity.
  - simpl. apply IHb1 in H3. apply IHb2 in H5. rewrite H3, H5. reflexivity.
  - apply IHb1 in H3. apply IHb2 in H5. rewrite H3, H5. reflexivity.
  - apply compile_aexp_adequate_forward in H3, H5.
    rewrite H3, H5.
    reflexivity.
Qed.

Lemma compile_bexp_adequate_backward :
  forall (b: bexp_Dan) (idents: list ident) (b': bexp_stack),
    b' = compile_bexp b (fun x => one_index_opt x idents) (List.length idents) ->
    rcompile_bexp idents b b'.
Proof.
  induction b; intros; simpl in H; rewrite H.
  - constructor.
  - constructor.
  - constructor. apply IHb.
    reflexivity.
  - constructor; [ apply IHb1 | apply IHb2 ]; reflexivity.
  - constructor; [ apply IHb1 | apply IHb2 ]; reflexivity.
  - constructor; apply compile_aexp_args_adequate_backwards; reflexivity.
Qed.

Lemma compile_bexp_adequate :
  forall (b: bexp_Dan) (idents: list ident) (b': bexp_stack),
    rcompile_bexp idents b b' <->
      b' = compile_bexp b (fun x => one_index_opt x idents) (List.length idents).
Proof.
  split; [ apply compile_bexp_adequate_forward | apply compile_bexp_adequate_backward ].
Qed.


(* Converts a DAN imperative command [imp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Dan expression to 
the stack expression *)
Fixpoint compile_imp (imp: imp_Dan) (map: ident -> nat) (num_local_vars: nat) :=
  match imp with
  | SKIP_Dan => Skip_Stk
  | ASSIGN_Dan x a =>
      Assign_Stk (map x)
                 (compile_aexp a map num_local_vars)
  | SEQ_Dan i1 i2 =>
      Seq_Stk (compile_imp i1 map num_local_vars)
              (compile_imp i2 map num_local_vars)
  | IF_Dan b i1 i2 => 
      If_Stk (compile_bexp b map num_local_vars)
             (compile_imp i1 map num_local_vars)
             (compile_imp i2 map num_local_vars)
  | WHILE_Dan b i =>
      While_Stk (compile_bexp b map num_local_vars)
                (compile_imp i map num_local_vars)
  end
.




Scheme rcomp_imp_aexp_ind := Induction for rcompile_aexp Sort Prop
    with rcomp_imp_args_ind := Induction for rcompile_args Sort Prop
                               with rcomp_imp_bexp_ind := Induction for rcompile_bexp Sort Prop
                               with rcomp_imp_imp_ind := Induction for rcompile_imp Sort Prop.

Combined Scheme rcomp_imp_mut_ind from rcomp_imp_aexp_ind, rcomp_imp_args_ind, rcomp_imp_bexp_ind, rcomp_imp_imp_ind.
                                        

Lemma compile_imp_adequate_forward :
  forall (i: imp_Dan) (idents: list ident) (i': imp_stack),
    rcompile_imp idents i i' ->
    i' = compile_imp i (fun x => one_index_opt x idents) (List.length idents).
Proof.
  induction i; intros; invs H.
  - apply IHi1 in H6. apply IHi2 in H7. apply compile_bexp_adequate in H4. rewrite H4, H6, H7. reflexivity.
  - reflexivity.
  - apply IHi in H5. apply compile_bexp_adequate in H3. rewrite H3, H5. reflexivity.
  - apply compile_aexp_args_adequate in H5.
    rewrite H5. reflexivity.
  - apply IHi1 in H3. apply IHi2 in H5. rewrite H3, H5. reflexivity.
Qed.

Lemma compile_imp_adequate_backward :
  forall (i: imp_Dan) (idents: list ident) (i': imp_stack),
    i' = compile_imp i (fun x => one_index_opt x idents) (List.length idents) ->
    rcompile_imp idents i i'.
Proof.
  induction i; intros; simpl in H; rewrite H.
  - constructor.
    + apply compile_bexp_adequate; reflexivity.
    + apply IHi1. reflexivity.
    + apply IHi2. reflexivity.
  - constructor.
  - constructor.
    + apply compile_bexp_adequate. reflexivity.
    + apply IHi. reflexivity.
  - constructor.
    + reflexivity.
    + apply compile_aexp_args_adequate. reflexivity.
  - constructor.
    + apply IHi1. reflexivity.
    + apply IHi2. reflexivity.
Qed.

Lemma compile_imp_adequate :
  forall (i: imp_Dan) (idents: list ident) (i': imp_stack),
    rcompile_imp idents i i' <->
      i' = compile_imp i (fun x => one_index_opt x idents) (List.length idents).
Proof.
  split.
  - apply compile_imp_adequate_forward.
  - apply compile_imp_adequate_backward.
Qed.




Fixpoint prepend_push exp n :=
  match n with
  | S m => prepend_push (Seq_Stk (Push_Stk) (exp)) m
  | 0 => exp
  end.

Fixpoint append_pop exp n :=
  match n with
  |S m => append_pop (Seq_Stk (exp) (Pop_Stk)) m
  |0 => exp
  end.

Definition push_n n :=
  match n with
  | S m => prepend_push Push_Stk m
  | 0 => Skip_Stk
  end.

Definition pop_n n :=
  match n with
  | S m => append_pop Pop_Stk m
  | 0 => Skip_Stk
  end.


(* compiles a program, then adds the number of variables ocurring in exp
  plus [args] pushes to the beginning of the program *)


(* Might be easier to have a record than to have a tuple that you keep having to rememmber the contents of *)
Record compiled_code :=
  { Pushes : option imp_stack
  ; Code : imp_stack
  ; Pops : option imp_stack
  ; VarStack : list ident
  ; VarMap : ident -> nat }.

Record compiled_function :=
  { cfName : ident
  ; cfArgs : nat
  ; cfPushes : option imp_stack
  ; cfCode : imp_stack
  ; cfVarStack : list ident
  ; cfVarMap : ident -> nat
  ; cfReturn_expr : aexp_stack
  ; cfReturn_pop : nat
  }.

Definition construct_code_body (c: compiled_code): imp_stack :=
  let rest_of_code := (match (Pops c) with
                       | Some sequence_of_pops =>
                           Seq_Stk (Code c) sequence_of_pops
                       | None => (Code c)
                       end) in
  match (Pushes c) with
  | Some sequence_of_pushes =>
      Seq_Stk sequence_of_pushes
              rest_of_code
  | None =>
      rest_of_code
  end.

Definition construct_function_body (c: compiled_function): imp_stack :=
  match (cfPushes c) with
  | Some sequence_of_pushes =>
      Seq_Stk sequence_of_pushes (cfCode c)
  | None => cfCode c
  end.

Definition compile_code exp: (imp_stack * list ident) :=
  let stk := construct_trans exp in
  let mapping := stack_mapping exp in
  let pre_push_comp := compile_imp exp mapping (List.length stk) in
  ((prepend_push pre_push_comp ((length stk))), stk)
.


Local Definition another_program :=
    "x" <- ((VAR_Dan "y") +d (VAR_Dan "z")) ;;
    "x" <- ((VAR_Dan "z") -d (VAR_Dan "y")) ;;
    "y" <- (PARAM_Dan 0).

Compute (compile_code another_program).


Definition compiled_code_proof_amenable (code: imp_Dan): compiled_code :=
  let stk := construct_trans code in
  let mapping := stack_mapping code in
  let stack_length := List.length stk in
  let comp_code := compile_imp code mapping stack_length in
  {|
    Pushes := (match stack_length with
               | 0 => None
               | _ => Some (push_n stack_length)
               end)
  ; Code := comp_code
  ; Pops := (match stack_length with
             | 0 => None
             | _ => Some (pop_n stack_length)
             end)
  ; VarStack := stk
  ; VarMap := mapping
  |}.

Definition pre_compile_function (f: fun_Dan) : fun_stk :=
  let body := ((DanTrickLanguage.Body) f) in
  let stk := construct_trans body in
  let mapping := stack_mapping body in
  {| Name := ((DanTrickLanguage.Name) f)
  ; Args := (DanTrickLanguage.Args) f
  ; Body := fst (compile_code ((DanTrickLanguage.Body) f))
  ; Return_expr := Var_Stk ((mapping ((DanTrickLanguage.Ret) f)))
  ; Return_pop := (List.length stk)|}
.

Definition pre_compile_function_proof_amenable (f: fun_Dan) : compiled_function :=
  let body := ((DanTrickLanguage.Body) f) in
  let compiled_body := compiled_code_proof_amenable body in
  let mapping := (VarMap compiled_body) in
  let stk := (VarStack compiled_body) in
  {|
    cfName := ((DanTrickLanguage.Name) f)
  ; cfArgs := (DanTrickLanguage.Args) f
  ; cfPushes := (Pushes compiled_body)
  ; cfCode := (Code compiled_body)
  ; cfVarStack := stk
  ; cfVarMap := (VarMap compiled_body)
  ; cfReturn_expr := Var_Stk ((mapping ((DanTrickLanguage.Ret) f)))
  ; cfReturn_pop := (List.length stk)
  |}.

Definition compiled_function_to_fun_stk (cf: compiled_function): fun_stk :=
  {|
    Name := cfName cf
  ; Args := cfArgs cf
  ; Body := construct_function_body cf
  ; Return_expr := cfReturn_expr cf
  ; Return_pop := cfReturn_pop cf
  |}.




Definition compile_function f :=
  let pre_fun := pre_compile_function f in
  {| Name := (Name) pre_fun
  ; Args := (Args) pre_fun
  ; Body := ((Body) pre_fun)
  ; Return_expr := (Return_expr) pre_fun
  ; Return_pop :=  (Return_pop) pre_fun
  |}.

Definition compile_fenv f :=
  fun (id : DanTrickLanguage.ident) => compile_function (f id). 

Definition compile_prog prog :=
  match prog with
  |PROF_Dan funs i => 
  let comp_pair := compile_code i in
     (Prog_Stk (List.map compile_function funs) (fst comp_pair), snd comp_pair)
  end. 


Definition x : ident := "x". 

Definition max_function_body : imp_Dan := (* a, b are parameters *)
  "a" <- (PARAM_Dan 0) ;;
  "b" <- (PARAM_Dan 1) ;;
  when (a >d b) then "ret" <- a else "ret" <- b done.


Definition max_fun: fun_Dan :=
  {| DanTrickLanguage.Name := "max"
  ; DanTrickLanguage.Args := 2
  ; DanTrickLanguage.Ret := "ret"
  ; DanTrickLanguage.Body := max_function_body |}.


(* The idea behind this definition is to define what it means to quotient an
environment out by a stack. *)


(* args and env are from source, translation is variable -> stack translation in
 the form of a list as above in construct_trans and sig and stack are the stack 
 signature and target stack we're trying to evaluate respectively. Basically, 
 if we translate [args] and [env] under [trans] and quotient under [sig], is
 [stack] in this set.  *)
Definition quotient_stack_eq (args : list nat) env (trans : list string) (sig : nat) (stk : list nat) : Prop := 
  let trans_stack := args ++ (List.map (fun x => env x) trans) in
  forall x, x < sig -> (List.nth) x trans_stack = List.nth x stk.

Lemma test_one_element : 
  quotient_stack_eq nil init_nenv ("y"::nil) 1 (0::nil).
Proof.
  unfold quotient_stack_eq. 
  intros.
  inversion H.
  -simpl. unfold init_nenv. auto.
  -simpl. unfold init_nenv. auto.        
Qed.  
  
Lemma test_args : 
  quotient_stack_eq (10::11::nil) init_nenv ("y"::nil) 0 (0::10::11::nil).
Proof. 
  unfold quotient_stack_eq. 
  intros.
  inversion H.
Qed. 



(* Correctness statement *)

Fixpoint construct_stack_fenv lst (f: fun_env_stk) : fun_env_stk :=
  match lst with
  | nil => f
  | foo :: foos => construct_stack_fenv foos (update ((foo).(Name)) foo f)
  end.

Inductive aexp_stack_changed: aexp_stack -> fun_env_stk -> Z -> Prop :=
| Const_stkchng :
  forall fenv n,
    aexp_stack_changed (Const_Stk n) fenv ((BinInt.Z.of_nat) 0)
| Var_stkchng :
  forall fenv k,
    aexp_stack_changed (Var_Stk k) fenv ((BinInt.Z.of_nat) 0)
| Plus_stkchng :
  forall fenv a1 a2 n1 n2,
    aexp_stack_changed a1 fenv n1 ->
    aexp_stack_changed a2 fenv n2 ->
    aexp_stack_changed (Plus_Stk a1 a2) fenv (n1 + n2)
| Minus_stkchng :
  forall fenv a1 a2 n1 n2,
    aexp_stack_changed a1 fenv n1 ->
    aexp_stack_changed a2 fenv n2 ->
    aexp_stack_changed (Minus_Stk a1 a2) fenv (n1 + n2)
| App_stkchng :
  forall fenv f func args zchngargs zfbodychng,
    fenv f = func ->
    args_stack_changed args fenv zchngargs ->
    imp_stack_changed (Body func) fenv zfbodychng ->
    aexp_stack_changed (App_Stk f args) fenv (zchngargs + zfbodychng - (Z.of_nat (Args func + Return_pop func)))%Z
with args_stack_changed : list aexp_stack -> fun_env_stk -> Z -> Prop :=
| Args_nil_stkchng :
  forall fenv,
    args_stack_changed nil fenv (0)%Z
| Args_cons_stkchng :
  forall fenv first_arg args first_changed rest_changed,
    aexp_stack_changed first_arg fenv first_changed ->
    args_stack_changed args fenv rest_changed ->
    args_stack_changed (first_arg :: args) fenv (first_changed + rest_changed)
with bexp_stack_changed : bexp_stack -> fun_env_stk -> Z -> Prop :=
| True_stkchng :
  forall fenv,
    bexp_stack_changed True_Stk fenv ((Z.of_nat) 0)
| False_stkchng :
  forall fenv,
    bexp_stack_changed False_Stk fenv ((Z.of_nat) 0)
| Neg_stkchng :
  forall fenv b n,
    bexp_stack_changed b fenv n ->
    bexp_stack_changed (Neg_Stk b) fenv n
| And_stkchng :
  forall fenv b1 b2 n1 n2,
    bexp_stack_changed b1 fenv n1 ->
    bexp_stack_changed b2 fenv n2 ->
    bexp_stack_changed (And_Stk b1 b2) fenv (n1 + n2)
| Or_stkchng :
  forall fenv b1 b2 n1 n2,
    bexp_stack_changed b1 fenv n1 ->
    bexp_stack_changed b2 fenv n2 ->
    bexp_stack_changed (Or_Stk b1 b2) fenv (n1 + n2)
| Leq_stkchng :
  forall fenv a1 a2 n1 n2,
    aexp_stack_changed a1 fenv n1 ->
    aexp_stack_changed a2 fenv n2 ->
    bexp_stack_changed (Leq_Stk a1 a2) fenv (n1 + n2)
| Eq_stkchng :
  forall fenv a1 a2 n1 n2,
    aexp_stack_changed a1 fenv n1 ->
    aexp_stack_changed a2 fenv n2 ->
    bexp_stack_changed (Eq_Stk a1 a2) fenv (n1 + n2)
with imp_stack_changed : imp_stack -> fun_env_stk -> Z -> Prop :=
| Skip_stkchng :
  forall fenv,
    imp_stack_changed Skip_Stk fenv ((Z.of_nat) 0)
| Assign_stkchng :
  forall fenv (k: stack_index) (a: aexp_stack) (na: Z),
    aexp_stack_changed a fenv na ->
    imp_stack_changed (Assign_Stk k a) fenv na
| Pop_stkchng :
  forall fenv,
    imp_stack_changed (Pop_Stk) fenv (-1)%Z
| Push_stkchng :
  forall fenv,
    imp_stack_changed (Push_Stk) fenv 1%Z
| Seq_stkchng :
  forall fenv i1 i2 n1 n2,
    imp_stack_changed i1 fenv n1 ->
    imp_stack_changed i2 fenv n2 ->
    imp_stack_changed (Seq_Stk i1 i2) fenv (n1 + n2)
| Seq_ifchng :
  forall fenv b i1 i2 nb n1 n2,
    bexp_stack_changed b fenv nb ->
    imp_stack_changed i1 fenv n1 ->
    imp_stack_changed i2 fenv n2 ->
    n1 = n2 ->
    imp_stack_changed (If_Stk b i1 i2) fenv n1
| While_ifchng :
  forall fenv b loop_body nb,
    bexp_stack_changed b fenv nb ->
    imp_stack_changed loop_body fenv (0)%Z ->
    imp_stack_changed (While_Stk b loop_body) fenv nb.

Definition all_fenv_fxns_in_compiler_codomain (fenv: fun_env_stk): Prop :=
  forall (f_id: ident) (f: fun_stk),
    fenv f_id = f ->
    exists f',
      f = compile_function f'.
