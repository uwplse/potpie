From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet ZArith.
From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogicHelpers Imp_LangLogProp Imp_LangLogHoare LogicProp StackLanguage StackLangTheorems ProofCompilableCodeCompiler ProofCompilerCodeCompAgnostic StackUpdateAdequacy StackLogic FunctionWellFormed ParamsWellFormed StackLogicBase TranslationPure.
From Imp_LangTrick Require Export ImpVarMap.
Import EqNotations.


Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.
    
(* Converts a IMP_LANG arithmetic expression [exp] with [args] number of arguments
and a given variable-to-index mapping [stack], converts Imp_Lang expression to 
the stack expression*)
Fixpoint compile_aexp (exp: aexp_Imp_Lang) (ident_to_index: ident -> nat) (num_local_vars: nat): aexp_stack :=
  match exp with
  | CONST_Imp_Lang n =>
      Const_Stk n
  | VAR_Imp_Lang x =>
      Var_Stk ((ident_to_index x))
  | PARAM_Imp_Lang n =>
      Var_Stk (num_local_vars + n + 1)
  | PLUS_Imp_Lang a1 a2 =>
      Plus_Stk (compile_aexp a1 ident_to_index num_local_vars)
               (compile_aexp a2 ident_to_index num_local_vars)
  | MINUS_Imp_Lang a1 a2 =>
      Minus_Stk (compile_aexp a1 ident_to_index num_local_vars)
                (compile_aexp a2 ident_to_index num_local_vars)
  | APP_Imp_Lang f aexps => 
      let comp_args :=
        List.map (fun x => compile_aexp x ident_to_index num_local_vars)
                 aexps in
      App_Stk f comp_args
  end.

(* Converts a IMP_LANG boolean expression [exp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Imp_Lang expression to 
the stack expression*)
Fixpoint compile_bexp (exp: bexp_Imp_Lang) (map: ident -> nat) (num_local_vars: nat) := 
  match exp with
  |  AND_Imp_Lang (LEQ_Imp_Lang a b) 
      (NEG_Imp_Lang 
        (AND_Imp_Lang (LEQ_Imp_Lang c d) 
          (LEQ_Imp_Lang f e))) => 
      Leq_Stk (compile_aexp a map num_local_vars)
              (compile_aexp b map num_local_vars)
  | TRUE_Imp_Lang => True_Stk
  | FALSE_Imp_Lang => False_Stk
  | NEG_Imp_Lang b =>
      Neg_Stk (compile_bexp b map num_local_vars)
  | AND_Imp_Lang b1 b2 =>
      And_Stk (compile_bexp b1 map num_local_vars)
              (compile_bexp b2 map num_local_vars)
  | OR_Imp_Lang  b1 b2 =>
      Or_Stk (compile_bexp b1 map num_local_vars)
             (compile_bexp b2 map num_local_vars)
  | LEQ_Imp_Lang a1 a2 =>
      Leq_Stk (compile_aexp a1 map num_local_vars)
              (compile_aexp a2 map num_local_vars)
  end
.

(* Converts a IMP_LANG imperative command [imp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Imp_Lang expression to 
the stack expression *)
Fixpoint compile_imp (imp: imp_Imp_Lang) (map: ident -> nat) (num_local_vars: nat) :=
  match imp with
  | SKIP_Imp_Lang => Skip_Stk
  | ASSIGN_Imp_Lang x a =>
      Assign_Stk (map x)
                 (compile_aexp a map num_local_vars)
  | SEQ_Imp_Lang i1 i2 =>
      Seq_Stk (compile_imp i1 map num_local_vars)
              (compile_imp i2 map num_local_vars)
  | IF_Imp_Lang b i1 i2 => 
      If_Stk (compile_bexp b map num_local_vars)
             (compile_imp i1 map num_local_vars)
             (compile_imp i2 map num_local_vars)
  | WHILE_Imp_Lang b i =>
      While_Stk (compile_bexp b map num_local_vars)
                (compile_imp i map num_local_vars)
  end
.

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
    "x" <- ((VAR_Imp_Lang "y") +d (VAR_Imp_Lang "z")) ;;
    "x" <- ((VAR_Imp_Lang "z") -d (VAR_Imp_Lang "y")) ;;
    "y" <- (PARAM_Imp_Lang 0).

Compute (compile_code another_program).


Definition compiled_code_proof_amenable (code: imp_Imp_Lang): compiled_code :=
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

Definition pre_compile_function (f: fun_Imp_Lang) : fun_stk :=
  let body := ((Imp_LangTrickLanguage.Body) f) in
  let stk := construct_trans body in
  let mapping := stack_mapping body in
  {| Name := ((Imp_LangTrickLanguage.Name) f)
  ; Args := (Imp_LangTrickLanguage.Args) f
  ; Body := fst (compile_code ((Imp_LangTrickLanguage.Body) f))
  ; Return_expr := Var_Stk ((mapping ((Imp_LangTrickLanguage.Ret) f)))
  ; Return_pop := (List.length stk)|}
.

Definition pre_compile_function_proof_amenable (f: fun_Imp_Lang) : compiled_function :=
  let body := ((Imp_LangTrickLanguage.Body) f) in
  let compiled_body := compiled_code_proof_amenable body in
  let mapping := (VarMap compiled_body) in
  let stk := (VarStack compiled_body) in
  {|
    cfName := ((Imp_LangTrickLanguage.Name) f)
  ; cfArgs := (Imp_LangTrickLanguage.Args) f
  ; cfPushes := (Pushes compiled_body)
  ; cfCode := (Code compiled_body)
  ; cfVarStack := stk
  ; cfVarMap := (VarMap compiled_body)
  ; cfReturn_expr := Var_Stk ((mapping ((Imp_LangTrickLanguage.Ret) f)))
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
  fun (id : ident) => compile_function (f id). 

Definition compile_prog prog :=
  match prog with
  |PROF_Imp_Lang funs i => 
  let comp_pair := compile_code i in
     (Prog_Stk (List.map compile_function funs) (fst comp_pair), snd comp_pair)
  end. 


Definition x : ident := "x". 

Definition max_function_body : imp_Imp_Lang := (* a, b are parameters *)
  "a" <- (PARAM_Imp_Lang 0) ;;
  "b" <- (PARAM_Imp_Lang 1) ;;
  when (a >d b) then "ret" <- a else "ret" <- b done.


Definition max_fun: fun_Imp_Lang :=
  {| Imp_LangTrickLanguage.Name := "max"
  ; Imp_LangTrickLanguage.Args := 2
  ; Imp_LangTrickLanguage.Ret := "ret"
  ; Imp_LangTrickLanguage.Body := max_function_body |}.


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


Module LTtoLEQ <: CodeCompilerType. 
  Definition compile_aexp (exp: aexp_Imp_Lang) (idents: list ident) (num_locals: nat): aexp_stack :=
    compile_aexp exp (ident_list_to_map idents) num_locals.

  Definition compile_bexp (exp: bexp_Imp_Lang) (idents: list ident) (num_locals: nat): bexp_stack :=
    compile_bexp exp (ident_list_to_map idents) num_locals.

  Definition compile_imp (imp: imp_Imp_Lang) (idents: list ident) (num_locals: nat) :=
    compile_imp imp (ident_list_to_map idents) num_locals.

  Definition idents_to_map := ident_list_to_map.
End LTtoLEQ. 

Module CheckableLTtoLEQ := CreateBasicCheckableCodeCompiler(LTtoLEQ).

Module CheckableLTtoLEQSpec := CreateStandardCheckableLogicCompiler(CheckableLTtoLEQ) (BasicSpecificationChecker).

Module ProofCheckableLTtoLEQ := ProofChecker(CheckableLTtoLEQ) (CheckableLTtoLEQSpec).

Module LTtoLEQSetDefns := ProofCompilableSetDefinitions(CheckableLTtoLEQ) (CheckableLTtoLEQSpec).


Module LTtoLEQProofCompilable <: ProofCompilableType.
  Module CC := CheckableLTtoLEQ.
  Module SC := CheckableLTtoLEQSpec.

  Inductive check_proof (fenv: fun_env) (func_list: list fun_Imp_Lang) (d d': AbsEnv) (i: imp_Imp_Lang) (facts: implication_env) (idents: list ident) (args: nat): (hl_Imp_Lang d i d' facts fenv) -> Prop :=
  | CheckHLSkip :
    forall (hl: hl_Imp_Lang d i d' facts fenv),
    forall (Hi : SKIP_Imp_Lang = i),
    forall (Heq: d = d'),
      hl =
        rew [fun H : AbsEnv => hl_Imp_Lang d i H facts fenv] Heq in
      rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H d facts fenv] Hi in
        hl_Imp_Lang_skip d facts fenv ->
      SC.check_logic d = true ->
      CC.check_imp i = true ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLAssign :
     forall x a,
     forall (hl: hl_Imp_Lang d i d' facts fenv)
       (Hi : ASSIGN_Imp_Lang x a = i)
       (Heq : Imp_LangLogSubst.subst_AbsEnv x a d' = d),
       hl =
         rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Hi in
       rew [fun H: AbsEnv => hl_Imp_Lang H (ASSIGN_Imp_Lang x a) d' facts fenv] Heq in
         hl_Imp_Lang_assign d' facts fenv x a ->
         CC.check_aexp a = true ->
         StackExprWellFormed.aexp_well_formed (CC.compile_aexp a idents args) ->
         StackExprWellFormed.absstate_well_formed (SC.comp_logic args idents d') ->
         stack_large_enough_for_state (CC.idents_to_map idents x) (SC.comp_logic args idents d') ->
         CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
         SC.check_logic d = true ->
         SC.check_logic d' = true ->
         (forall fenv',
             fenv_well_formed' func_list fenv ->
             fun_app_well_formed fenv func_list a ->
             all_params_ok_aexp args a -> (* ...might not need this one *)
             var_map_wf_wrt_aexp idents a ->
             funcs_okay_too func_list fenv' ->
             StackPurestBase.aexp_stack_pure_rel (CC.compile_aexp a idents args) fenv') ->
         (forall s' k,
             SC.comp_logic args idents d' = s' ->
             var_map_wf_wrt_aexp idents a ->
             In x idents ->
             k = CC.idents_to_map idents x ->
             (* state_update k a_stk s' = s -> *)
             SC.comp_logic args idents (Imp_LangLogSubst.subst_AbsEnv x a d') = state_update k (CC.compile_aexp a idents args) s') ->
         check_proof fenv func_list d d' i facts idents args hl
  | CheckHLSeq :
    forall d0 i1 i2,
    forall (hl: hl_Imp_Lang d i d' facts fenv)
      (hl1: hl_Imp_Lang d i1 d0 facts fenv)
      (hl2: hl_Imp_Lang d0 i2 d' facts fenv),
    forall (Hi: SEQ_Imp_Lang i1 i2 = i),
      hl = rew [fun H : imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Hi in
        hl_Imp_Lang_seq d d' d0 facts fenv i1 i2 hl1 hl2 ->
      CC.check_imp i = true ->
      CC.check_imp i1 = true ->
      CC.check_imp i2 = true ->
      SC.check_logic d0 = true ->
      check_proof fenv func_list d d0 i1 facts idents args hl1 ->
      check_proof fenv func_list d0 d' i2 facts idents args hl2 ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLIf :
    forall b i1 i2,
    forall (hl1: hl_Imp_Lang (atrueImp_Lang b d) i1 d' facts fenv)
      (hl2: hl_Imp_Lang (afalseImp_Lang b d) i2 d' facts fenv)
      (Hi: IF_Imp_Lang b i1 i2 = i)
      (hl: hl_Imp_Lang d i d' facts fenv),
      hl =
         rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H d' facts fenv] Hi in
        hl_Imp_Lang_if d d' b i1 i2 facts fenv hl1 hl2 ->
      CC.check_bexp b = true ->
      CC.check_imp i1 = true ->
      CC.check_imp i = true ->
      CC.check_imp i2 = true ->
      (forall fenv',
          fenv_well_formed' func_list fenv ->
          fun_app_bexp_well_formed fenv func_list b ->
          var_map_wf_wrt_bexp idents b ->
          funcs_okay_too func_list fenv' ->
          StackPurestBase.bexp_stack_pure_rel (CC.compile_bexp b idents args) fenv') ->
      SC.check_logic (atrueImp_Lang b d) = true ->
      SC.check_logic (afalseImp_Lang b d) = true ->
      check_proof fenv func_list (atrueImp_Lang b d) d' i1 facts idents args hl1 ->
      check_proof fenv func_list (afalseImp_Lang b d) d' i2 facts idents args hl2 ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLWhile :
    forall b i__body,
    forall (hl__body: hl_Imp_Lang (atrueImp_Lang b d) i__body d facts fenv)
      (hl: hl_Imp_Lang d i d' facts fenv)
      (HeqP: afalseImp_Lang b d = d')
      (Hi: WHILE_Imp_Lang b i__body = i),
      hl =
        rew [fun H: AbsEnv => hl_Imp_Lang d i H facts fenv]
            HeqP in
      rew [fun H: imp_Imp_Lang => hl_Imp_Lang d H (afalseImp_Lang b d) facts fenv]
          Hi in
        hl_Imp_Lang_while d b i__body facts fenv hl__body ->
      CC.check_bexp b = true ->
      CC.check_imp i = true ->
      CC.check_imp i__body = true ->
      (forall fenv',
          fenv_well_formed' func_list fenv ->
          fun_app_bexp_well_formed fenv func_list b ->
          var_map_wf_wrt_bexp idents b ->
          funcs_okay_too func_list fenv' ->
          StackPurestBase.bexp_stack_pure_rel (CC.compile_bexp b idents args) fenv') ->
      SC.check_logic (atrueImp_Lang b d) = true ->
      SC.check_logic (afalseImp_Lang b d) = true ->
      check_proof fenv func_list (atrueImp_Lang b d) d i__body facts idents args hl__body ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLPre :
    forall P n,
    forall (hl: hl_Imp_Lang d i d' facts fenv)
      (hlP: hl_Imp_Lang P i d' facts fenv)
      (aimp: aimpImp_Lang d P fenv)
      (nth: nth_error facts n = Some (d, P)),
      hl = (hl_Imp_Lang_consequence_pre P d' d i n facts fenv hlP nth aimp) ->
      CC.check_imp i = true ->
      SC.check_logic P = true ->
      SC.check_logic d = true ->
      SC.check_logic d' = true ->
      check_proof fenv func_list P d' i facts idents args hlP ->
      check_proof fenv func_list d d' i facts idents args hl
  | CheckHLPost :
    forall Q n,
    forall (hl: hl_Imp_Lang d i d' facts fenv)
      (hlQ: hl_Imp_Lang d i Q facts fenv)
      (nth: nth_error facts n = Some (Q, d'))
      (aimp: aimpImp_Lang Q d' fenv),
      hl = (hl_Imp_Lang_consequence_post d Q d' i n facts fenv hlQ nth aimp) ->
      CC.check_imp i = true ->
      SC.check_logic Q = true ->
      SC.check_logic d = true ->
      SC.check_logic d' = true ->
      check_proof fenv func_list d Q i facts idents args hlQ ->
      check_proof fenv func_list d d' i facts idents args hl.

  Lemma spec_conjunction_commutes:
    forall (args: nat) (idents: list ident) (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
      SC.check_logic (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ val_to_prop b)))) = true ->
      SC.check_logic P = true ->
      CC.check_bexp b = true ->
      SC.comp_logic
        args
        idents
        (AbsEnvAnd P (AbsEnvLP (Imp_Lang_lp_bool (UnaryProp _ _ val_to_prop b))))
      =
        AbsAnd (SC.comp_logic args idents P)
               (BaseState
                  (AbsStkSize (args + Datatypes.length idents))
                  (MetaBool (UnaryProp _ _ val_to_prop (CC.compile_bexp b idents args)))).
  Proof.
    induction P; intros.
    - simpl. unfold SC.CC.compile_bexp. reflexivity.
    - simpl. unfold SC.CC.compile_bexp. reflexivity.
    - simpl. unfold SC.CC.compile_bexp. reflexivity.
  Qed.

  Lemma spec_lp_conjunction_check:
    forall (P: AbsEnv) (b: bexp_Imp_Lang) (val_to_prop: bool -> Prop),
      SC.check_logic P = true ->
      CC.check_bexp b = true ->
      SC.check_logic
        (AbsEnvAnd P
                   (AbsEnvLP
                      (Imp_Lang_lp_bool
                         (UnaryProp bool bexp_Imp_Lang
                                    val_to_prop b)))) = true.
  Proof.
    intros.
    unfold SC.check_logic. reflexivity.
  Qed.

  Lemma skip_compilation_okay: forall (args: nat) (idents: list ident),
      CC.check_imp SKIP_Imp_Lang = true ->
      CC.compile_imp SKIP_Imp_Lang idents args = Skip_Stk.
  Proof.
    intros. unfold CC.compile_imp. unfold compile_imp. reflexivity.
  Qed.
    
  Lemma assign_compilation_commutes: forall (args: nat) (idents: list ident) (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.compile_imp (ASSIGN_Imp_Lang x a) idents args = Assign_Stk (CC.idents_to_map idents x) (CC.compile_aexp a idents args).
  Proof.
    intros. unfold CC.compile_imp. unfold compile_imp. unfold CC.compile_aexp. reflexivity.
  Qed.

  Lemma assign_check_implies_assignee_check :
    forall (x: ident) (a: aexp_Imp_Lang),
      CC.check_imp (ASSIGN_Imp_Lang x a) = true ->
      CC.check_aexp a = true.
  Proof.
    intros. unfold CC.check_aexp. reflexivity.
  Qed.

  Lemma sequence_compilation_commutes: forall (args: nat) (idents: list ident) (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.compile_imp (SEQ_Imp_Lang i1 i2) idents args = Seq_Stk (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Proof.
    intros. unfold CC.compile_imp. simpl. reflexivity.
  Qed.

  Lemma sequence_check_implies_all_check :
    forall (i1 i2: imp_Imp_Lang),
      CC.check_imp (SEQ_Imp_Lang i1 i2) = true ->
      CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  Proof.
    intros. unfold CC.check_imp. split; reflexivity.
  Qed.
  
  Lemma if_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      CC.compile_imp (IF_Imp_Lang b i1 i2) idents args
      =
        If_Stk (CC.compile_bexp b idents args) (CC.compile_imp i1 idents args) (CC.compile_imp i2 idents args).
  Proof.
    intros. unfold CC.compile_bexp.  unfold CC.compile_imp.  simpl. reflexivity.
  Qed.
  
  Lemma if_check_implies_condition_then_else_check:
    forall (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang),
      CC.check_imp (IF_Imp_Lang b i1 i2) = true ->
      CC.check_bexp b = true /\ CC.check_imp i1 = true /\ CC.check_imp i2 = true.
  Proof.
    intros. unfold CC.check_bexp, CC.check_imp. repeat split; reflexivity.
  Qed.
  
  Lemma while_compilation_commutes: forall (args: nat) (idents: list ident) (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      CC.compile_imp (WHILE_Imp_Lang b i) idents args
      =
        While_Stk (CC.compile_bexp b idents args) (CC.compile_imp i idents args).
  Proof.
    intros. unfold CC.compile_imp. unfold CC.compile_bexp. reflexivity.
  Qed.
  Lemma while_check_implies_condition_loop_check :
    forall (b: bexp_Imp_Lang) (i: imp_Imp_Lang),
      CC.check_imp (WHILE_Imp_Lang b i) = true ->
      CC.check_bexp b = true /\ CC.check_imp i = true.
  Proof.
    intros. unfold CC.check_bexp, CC.check_imp. split; reflexivity.
  Qed.

  Lemma size_change_implication_okay : forall (s1 ARG : AbsState) (b : bexp_Imp_Lang)
         (idents : list ident) (n_args : nat) 
         (fenv : fun_env) (d : AbsEnv) (my_fun : bool -> Prop)
         (fenv' : fun_env_stk) (funcs : list fun_Imp_Lang),
       funcs_okay_too funcs fenv' ->
       fenv_well_formed' funcs fenv ->
       SC.comp_logic n_args idents d = s1 ->
       SC.check_logic d = true ->
       CC.check_bexp b = true ->
       ARG =
         AbsAnd s1
                (BaseState AbsStkTrue
                           (MetaBool
                              (UnaryProp bool bexp_stack my_fun
                                         (CC.compile_bexp b idents n_args)))) ->
       (aimpstk ARG
                (AbsAnd s1
                        (BaseState (AbsStkSize (Datatypes.length idents + n_args))
                                   (MetaBool
                                      (UnaryProp bool bexp_stack my_fun
                                                 (CC.compile_bexp b idents n_args)))))) fenv'.
  Proof.
    induction s1; unfold aimpstk; intros; subst.
    - destruct d eqn:Hd.
      + simpl in H1. invc H1. invc H5. econstructor.
        * eassumption.
        * invs H6. econstructor.
          -- rewrite Nat.add_comm. eassumption.
          -- invs H9. eassumption.
      + simpl in H1. invs H1.
      + simpl in H1. invs H1.
    - destruct d eqn:Hd; try solve [simpl in H1; invs H1].
      invc H5. invs H7.
      simpl in H1. invs H1.
      remember (SC.comp_logic n_args idents a1) as s1.
      remember (SC.comp_logic n_args idents a2) as s2.
      remember ((BaseState AbsStkTrue
             (MetaBool
                (UnaryProp bool bexp_stack my_fun
                   (CC.compile_bexp b idents n_args))))) as bm.
      assert (absstate_match_rel (AbsAnd s1 bm) fenv' stk) by (econstructor; eassumption).
      assert (absstate_match_rel (AbsAnd s2 bm) fenv' stk) by (econstructor; eassumption).
      eapply IHs1_1 in H4. eapply IHs1_2 in H5. inversion H5.
      econstructor.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + rewrite Heqs2. reflexivity.
      + eassumption.
      + eassumption.
      + rewrite Heqbm. reflexivity.
      + eassumption.
      + eassumption.
      + rewrite Heqs1. reflexivity.
      + eassumption.
      + eassumption.
      + rewrite Heqbm. reflexivity.
    - invc H5. 
      destruct d eqn:Hd; try solve [invs H1].
      simpl in H1.
      remember ((BaseState AbsStkTrue
             (MetaBool
                (UnaryProp bool bexp_stack my_fun
                   (CC.compile_bexp b idents n_args))))) as bm.
      inversion H1.
      inversion H7.
      subst s1. subst s2. subst fenv0. subst stk0.
      + assert (absstate_match_rel (AbsAnd s1_1 bm) fenv' stk) by (econstructor; eassumption).
        
        eapply IHs1_1 in H4. inversion H4.
        econstructor.
        * eapply RelAbsOrLeft. rewrite H5. eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * rewrite <- H5. reflexivity.
        * eassumption.
        * eassumption.
        * rewrite Heqbm. reflexivity.
      + assert (absstate_match_rel (AbsAnd s1_2 bm) fenv' stk) by (econstructor; eassumption).
        eapply IHs1_2 in H13. inversion H13. econstructor.
        * eapply RelAbsOrRight. rewrite H6. eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * rewrite <- H6. reflexivity.
        * eassumption.
        * eassumption.
        * rewrite Heqbm. reflexivity.
  Qed.

  Definition valid_imp_trans_def facts facts' (fenv : fun_env) fenv0 map args :=
    Datatypes.length facts <= Datatypes.length facts' /\
      (forall (n : nat) (P Q : AbsEnv) (P' Q' : AbsState),
          SC.check_logic P = true ->
          SC.check_logic Q = true ->
          SC.comp_logic args map P = P' ->
          SC.comp_logic args map Q = Q' ->
          nth_error facts n = Some (P, Q) ->
          nth_error facts' n = Some (P', Q') 
                  ) /\
      StackLogic.fact_env_valid facts' fenv0.
End LTtoLEQProofCompilable.

Module LTtoLEQCompilerAgnostic := 
  CompilerAgnosticProofCompiler(LTtoLEQProofCompilable).
  
Print LTtoLEQCompilerAgnostic. 
