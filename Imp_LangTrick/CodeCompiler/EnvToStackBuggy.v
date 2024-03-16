From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet ZArith.
From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogicHelpers StackLanguage StackLangTheorems.
From Imp_LangTrick Require Export ImpVarMap.


Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.




Fixpoint count_aexp (expr: aexp_Imp_Lang) : nat :=
  match expr with
  | CONST_Imp_Lang _ => 0
  | VAR_Imp_Lang _ => 0
  | PARAM_Imp_Lang _ => 0
  | PLUS_Imp_Lang a1 a2 => (count_aexp a1) + (count_aexp a2)
  | MINUS_Imp_Lang a1 a2 => (count_aexp a1) + (count_aexp a2)
  | APP_Imp_Lang _ args =>
      List.fold_left (fun sum arg => sum + (count_aexp arg)) args 0
  end.
    
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

Fixpoint syntactic_aexp_equality_broken a1 a2 :=
  match (a1, a2) with
  |(CONST_Imp_Lang n1, CONST_Imp_Lang n2) => n1 =? n2
  |(VAR_Imp_Lang x, VAR_Imp_Lang y) => String.eqb x y
  |(PARAM_Imp_Lang n1, PARAM_Imp_Lang n2) => n1 =? n2
  |(PLUS_Imp_Lang e1 e2, PLUS_Imp_Lang e3 e4) => andb (syntactic_aexp_equality_broken e1 e3) (syntactic_aexp_equality_broken e2 e4)
  |(MINUS_Imp_Lang e1 e2, MINUS_Imp_Lang e3 e4) => andb (syntactic_aexp_equality_broken e1 e3) (syntactic_aexp_equality_broken e2 e4)
  | (APP_Imp_Lang f1 aexps1, APP_Imp_Lang f2 aexps2) => false
  | _ => false
  end. 

  (* (((Var_Stk 3) <=s (Var_Stk 2)) &s (!s ((Var_Stk 3) <=s (Var_Stk 2)) &s ((Var_Stk 2) <=s (Var_Stk 3)))) *)


(* Converts a IMP_LANG boolean expression [exp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Imp_Lang expression to 
the stack expression*)
Fixpoint compile_bexp (exp: bexp_Imp_Lang) (map: ident -> nat) (num_local_vars: nat) := 
  match exp with
  | AND_Imp_Lang (LEQ_Imp_Lang a1 a2) (NEG_Imp_Lang (AND_Imp_Lang (LEQ_Imp_Lang a3 a4) (LEQ_Imp_Lang a6 a5))) => if syntactic_aexp_equality_broken a1 a3 then 
      if syntactic_aexp_equality_broken a3 a5 then 
        if syntactic_aexp_equality_broken a2 a4 then 
          if syntactic_aexp_equality_broken a4 a6 then
    Neg_Stk ((Leq_Stk (compile_aexp a2 map num_local_vars))
    (compile_aexp a1 map num_local_vars))
    else True_Stk else True_Stk else True_Stk else True_Stk
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
      Assign_Stk (map x) (compile_aexp a map num_local_vars)
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
  ; Return_expr := Plus_Stk ((Return_expr) pre_fun) (Const_Stk 1)
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
