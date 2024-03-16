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
Fixpoint compile_aexp_incomplete (exp: aexp_Imp_Lang) (ident_to_index: ident -> nat) (num_local_vars: nat): aexp_stack :=
  match exp with
  | CONST_Imp_Lang n =>
      Const_Stk n
  | VAR_Imp_Lang x =>
      Var_Stk ((ident_to_index x))
  | PARAM_Imp_Lang n =>
      Var_Stk (num_local_vars + n + 1)
  | PLUS_Imp_Lang a1 a2 =>
      Plus_Stk (compile_aexp_incomplete a1 ident_to_index num_local_vars)
               (compile_aexp_incomplete a2 ident_to_index num_local_vars)
  | MINUS_Imp_Lang a1 a2 =>
      Minus_Stk (compile_aexp_incomplete a1 ident_to_index num_local_vars)
                (compile_aexp_incomplete a2 ident_to_index num_local_vars)
  | APP_Imp_Lang f aexps => 
      let comp_args :=
        List.map (fun x => compile_aexp_incomplete x ident_to_index num_local_vars)
                 aexps in
      App_Stk f comp_args
  end.



(* Converts a IMP_LANG boolean expression [exp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Imp_Lang expression to 
the stack expression*)
Definition compile_bexp_incomplete (exp: bexp_Imp_Lang) (map: ident -> nat) (num_local_vars: nat) := 
  match exp with
  | TRUE_Imp_Lang => True_Stk
  | FALSE_Imp_Lang => False_Stk
  | _ => True_Stk
  end
.

  




(* Converts a IMP_LANG imperative command [imp] with [args] number of arguments
and a given variable-to-index mapping [map], converts Imp_Lang expression to 
the stack expression *)
Definition compile_imp_incomplete (imp: imp_Imp_Lang) (map: ident -> nat) (num_local_vars: nat) :=
  match imp with
  (* | SKIP_Imp_Lang => Skip_Stk *)
  | ASSIGN_Imp_Lang x a =>
      Assign_Stk (map x)
                 (compile_aexp_incomplete a map num_local_vars)
  | _ => Skip_Stk
  (* | SEQ_Imp_Lang i1 i2 => *)
      (* Seq_Stk (compile_imp_incomplete i1 map num_local_vars) *)
              (* (compile_imp_incomplete i2 map num_local_vars) *)
  (* | IF_Imp_Lang b i1 i2 =>  *)
      (* If_Stk (compile_bexp_incomplete b map num_local_vars) *)
             (* (compile_imp_incomplete i1 map num_local_vars) *)
             (* (compile_imp_incomplete i2 map num_local_vars) *)
  (* | WHILE_Imp_Lang b i => *)
      (* While_Stk (compile_bexp_incomplete b map num_local_vars) *)
                (* (compile_imp_incomplete i map num_local_vars) *)
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
Record compiled_code_incomplete :=
  { Pushes : option imp_stack
  ; Code : imp_stack
  ; Pops : option imp_stack
  ; VarStack : list ident
  ; VarMap : ident -> nat }.

Record compiled_function_incomplete :=
  { cfName : ident
  ; cfArgs : nat
  ; cfPushes : option imp_stack
  ; cfCode : imp_stack
  ; cfVarStack : list ident
  ; cfVarMap : ident -> nat
  ; cfReturn_expr : aexp_stack
  ; cfReturn_pop : nat
  }.

Definition construct_code_body_incomplete (c: compiled_code_incomplete): imp_stack :=
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

Definition construct_function_body_incomplete (c: compiled_function_incomplete): imp_stack :=
  match (cfPushes c) with
  | Some sequence_of_pushes =>
      Seq_Stk sequence_of_pushes (cfCode c)
  | None => cfCode c
  end.

Definition compile_code_incomplete exp: (imp_stack * list ident) :=
  let stk := construct_trans exp in
  let mapping := stack_mapping exp in
  let pre_push_comp := compile_imp_incomplete exp mapping (List.length stk) in
  ((prepend_push pre_push_comp ((length stk))), stk)
.

Definition compiled_code_proof_amenable_incomplete (code: imp_Imp_Lang): compiled_code_incomplete :=
  let stk := construct_trans code in
  let mapping := stack_mapping code in
  let stack_length := List.length stk in
  let comp_code := compile_imp_incomplete code mapping stack_length in
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

Definition pre_compile_function_incomplete (f: fun_Imp_Lang) : fun_stk :=
  let body := ((Imp_LangTrickLanguage.Body) f) in
  let stk := construct_trans body in
  let mapping := stack_mapping body in
  {| Name := ((Imp_LangTrickLanguage.Name) f)
  ; Args := (Imp_LangTrickLanguage.Args) f
  ; Body := fst (compile_code_incomplete ((Imp_LangTrickLanguage.Body) f))
  ; Return_expr := Var_Stk ((mapping ((Imp_LangTrickLanguage.Ret) f)))
  ; Return_pop := (List.length stk)|}
.

Definition pre_compile_function_incomplete_proof_amenable_incomplete (f: fun_Imp_Lang) : compiled_function_incomplete :=
  let body := ((Imp_LangTrickLanguage.Body) f) in
  let compiled_body := compiled_code_proof_amenable_incomplete body in
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

Definition compiled_function_to_fun_stk_incomplete (cf: compiled_function_incomplete): fun_stk :=
  {|
    Name := cfName cf
  ; Args := cfArgs cf
  ; Body := construct_function_body_incomplete cf
  ; Return_expr := cfReturn_expr cf
  ; Return_pop := cfReturn_pop cf
  |}.




Definition compile_function_incomplete f :=
  let pre_fun := pre_compile_function_incomplete f in
  {| Name := (Name) pre_fun
  ; Args := (Args) pre_fun
  ; Body := ((Body) pre_fun)
  ; Return_expr := (Return_expr) pre_fun
  ; Return_pop :=  (Return_pop) pre_fun
  |}.

Definition compile_fenv_incomplete f :=
  fun (id : ident) => compile_function_incomplete (f id). 

Definition compile_prog_incomplete prog :=
  match prog with
  |PROF_Imp_Lang funs i => 
  let comp_pair := compile_code_incomplete i in
     (Prog_Stk (List.map compile_function_incomplete funs) (fst comp_pair), snd comp_pair)
  end. 
