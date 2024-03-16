From Coq Require Import List String.
From Imp_LangTrick.Imp Require Import Imp_LangTrickLanguage.

Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive all_params_ok : nat -> imp_Imp_Lang -> Prop :=
| all_params_ok_skip :
  forall (num_args: nat),
    all_params_ok num_args SKIP_Imp_Lang
| all_params_ok_assign :
  forall (num_args: nat) x a,
    all_params_ok_aexp num_args a ->
    all_params_ok num_args (ASSIGN_Imp_Lang x a)
| all_params_ok_seq :
  forall (num_args: nat) i1 i2,
    all_params_ok num_args i1 ->
    all_params_ok num_args i2 ->
    all_params_ok num_args (SEQ_Imp_Lang i1 i2)
| all_params_ok_if :
  forall (num_args: nat) b i1 i2,
    all_params_ok_bexp num_args b ->
    all_params_ok num_args i1 ->
    all_params_ok num_args i2 ->
    all_params_ok num_args (IF_Imp_Lang b i1 i2)
                  
| all_params_ok_while :
  forall (num_args: nat) b i_loop,
    all_params_ok_bexp num_args b ->
    all_params_ok num_args i_loop ->
    all_params_ok num_args (WHILE_Imp_Lang b i_loop)
with all_params_ok_bexp : nat -> bexp_Imp_Lang -> Prop :=
| all_params_ok_bexp_true :
  forall (num_args: nat),
    all_params_ok_bexp num_args TRUE_Imp_Lang
| all_params_ok_bexp_false :
  forall (num_args: nat),
    all_params_ok_bexp num_args FALSE_Imp_Lang
| all_params_ok_bexp_neg :
  forall (num_args: nat) (b: bexp_Imp_Lang),
    all_params_ok_bexp num_args b ->
    all_params_ok_bexp num_args (NEG_Imp_Lang b)
| all_params_ok_bexp_and :
  forall (num_args: nat) (b1 b2: bexp_Imp_Lang),
    all_params_ok_bexp num_args b1 ->
    all_params_ok_bexp num_args b2 ->
    all_params_ok_bexp num_args (AND_Imp_Lang b1 b2)
| all_params_ok_bexp_or :
  forall (num_args: nat) (b1 b2: bexp_Imp_Lang),
    all_params_ok_bexp num_args b1 ->
    all_params_ok_bexp num_args b2 ->
    all_params_ok_bexp num_args (OR_Imp_Lang b1 b2)
| all_params_ok_bexp_leq :
  forall (num_args: nat) (a1 a2: aexp_Imp_Lang),
    all_params_ok_aexp num_args a1 ->
    all_params_ok_aexp num_args a2 ->
    all_params_ok_bexp num_args (LEQ_Imp_Lang a1 a2)
with all_params_ok_aexp : nat -> aexp_Imp_Lang -> Prop :=
| all_params_ok_aexp_const :
  forall (num_args: nat) (n: nat),
    all_params_ok_aexp num_args (CONST_Imp_Lang n)
| all_params_ok_aexp_param :
  forall (num_args: nat) (p: nat),
    (* params are 0-indexed *)
    p < num_args ->
    all_params_ok_aexp num_args (PARAM_Imp_Lang p)
| all_params_ok_aexp_var :
  forall (num_args: nat) (x: string),
    all_params_ok_aexp num_args (VAR_Imp_Lang x)
| all_params_ok_aexp_plus :
  forall (num_args: nat) (a1 a2: aexp_Imp_Lang),
    all_params_ok_aexp num_args a1 ->
    all_params_ok_aexp num_args a2 ->
    all_params_ok_aexp num_args (PLUS_Imp_Lang a1 a2)
| all_params_ok_aexp_minus :
  forall (num_args: nat) (a1 a2: aexp_Imp_Lang),
    all_params_ok_aexp num_args a1 ->
    all_params_ok_aexp num_args a2 ->
    all_params_ok_aexp num_args (MINUS_Imp_Lang a1 a2)
| all_params_ok_aexp_app :
  forall (num_args: nat) (f: ident) (args: list aexp_Imp_Lang),
    all_params_ok_args num_args args ->
    all_params_ok_aexp num_args (APP_Imp_Lang f args)
with all_params_ok_args : nat -> list aexp_Imp_Lang -> Prop :=
| all_params_ok_args_nil :
  forall (num_args: nat),
    all_params_ok_args num_args nil
| all_params_ok_args_cons :
  forall (num_args: nat) (arg: aexp_Imp_Lang) (args: list aexp_Imp_Lang),
    all_params_ok_aexp num_args arg ->
    all_params_ok_args num_args args ->
    all_params_ok_args num_args (arg :: args).
