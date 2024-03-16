From Coq Require Import List String Peano Arith Psatz.
From Imp_LangTrick Require Import Imp_LangTrickLanguage ImpVarMap ImpVarMapTheorems EnvToStack.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive fun_app_well_formed : fun_env -> list fun_Imp_Lang -> aexp_Imp_Lang -> Prop :=
| fun_app_const :
  forall fenv wf_funcs n,
    fun_app_well_formed fenv wf_funcs (CONST_Imp_Lang n)
| fun_app_param :
  forall fenv wf_funcs p,
    fun_app_well_formed fenv wf_funcs (PARAM_Imp_Lang p)
| fun_app_var :
  forall fenv wf_funcs x,
    fun_app_well_formed fenv wf_funcs (VAR_Imp_Lang x)
| fun_app_plus :
  forall fenv wf_funcs a1 a2,
    fun_app_well_formed fenv wf_funcs a1 ->
    fun_app_well_formed fenv wf_funcs a2 ->
    fun_app_well_formed fenv wf_funcs (PLUS_Imp_Lang a1 a2)
| fun_app_minus :
  forall fenv wf_funcs a1 a2,
    fun_app_well_formed fenv wf_funcs a1 ->
    fun_app_well_formed fenv wf_funcs a2 ->
    fun_app_well_formed fenv wf_funcs (MINUS_Imp_Lang a1 a2)
| fun_app_this_fun :
  forall fenv wf_funcs args f func,
    fun_app_args_well_formed fenv wf_funcs args ->
    (* Mostly for convenience *)
    func = fenv f ->
    In func wf_funcs ->
    (* We call it with the right number of args *)
    Imp_LangTrickLanguage.Args func = Datatypes.length args ->
    (* This ensures that imp actually contains the return variable, so that it ends up in the mapping at compile time *)
    imp_has_variable (Imp_LangTrickLanguage.Ret func) (Imp_LangTrickLanguage.Body func) ->
    (* The name of the function is what we think it is, or it's the default (the identity function) *)
    (Imp_LangTrickLanguage.Name func = f \/ Imp_LangTrickLanguage.Name func = "id") ->
    (* (* And then, of course, we want the body of the function to contain well-formed applications *) *)
    fun_app_well_formed fenv wf_funcs (APP_Imp_Lang f args)
with fun_app_args_well_formed : fun_env -> list fun_Imp_Lang -> list aexp_Imp_Lang -> Prop :=
| fun_app_args_nil :
  forall fenv wf_funcs,
    fun_app_args_well_formed fenv wf_funcs nil
| fun_app_args_cons :
  forall fenv wf_funcs arg args,
    fun_app_well_formed fenv wf_funcs arg ->
    fun_app_args_well_formed fenv wf_funcs args ->
    fun_app_args_well_formed fenv wf_funcs (arg :: args)
with fun_app_bexp_well_formed : fun_env -> list fun_Imp_Lang -> bexp_Imp_Lang -> Prop :=
| fun_app_true :
  forall fenv wf_funcs ,
    fun_app_bexp_well_formed fenv wf_funcs (TRUE_Imp_Lang)
| fun_app_false :
  forall fenv wf_funcs ,
    fun_app_bexp_well_formed fenv wf_funcs (FALSE_Imp_Lang)
| fun_app_neg :
  forall fenv wf_funcs b,
    fun_app_bexp_well_formed fenv wf_funcs b ->
    fun_app_bexp_well_formed fenv wf_funcs (NEG_Imp_Lang b)
| fun_app_and :
  forall fenv wf_funcs b1 b2,
    fun_app_bexp_well_formed fenv wf_funcs b1 ->
    fun_app_bexp_well_formed fenv wf_funcs b2 ->
    fun_app_bexp_well_formed fenv wf_funcs (AND_Imp_Lang b1 b2)
| fun_app_or :
  forall fenv wf_funcs b1 b2,
    fun_app_bexp_well_formed fenv wf_funcs b1 ->
    fun_app_bexp_well_formed fenv wf_funcs b2 ->
    fun_app_bexp_well_formed fenv wf_funcs (OR_Imp_Lang b1 b2)
| fun_app_leq :
  forall fenv wf_funcs a1 a2,
    fun_app_well_formed fenv wf_funcs a1 ->
    fun_app_well_formed fenv wf_funcs a2 ->
    fun_app_bexp_well_formed fenv wf_funcs (LEQ_Imp_Lang a1 a2)
with fun_app_imp_well_formed : fun_env -> list fun_Imp_Lang -> imp_Imp_Lang -> Prop :=
| fun_app_skip :
  forall fenv wf_funcs,
    fun_app_imp_well_formed fenv wf_funcs SKIP_Imp_Lang
| fun_app_assign :
  forall fenv wf_funcs x a,
    fun_app_well_formed fenv wf_funcs a ->
    fun_app_imp_well_formed fenv wf_funcs (ASSIGN_Imp_Lang x a)
| fun_app_seq :
  forall fenv wf_funcs i1 i2,
    fun_app_imp_well_formed fenv wf_funcs i1 ->
    fun_app_imp_well_formed fenv wf_funcs i2 ->
    fun_app_imp_well_formed fenv wf_funcs (SEQ_Imp_Lang i1 i2)
| fun_app_if :
  forall fenv wf_funcs b i1 i2,
    fun_app_bexp_well_formed fenv wf_funcs b ->
    fun_app_imp_well_formed fenv wf_funcs i1 ->
    fun_app_imp_well_formed fenv wf_funcs i2 ->
    fun_app_imp_well_formed fenv wf_funcs (IF_Imp_Lang b i1 i2)
| fun_app_while :
  forall fenv wf_funcs b i,
    fun_app_bexp_well_formed fenv wf_funcs b ->
    fun_app_imp_well_formed fenv wf_funcs i ->
    fun_app_imp_well_formed fenv wf_funcs (WHILE_Imp_Lang b i).

Definition obind {A B: Type} (x: option A) (f: A -> option B) : option B :=
  match x with
  | Some x => f x
  | None => None
  end.

Definition obind2 {A B C: Type} (f: A -> B -> option C) (a: option A) (b: option B) : option C :=
  match a with
  | Some a' => obind b (f a')
  | None => None
  end.

Definition set_union_option (s1 s2: option (ListSet.set ident)): option (ListSet.set ident) :=
  obind2 (fun a b => Some (ListSet.set_union string_dec a b)) s1 s2.

Fixpoint collect_all_func_names_imp (fenv: fun_env) (fuel: nat) (i: imp_Imp_Lang): option (ListSet.set ident) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match i with
      | ASSIGN_Imp_Lang x a => collect_all_func_names_aexp fenv fuel' a
      | SEQ_Imp_Lang i1 i2 =>
          set_union_option
            (collect_all_func_names_imp fenv fuel' i1)
            (collect_all_func_names_imp fenv fuel' i2)
      | IF_Imp_Lang b i1 i2 =>
          set_union_option
            (collect_all_func_names_bexp fenv fuel' b)
            (set_union_option
               (collect_all_func_names_imp fenv fuel' i1)
               (collect_all_func_names_imp fenv fuel' i2))
      | WHILE_Imp_Lang b i =>
          set_union_option
            (collect_all_func_names_bexp fenv fuel' b)
            (collect_all_func_names_imp fenv fuel' i)
      | _ => Some (ListSet.empty_set ident)
      end
  end
with collect_all_func_names_aexp (fenv: fun_env) (fuel: nat) (a: aexp_Imp_Lang): option (ListSet.set ident) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match a with
           | PLUS_Imp_Lang a1 a2
           | MINUS_Imp_Lang a1 a2 =>
               set_union_option
                 (collect_all_func_names_aexp fenv fuel' a1)
                 (collect_all_func_names_aexp fenv fuel' a2)
           | APP_Imp_Lang f args =>
               obind (collect_all_func_names_args fenv fuel' args) (fun s => Some (ListSet.set_add string_dec f s))
           | _ =>
               Some (ListSet.empty_set ident)
           end
       end
with collect_all_func_names_args (fenv: fun_env) (fuel: nat) (args: list aexp_Imp_Lang): option (ListSet.set ident) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match args with
           | nil => Some (ListSet.empty_set ident)
           | arg :: args' =>
               set_union_option (collect_all_func_names_aexp fenv fuel' arg) (collect_all_func_names_args fenv fuel' args')
           end
       end
with collect_all_func_names_bexp (fenv: fun_env) (fuel: nat) (b: bexp_Imp_Lang): option (ListSet.set ident) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match b with
           | NEG_Imp_Lang b => collect_all_func_names_bexp fenv fuel' b
           | AND_Imp_Lang b1 b2
           | OR_Imp_Lang b1 b2 =>
               set_union_option
                 (collect_all_func_names_bexp fenv fuel' b1)
                 (collect_all_func_names_bexp fenv fuel' b2)
           | LEQ_Imp_Lang a1 a2 =>
               set_union_option
                 (collect_all_func_names_aexp fenv fuel' a1)
                 (collect_all_func_names_aexp fenv fuel' a2)
           | _ =>
               Some (ListSet.empty_set ident)
           end
       end.

Definition default_fuel := 100000.

Definition collect_all_func_names_funcs (fenv: fun_env) (fident_list: list ident): option (ListSet.set ident) :=
  fold_left (fun (acc: option (ListSet.set ident)) (x: ident) => set_union_option (collect_all_func_names_imp fenv default_fuel (Imp_LangTrickLanguage.Body (fenv x))) acc) fident_list (Some fident_list).

Fixpoint collect_all_funcs_names (fenv: fun_env) (fuel: nat) (fident_list: ListSet.set ident): option (ListSet.set ident) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      let new_fident_list := collect_all_func_names_funcs fenv fident_list in
      match new_fident_list with
      | None => None
      | Some new_fident_list' =>
          if list_eq_dec string_dec new_fident_list' fident_list
          then Some fident_list
          else collect_all_funcs_names fenv fuel' (new_fident_list')
      end
  end.

Definition fenv_well_formed_aexp (fenv: fun_env) (a: aexp_Imp_Lang) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Imp_Lang),
    Some first_fident_list = (collect_all_func_names_aexp fenv default_fuel a) ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_well_formed fenv func_list a.

Definition fenv_well_formed_bexp (fenv: fun_env) (b: bexp_Imp_Lang) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Imp_Lang),
    Some first_fident_list = collect_all_func_names_bexp fenv default_fuel b ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_bexp_well_formed fenv func_list b.

Definition fenv_well_formed_args (fenv: fun_env) (args: list aexp_Imp_Lang) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Imp_Lang),
    Some first_fident_list = collect_all_func_names_args fenv default_fuel args ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_args_well_formed fenv func_list args.


Definition fenv_well_formed (fenv: fun_env) (i: imp_Imp_Lang) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Imp_Lang),
    Some first_fident_list = (collect_all_func_names_imp fenv default_fuel i) ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_imp_well_formed fenv func_list i.

Definition construct_func_list (fenv: fun_env) (maybe_list: option (ListSet.set ident)): option (list fun_Imp_Lang) :=
  option_map (map fenv) (obind maybe_list (collect_all_funcs_names fenv default_fuel)).

Definition construct_imp_func_list (fenv: fun_env) (i: imp_Imp_Lang): option (list fun_Imp_Lang) :=
  construct_func_list fenv (collect_all_func_names_imp fenv default_fuel i).

Definition construct_aexp_func_list (fenv: fun_env) (a: aexp_Imp_Lang): option (list fun_Imp_Lang) :=
  construct_func_list fenv (collect_all_func_names_aexp fenv default_fuel a).

Definition construct_bexp_func_list (fenv: fun_env) (b: bexp_Imp_Lang): option (list fun_Imp_Lang) :=
  construct_func_list fenv (collect_all_func_names_bexp fenv default_fuel b).

Definition construct_args_func_list (fenv: fun_env) (args: list aexp_Imp_Lang): option (list fun_Imp_Lang) :=
  construct_func_list fenv (collect_all_func_names_args fenv default_fuel args).

Ltac unfold_func_wf_consts_in H :=
  unfold construct_imp_func_list, construct_aexp_func_list, construct_bexp_func_list, construct_args_func_list in H;
  unfold construct_func_list in H.

Definition fenv_well_formed' (funcs: list fun_Imp_Lang) (fenv: fun_env): Prop :=
  NoDup funcs /\
    (forall (f: ident) (func: fun_Imp_Lang),
      func = fenv f ->
      (In func funcs \/ func = init_fenv "id") /\
        fun_app_imp_well_formed fenv funcs (Imp_LangTrickLanguage.Body func) /\
        imp_has_variable (Imp_LangTrickLanguage.Ret func) (Imp_LangTrickLanguage.Body func)) /\
    NoDup (List.map Imp_LangTrickLanguage.Name funcs) /\
    (forall (func: fun_Imp_Lang),
        In func funcs ->
        forall (f: ident),
        forall (IN_FUNC_NAMES : In f (List.map Imp_LangTrickLanguage.Name funcs)),
          func = fenv f ->
          f = (Imp_LangTrickLanguage.Name func)) /\
    In (init_fenv "id") funcs /\
    (forall (f: ident),
        ~ (In f (List.map Imp_LangTrickLanguage.Name funcs)) ->
        fenv f = init_fenv "id") /\
    (* the following is an attempt to better characterize the fenvs, but i don't think this helps either *)
    (forall (func: fun_Imp_Lang) (f: ident),
        func = fenv f ->
        In func funcs ->
        exists fname,
          In fname (List.map Imp_LangTrickLanguage.Name funcs) /\
            fenv f = fenv fname /\
            fname = Imp_LangTrickLanguage.Name func)
        
     .

