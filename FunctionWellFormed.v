From Coq Require Import List String Peano Arith Psatz.
From DanTrick Require Import DanTrickLanguage ImpVarMap ImpVarMapTheorems EnvToStack.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive fun_app_well_formed : fun_env -> list fun_Dan -> aexp_Dan -> Prop :=
| fun_app_const :
  forall fenv wf_funcs n,
    fun_app_well_formed fenv wf_funcs (CONST_Dan n)
| fun_app_param :
  forall fenv wf_funcs p,
    fun_app_well_formed fenv wf_funcs (PARAM_Dan p)
| fun_app_var :
  forall fenv wf_funcs x,
    fun_app_well_formed fenv wf_funcs (VAR_Dan x)
| fun_app_plus :
  forall fenv wf_funcs a1 a2,
    fun_app_well_formed fenv wf_funcs a1 ->
    fun_app_well_formed fenv wf_funcs a2 ->
    fun_app_well_formed fenv wf_funcs (PLUS_Dan a1 a2)
| fun_app_minus :
  forall fenv wf_funcs a1 a2,
    fun_app_well_formed fenv wf_funcs a1 ->
    fun_app_well_formed fenv wf_funcs a2 ->
    fun_app_well_formed fenv wf_funcs (MINUS_Dan a1 a2)
| fun_app_this_fun :
  forall fenv wf_funcs args f func,
    fun_app_args_well_formed fenv wf_funcs args ->
    (* Mostly for convenience *)
    func = fenv f ->
    In func wf_funcs ->
    (* We call it with the right number of args *)
    DanTrickLanguage.Args func = Datatypes.length args ->
    (* This ensures that imp actually contains the return variable, so that it ends up in the mapping at compile time *)
    imp_has_variable (DanTrickLanguage.Ret func) (DanTrickLanguage.Body func) ->
    (* The name of the function is what we think it is, or it's the default (the identity function) *)
    (DanTrickLanguage.Name func = f \/ DanTrickLanguage.Name func = "id") ->
    (* (* And then, of course, we want the body of the function to contain well-formed applications *) *)
    fun_app_well_formed fenv wf_funcs (APP_Dan f args)
with fun_app_args_well_formed : fun_env -> list fun_Dan -> list aexp_Dan -> Prop :=
| fun_app_args_nil :
  forall fenv wf_funcs,
    fun_app_args_well_formed fenv wf_funcs nil
| fun_app_args_cons :
  forall fenv wf_funcs arg args,
    fun_app_well_formed fenv wf_funcs arg ->
    fun_app_args_well_formed fenv wf_funcs args ->
    fun_app_args_well_formed fenv wf_funcs (arg :: args)
with fun_app_bexp_well_formed : fun_env -> list fun_Dan -> bexp_Dan -> Prop :=
| fun_app_true :
  forall fenv wf_funcs ,
    fun_app_bexp_well_formed fenv wf_funcs (TRUE_Dan)
| fun_app_false :
  forall fenv wf_funcs ,
    fun_app_bexp_well_formed fenv wf_funcs (FALSE_Dan)
| fun_app_neg :
  forall fenv wf_funcs b,
    fun_app_bexp_well_formed fenv wf_funcs b ->
    fun_app_bexp_well_formed fenv wf_funcs (NEG_Dan b)
| fun_app_and :
  forall fenv wf_funcs b1 b2,
    fun_app_bexp_well_formed fenv wf_funcs b1 ->
    fun_app_bexp_well_formed fenv wf_funcs b2 ->
    fun_app_bexp_well_formed fenv wf_funcs (AND_Dan b1 b2)
| fun_app_or :
  forall fenv wf_funcs b1 b2,
    fun_app_bexp_well_formed fenv wf_funcs b1 ->
    fun_app_bexp_well_formed fenv wf_funcs b2 ->
    fun_app_bexp_well_formed fenv wf_funcs (OR_Dan b1 b2)
| fun_app_leq :
  forall fenv wf_funcs a1 a2,
    fun_app_well_formed fenv wf_funcs a1 ->
    fun_app_well_formed fenv wf_funcs a2 ->
    fun_app_bexp_well_formed fenv wf_funcs (LEQ_Dan a1 a2)
with fun_app_imp_well_formed : fun_env -> list fun_Dan -> imp_Dan -> Prop :=
| fun_app_skip :
  forall fenv wf_funcs,
    fun_app_imp_well_formed fenv wf_funcs SKIP_Dan
| fun_app_assign :
  forall fenv wf_funcs x a,
    fun_app_well_formed fenv wf_funcs a ->
    fun_app_imp_well_formed fenv wf_funcs (ASSIGN_Dan x a)
| fun_app_seq :
  forall fenv wf_funcs i1 i2,
    fun_app_imp_well_formed fenv wf_funcs i1 ->
    fun_app_imp_well_formed fenv wf_funcs i2 ->
    fun_app_imp_well_formed fenv wf_funcs (SEQ_Dan i1 i2)
| fun_app_if :
  forall fenv wf_funcs b i1 i2,
    fun_app_bexp_well_formed fenv wf_funcs b ->
    fun_app_imp_well_formed fenv wf_funcs i1 ->
    fun_app_imp_well_formed fenv wf_funcs i2 ->
    fun_app_imp_well_formed fenv wf_funcs (IF_Dan b i1 i2)
| fun_app_while :
  forall fenv wf_funcs b i,
    fun_app_bexp_well_formed fenv wf_funcs b ->
    fun_app_imp_well_formed fenv wf_funcs i ->
    fun_app_imp_well_formed fenv wf_funcs (WHILE_Dan b i).

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

Fixpoint collect_all_func_names_imp (fenv: fun_env) (fuel: nat) (i: imp_Dan): option (ListSet.set ident) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match i with
      | ASSIGN_Dan x a => collect_all_func_names_aexp fenv fuel' a
      | SEQ_Dan i1 i2 =>
          set_union_option
            (collect_all_func_names_imp fenv fuel' i1)
            (collect_all_func_names_imp fenv fuel' i2)
      | IF_Dan b i1 i2 =>
          set_union_option
            (collect_all_func_names_bexp fenv fuel' b)
            (set_union_option
               (collect_all_func_names_imp fenv fuel' i1)
               (collect_all_func_names_imp fenv fuel' i2))
      | WHILE_Dan b i =>
          set_union_option
            (collect_all_func_names_bexp fenv fuel' b)
            (collect_all_func_names_imp fenv fuel' i)
      | _ => Some (ListSet.empty_set ident)
      end
  end
with collect_all_func_names_aexp (fenv: fun_env) (fuel: nat) (a: aexp_Dan): option (ListSet.set ident) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match a with
           | PLUS_Dan a1 a2
           | MINUS_Dan a1 a2 =>
               set_union_option
                 (collect_all_func_names_aexp fenv fuel' a1)
                 (collect_all_func_names_aexp fenv fuel' a2)
           | APP_Dan f args =>
               obind (collect_all_func_names_args fenv fuel' args) (fun s => Some (ListSet.set_add string_dec f s))
           | _ =>
               Some (ListSet.empty_set ident)
           end
       end
with collect_all_func_names_args (fenv: fun_env) (fuel: nat) (args: list aexp_Dan): option (ListSet.set ident) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match args with
           | nil => Some (ListSet.empty_set ident)
           | arg :: args' =>
               set_union_option (collect_all_func_names_aexp fenv fuel' arg) (collect_all_func_names_args fenv fuel' args')
           end
       end
with collect_all_func_names_bexp (fenv: fun_env) (fuel: nat) (b: bexp_Dan): option (ListSet.set ident) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match b with
           | NEG_Dan b => collect_all_func_names_bexp fenv fuel' b
           | AND_Dan b1 b2
           | OR_Dan b1 b2 =>
               set_union_option
                 (collect_all_func_names_bexp fenv fuel' b1)
                 (collect_all_func_names_bexp fenv fuel' b2)
           | LEQ_Dan a1 a2 =>
               set_union_option
                 (collect_all_func_names_aexp fenv fuel' a1)
                 (collect_all_func_names_aexp fenv fuel' a2)
           | _ =>
               Some (ListSet.empty_set ident)
           end
       end.

Definition default_fuel := 100000.

Definition collect_all_func_names_funcs (fenv: fun_env) (fident_list: list ident): option (ListSet.set ident) :=
  fold_left (fun (acc: option (ListSet.set ident)) (x: ident) => set_union_option (collect_all_func_names_imp fenv default_fuel (DanTrickLanguage.Body (fenv x))) acc) fident_list (Some fident_list).

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

Definition fenv_well_formed_aexp (fenv: fun_env) (a: aexp_Dan) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Dan),
    Some first_fident_list = (collect_all_func_names_aexp fenv default_fuel a) ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_well_formed fenv func_list a.

Definition fenv_well_formed_bexp (fenv: fun_env) (b: bexp_Dan) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Dan),
    Some first_fident_list = collect_all_func_names_bexp fenv default_fuel b ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_bexp_well_formed fenv func_list b.

Definition fenv_well_formed_args (fenv: fun_env) (args: list aexp_Dan) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Dan),
    Some first_fident_list = collect_all_func_names_args fenv default_fuel args ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_args_well_formed fenv func_list args.


Definition fenv_well_formed (fenv: fun_env) (i: imp_Dan) :=
  forall (first_fident_list fident_list: list ident) (func_list: list fun_Dan),
    Some first_fident_list = (collect_all_func_names_imp fenv default_fuel i) ->
    Some fident_list = collect_all_funcs_names fenv default_fuel first_fident_list ->
    func_list = map fenv fident_list ->
    fun_app_imp_well_formed fenv func_list i.

Definition construct_func_list (fenv: fun_env) (maybe_list: option (ListSet.set ident)): option (list fun_Dan) :=
  option_map (map fenv) (obind maybe_list (collect_all_funcs_names fenv default_fuel)).

Definition construct_imp_func_list (fenv: fun_env) (i: imp_Dan): option (list fun_Dan) :=
  construct_func_list fenv (collect_all_func_names_imp fenv default_fuel i).

Definition construct_aexp_func_list (fenv: fun_env) (a: aexp_Dan): option (list fun_Dan) :=
  construct_func_list fenv (collect_all_func_names_aexp fenv default_fuel a).

Definition construct_bexp_func_list (fenv: fun_env) (b: bexp_Dan): option (list fun_Dan) :=
  construct_func_list fenv (collect_all_func_names_bexp fenv default_fuel b).

Definition construct_args_func_list (fenv: fun_env) (args: list aexp_Dan): option (list fun_Dan) :=
  construct_func_list fenv (collect_all_func_names_args fenv default_fuel args).

Ltac unfold_func_wf_consts_in H :=
  unfold construct_imp_func_list, construct_aexp_func_list, construct_bexp_func_list, construct_args_func_list in H;
  unfold construct_func_list in H.

Definition fenv_well_formed' (funcs: list fun_Dan) (fenv: fun_env): Prop :=
  NoDup funcs /\
    forall (f: ident) (func: fun_Dan),
      func = fenv f ->
      (In func funcs \/ func = init_fenv "id") /\
        fun_app_imp_well_formed fenv funcs (DanTrickLanguage.Body func) /\
        imp_has_variable (DanTrickLanguage.Ret func) (DanTrickLanguage.Body func).

