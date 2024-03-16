type stk_hoare_tree =
    StkHTSkip of EConstr.types
  | StkHTAssign of EConstr.types * EConstr.types * EConstr.types
  | StkHTPush of EConstr.types
  | StkHTPop of EConstr.types * EConstr.types * EConstr.types
  | StkHTSeq of EConstr.types * EConstr.types * EConstr.types *
      EConstr.types * EConstr.types * stk_hoare_tree * stk_hoare_tree
  | StkHTIf of EConstr.types * EConstr.types * EConstr.types *
      EConstr.types * EConstr.types * stk_hoare_tree * stk_hoare_tree
  | StkHTWhile of EConstr.types * EConstr.types * EConstr.types *
      stk_hoare_tree
  | StkHTConLeft of (EConstr.types * EConstr.types) * EConstr.types *
      EConstr.types * EConstr.types * stk_hoare_tree
  | StkHTConRight of EConstr.types * EConstr.types *
      (EConstr.types * EConstr.types) * EConstr.types * stk_hoare_tree
  | StkHTCon of (EConstr.types * EConstr.types) *
      (EConstr.types * EConstr.types) * EConstr.types * stk_hoare_tree
val get_pre : Environ.env -> Evd.evar_map -> stk_hoare_tree -> EConstr.types
val get_post : Environ.env -> Evd.evar_map -> stk_hoare_tree -> EConstr.types
val get_imp : Environ.env -> Evd.evar_map -> stk_hoare_tree -> EConstr.t
val to_string : stk_hoare_tree -> string
val econstrs_to_strings :
  Environ.env -> Evd.evar_map -> EConstr.t list -> string list
val econstr_to_string : Environ.env -> Evd.evar_map -> EConstr.t -> string
val parenthesize :
  ?left:string -> ?right:string -> string list -> string list
val to_string_with_args :
  stk_hoare_tree -> Environ.env -> Evd.evar_map -> string
val absstate_to_string : Environ.env -> Evd.evar_map -> EConstr.t -> string
val max_depth : stk_hoare_tree -> int
val to_string_with_args_abbr_tl_rec :
  Environ.env -> Evd.evar_map -> stk_hoare_tree -> string
val to_string_with_args_abbr :
  ?max_level:int -> stk_hoare_tree -> Environ.env -> Evd.evar_map -> string
val collect_trees :
  ?max:int ->
  (stk_hoare_tree -> bool) -> stk_hoare_tree -> stk_hoare_tree list
val recurse_over_constr :
  Environ.env -> Constr.constr -> Evd.evar_map -> stk_hoare_tree option
val construct_hoare_tree :
  Environ.env ->
  Evd.evar_map -> String.t -> Constr.constr array -> stk_hoare_tree option
val make_stk_hoare_tree :
  Environ.env -> Evd.evar_map -> stk_hoare_tree -> EConstr.t option
