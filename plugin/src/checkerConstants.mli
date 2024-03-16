val make_constant : string -> EConstr.t
val imp_stack : Names.MutInd.t * int
val aexp_stack : Names.MutInd.t * int
val bexp_stack : Names.MutInd.t * int
val fun_stk : Names.MutInd.t * int
val aexp_stack_frame : Names.MutInd.t * int
val fun_stk_constructor : EConstr.t
val funcs_frame : EConstr.t
val frame_of_aexp : EConstr.t
val frame_of_bexp : EConstr.t
val absstate : Names.MutInd.t * int
val absstack : Names.MutInd.t * int
val absstate_tbl : Environ.env -> Evd.evar_map -> (string, EConstr.t) Hashtbl.t
val absstack_tbl : Environ.env -> Evd.evar_map -> (string, EConstr.t) Hashtbl.t
val imp_stack_cons_tbl : Environ.env -> Evd.evar_map -> (string, EConstr.t) Hashtbl.t
val sarray : 'a -> 'a array
val construct_update : EConstr.t
val coq_state_update : EConstr.t
val construct_state_stk_size_inc : EConstr.t
val state_stack_size_inc : EConstr.t
val construct_aexp_stack_pure_rel : EConstr.t
val construct_bexp_stack_pure_rel : EConstr.t
val aimp_self : EConstr.t
val coq_option_map : EConstr.t
val atruestk : EConstr.t
val afalsestk : EConstr.t
val aimpstk : EConstr.t
val make_app : EConstr.t -> EConstr.t list -> EConstr.t
val get_precondition : EConstr.t
val get_postcondition : EConstr.t
val increase_absstack_okay : EConstr.t
val construct_n_leq_m : EConstr.t
val maximum_stack_size_implied : EConstr.t
val nth_error : EConstr.t
val fact_env_valid_means_aimpstk : EConstr.t
