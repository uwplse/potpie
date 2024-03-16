val _coq_module : string list -> Names.ModPath.t
val coq_module : string -> Names.ModPath.t
val get_inductive : string -> ?index:int -> Names.MutInd.t * int
val get_constant : string -> Names.Constant.t
val get_inductive_econstr : string -> ?index:int -> EConstr.t
val make_constructor : EConstr.t -> int -> EConstr.t
val get_names_num_constructors :
  env:Environ.env ->
  trm:EConstr.t -> sigma:Evd.evar_map -> Names.Id.t array * int
val _get_constructors :
  ?sigma:Evd.evar_map -> EConstr.t -> int -> EConstr.t list
val get_constructors :
  env:Environ.env -> trm:EConstr.t -> sigma:Evd.evar_map -> EConstr.t list
val get_constructors_hashtbl :
  env:Environ.env ->
  trm:EConstr.t -> sigma:Evd.evar_map -> (string, EConstr.t) Hashtbl.t
val is_constructor_of_inductive :
  Environ.env ->
  Evd.evar_map ->
  Names.inductive -> Constr.t -> (Names.constructor * string) option
val sht : Names.inductive
val prod : Names.inductive
val is_stk_hoare_tree_constructor :
  Environ.env ->
  Evd.evar_map -> Constr.t -> (Names.constructor * string) option
val get_pair_from_prod :
  Environ.env ->
  Constr.constr -> Evd.evar_map -> Constr.constr * Constr.constr
val make_pair_type : 'a -> 'b -> EConstr.t -> EConstr.t -> EConstr.t
val prod_pair_constructor : Environ.env -> Evd.evar_map -> EConstr.t
val make_pair :
  Environ.env ->
  Evd.evar_map -> EConstr.t -> EConstr.t -> EConstr.t * EConstr.t
