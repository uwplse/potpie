val coq_bool : Names.MutInd.t * int
val inject_bool_into_coq_bool : bool -> EConstr.t
val coq_bool_to_bool : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val coq_eq : Names.MutInd.t * int
val coq_eq_refl : EConstr.t
val coq_option : Names.MutInd.t * int
val coq_Some : EConstr.t
val coq_None : EConstr.t
val constructor_to_string : Names.Construct.t -> string
val unwrap_option :
  Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t array option
val coq_nat : Names.MutInd.t * int
val coq_nat_S : EConstr.t
val coq_nat_O : EConstr.t
val coq_nat_constructors : EConstr.t * EConstr.t * (EConstr.t -> EConstr.t)
val int_to_coq_nat : int -> EConstr.t option
val coq_list : Names.MutInd.t * int
val coq_list_constructors :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  EConstr.t * EConstr.t * EConstr.t * (EConstr.t -> EConstr.t -> EConstr.t)
val coq_list_to_list :
  Environ.env -> EConstr.t -> Evd.evar_map -> EConstr.t * EConstr.t list
