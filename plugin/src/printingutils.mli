val debug_print : Pp.t -> unit
val econstr_debug_print :
  Environ.env -> ?sigma:Evd.evar_map -> EConstr.t -> unit
val print_warn : Pp.t -> unit
val econstr_pp : Environ.env -> ?sigma:Evd.evar_map -> EConstr.t -> Pp.t
val econstr_string : Environ.env -> Evd.evar_map -> EConstr.t -> string
val econstrs_to_strings :
  Environ.env -> Evd.evar_map -> EConstr.t list -> string list
val parenthesize : string list -> string list
val inductive_to_string : Names.inductive -> string
val print_kinds : 'a -> EConstr.t -> Evd.evar_map -> string
module CRD = Context.Rel.Declaration
val print_to_string : (Format.formatter -> 'a -> unit) -> 'a -> string
val name_as_string : Names.Name.t -> string
val print_constr : Format.formatter -> Constr.constr -> unit
val print_univ_level : Format.formatter -> Univ.Level.t -> unit
val universe_as_string : Univ.Universe.t -> string
val sort_as_string : Sorts.t -> string
val term_as_string : Environ.env -> Constr.types -> string
val debug_term : Environ.env -> Constr.types -> string -> unit
val debug_terms : Environ.env -> Constr.types list -> string -> unit
val print_separator : 'a -> unit
val all_rel_indexes : Environ.env -> int list
val env_as_string : Environ.env -> string
val debug_env : Environ.env -> string -> unit
val print_patch :
  Environ.env -> Evd.evar_map -> string -> Constr.constr -> unit
val binding_to_string : Environ.env -> Constr.rel_declaration -> 'a -> string
