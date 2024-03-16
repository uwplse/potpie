open Environ
open Evd
open Stateutils

(*
 * Check a stack Hoare logic proof tree
 *)
val check_stack_proof :
  env -> (* environment *)
  EConstr.t -> (* proof tree as a Coq term *)
  EConstr.t -> (* function environment as a Coq term *)
  EConstr.t -> (* facts environment as a Coq term *)
  EConstr.t -> (* fact_env_valid *)
  evar_map -> (* state *)
  (EConstr.t option) state (* certificate *)
