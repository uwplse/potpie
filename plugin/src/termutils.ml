(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 * Utilities for the state monad were moved to stateutils.ml/stateutils.mli
 * Utilities for inductive types & proofs are in induction.ml/induction.mli
 *)

open EConstr
open Environ
open Names
open Tacred
open CClosure
open RedFlags
open Libobject
open Lib

(* --- Debugging --- *)

(*
 * A convenient function for printing terms
 *)
let print env t sigma = Printer.pr_econstr_env env sigma t

(*
 * Same as above, but output to Coq rather than returning a Pp.t object
 *)
let print_message env t sigma = Feedback.msg_notice (print env t sigma) 

(* --- Environments --- *)

(*
 * Environments in the Coq kernel map names (local and global variables)
 * to definitions and types. Here are a few utility functions for environments.
 *)
               
(*
 * This gets the global environment and the corresponding state:
 *)
let global_env () =
  let env = Global.env () in
  Evd.from_env env, env

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(* Push a let-in definition to an environment *)
let push_let_in (n, e, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalDef(n, e, t)) env
  
(*
 * Push all local bindings in a product type to an environment, until the
 * conclusion is no longer a product type. Return the environment with all
 * of the bindings, and the conclusion type.
 *)
let rec push_all_locals_prod env typ sigma =
  match kind sigma typ with
  | Constr.Prod (n, t, b) ->
     push_all_locals_prod (push_local (n, t) env) b sigma
  | _ ->
     (env, typ)

(*
 * Like push_all_locals_prod, but for lambda terms
 *)
let rec push_all_locals_lambda env trm sigma =
  match kind sigma trm with
  | Constr.Lambda (n, t, b) ->
     push_all_locals_lambda (push_local (n, t) env) b sigma
  | _ ->
     (env, trm)

(*
 * Like push_all_locals_lambda, but only push the first nargs locals
 * If nargs is too large, then behave like push_all_locals_lambda
 *)
let rec push_n_locals_lambda nargs env trm sigma =
  if nargs <= 0 then
    (env, trm)
  else
    match kind sigma trm with
    | Constr.Lambda (n, t, b) ->
       push_n_locals_lambda (nargs - 1) (push_local (n, t) env) b sigma
    | _ ->
       env, trm

(*
 * Reconstruct a lambda term from an environment, removing those bindings
 * from the environment. Stop when there are n bindings left in the environment.
 *)
let rec reconstruct_lambda_n i env b =
  if nb_rel env = i then
    env, b
  else
    let (n, _, t) = Context.Rel.Declaration.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n i env' (mkLambda (n, (EConstr.of_constr t), b))

(* Reconstruct a lambda from an environment, popping all local variables *)
let reconstruct_lambda = reconstruct_lambda_n 0

(* --- Definitions --- *)

(*
 * One of the coolest things about plugins is that you can use them
 * to define new terms. Here's a simplified (yes it looks terrifying,
 * but it really is simplified) function for defining new terms and storing them
 * in the global environment.
 *
 * This will only work if the term you produce
 * type checks in the end, so don't worry about accidentally proving False.
 * If you want to use the defined function later in your plugin, you
 * have to refresh the global environment by calling global_env () again,
 * but we don't need that in this plugin.
 *)
let define name body sigma =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  ignore (Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma)

(*
 * When you first start using a plugin, if you want to manipulate terms
 * in an interesting way, you need to move from the external representation
 * of terms to the internal representation of terms. This does that for you.
 *)
let internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm

(*
 * Look up a definition from an environment
 *)
let lookup_definition env def sigma =
  match kind sigma def with
  | Constr.Const (c, u) ->
     let cb = lookup_constant c env in
     (match Global.body_of_constant_body Library.indirect_accessor cb with
      | Some(e, _, _) -> EConstr.of_constr e
      | None -> failwith "This term has no value")
  | _ -> failwith "not a definition"

(* Fully lookup a def in env, but return the term if it is not a definition *)
let rec unwrap_definition env trm sigma =
  try
    let body = lookup_definition env trm sigma in
    if Constr.equal (EConstr.to_constr sigma body) (EConstr.to_constr sigma trm) then
      trm
    else
      unwrap_definition env body sigma
  with _ ->
    trm

(* --- Equality --- *)
  
(*
 * This checks if there is any set of internal constraints in the state
 * such that trm1 and trm2 are definitionally equal in the current environment.
 *)
let equal env trm1 trm2 sigma =
  let opt = Reductionops.infer_conv env sigma trm1 trm2 in
  match opt with
  | Some sigma -> sigma, true
  | None -> sigma, false



(* --- Reduction --- *)

(*
 * Fully normalize a term (apply all possible reduction rules)
 *)

let econstr_pp env ?(sigma=Evd.empty) term =
  Printer.pr_econstr_env env sigma term

let econstr_string env sigma term =
  Pp.string_of_ppcmds (econstr_pp env ~sigma:sigma term)

let rec print_kinds env term sigma =
  let open Pp in
  let open Names in
  let open EConstr in
  let print_name n = string_of_ppcmds (Name.print n) in
  match kind sigma term with
  | Rel i ->
    "Rel " ^ (string_of_int i)
  | Var n ->
    "Var " ^ (Id.to_string n)
  | Meta m ->
    "Meta " ^ (string_of_int m)
  | Evar existential ->
    "Evar " ^ (match existential with
        | (t, some_list) ->
          string_of_ppcmds (Evar.print t))
  | Sort s ->
    "Sort"
  | Cast (c, k, t) ->
    "Cast[" ^ (print_kinds env c sigma) ^ ":" ^ (print_kinds env t sigma) ^ "]"
  | Prod (n, t, c) ->
    "Prod[" ^ (string_of_ppcmds (Name.print (Context.binder_name n)))
    ^ ":" ^ (print_kinds env t sigma) ^ ", " ^ (print_kinds env c sigma) ^ "]"
  | Lambda (n, t, c) ->
    "Lambda[" ^ (string_of_ppcmds (Name.print (Context.binder_name n))) ^ ":" ^ (print_kinds env t sigma) ^ "=>" ^ (print_kinds env c sigma) ^ "]"
  | LetIn (n, c1, t, c2) ->
    "LetIn[" ^ (print_name (Context.binder_name n)) ^ ":" ^ (print_kinds env t sigma) ^ "=" ^ (print_kinds env c1 sigma) ^ " in " ^ (print_kinds env c2 sigma) ^ "]"
  | App (name, args) ->
    "App[" ^ (print_kinds env name sigma) ^ "(" ^ (String.concat "," (List.map (fun i -> print_kinds env i sigma) (Array.to_list args))) ^ ")]"
  | Const (n, u) ->
    "Const[" ^ (Constant.to_string n) ^ "]"
  | Ind (n, u) ->
    (match n with
    | (m, i) ->
      "Ind[" ^ (MutInd.to_string m) ^ "," ^ (string_of_int i) ^ "]"
    )
  | Construct (c, u) ->
    (match c with
     | (i, k) ->
       "Construct[" ^ (match i with
           | (m, _) -> MutInd.to_string m) ^ "," ^ (string_of_int k) ^ "]"
    )
  | Case (ci, u, params, p, iv, c, brs) ->
    "Case[" ^ (print_kinds env c sigma) ^ "--" ^ (String.concat ":" (List.map (fun br -> (match br with
        | (names, body) -> "[" ^ (String.concat "," (List.map (fun i -> string_of_ppcmds (Name.print (Context.binder_name i))) (Array.to_list names))) ^ "(" ^ (print_kinds env body sigma) ^ ")" ^ "]")) (Array.to_list brs))) ^ "]"
  | Fix pfix ->
    "Fix[...]"
    (* (match pfix with *)
    (* | (names, types_array, constrs) -> *)
    (*   let bound_vars = List.map string_of_ppcmds (List.map (Name.print) (List.map (Context.binder_name) (Array.to_list names))) in *)
    (*   "Fix[" ^ (String.concat "," bound_vars) ^ "]") *)
  | CoFix pco ->
    "CoFix"
  | Proj (n, c) ->
    "Proj[" ^ (Projection.to_string n) ^ ": " ^ (print_kinds env c sigma) ^ "]"
  | Int i ->
    "Int[" ^ (Uint63.to_string i) ^ "]"
  | Float f ->
    "Float[" ^ (Float64.to_string f) ^ "]"
  | Array (u, vals, def, t) ->
    "Array[" ^ (print_kinds env t sigma) ^ " -- " ^ (String.concat " " (List.map (fun v -> print_kinds env v sigma) (Array.to_list vals)))

(* Cache for opaques *)
type key_typ = Names.GlobRef.t
module OpaquesCache =
  Hashtbl.Make
    (struct
      type t = key_typ
      let equal =
        (fun t t' -> Names.GlobRef.equal t t')
      let hash =
        (fun t ->
          let open Globnames in
          (ExtRefOrdered.hash (TrueGlobal t)))
    end)

(* Initialize the opaque cache *)
let opaques_cache = OpaquesCache.create 100

(*
 * Wrapping the table for persistence
 *)
let cache_opaque (trm, is_opaque) =
  OpaquesCache.add opaques_cache trm is_opaque

let sub_opaque (subst, (trm, is_opaque)) =
  let open Globnames in
  let trm = subst_global_reference subst trm in
  trm, is_opaque

let inOpaques : key_typ * bool -> obj =
  declare_object { (default_object "OPAQUES") with
    cache_function = cache_opaque;
    load_function = (fun _ -> cache_opaque);
    open_function = (fun _ _ -> cache_opaque);
    classify_function = (fun opaque_obj -> Substitute);
    subst_function = sub_opaque }
              
(*
 * Check if there is an opaque lifting along an ornament for a given term
 *)
let has_opaque_bool trm =
  try
    let open Globnames in
    let trm = Constr.destRef trm in
    OpaquesCache.mem opaques_cache (fst trm)
  with _ ->
    false

(*
 * Lookup an opaque lifting
 *)
let lookup_opaque trm =
  let open Globnames in
  if has_opaque_bool trm then
    let trm = Constr.destRef trm in
    OpaquesCache.find opaques_cache (fst trm)
  else
    false

(*
 * Add an opaque lifting to the opaque lifting cache
 *)
let save_opaque trm =
  try
    let open Globnames in
    let trm = fst (Constr.destRef trm) in
    let opaque_obj = inOpaques (trm, true) in
    add_leaf opaque_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache opaque term")

(*
 * Remove an opaque lifting from the opaque lifting cache
 *)
let remove_opaque trm =
  try
    let open Globnames in
    let trm = fst (Constr.destRef trm) in
    let opaque_obj = inOpaques (trm, false) in
    add_leaf opaque_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache opaque term")

(* Add opaque terms for normalization to our plugin-local database *)
let add_opaques opaques sigma =
  List.iter
    (fun qid ->
      Feedback.msg_info
        (Pp.seq [Pp.str "Adding opaque constant "; Libnames.pr_qualid qid]);
      try
        let c = mkConst (Nametab.locate_constant qid) in
        save_opaque (EConstr.to_constr sigma c)
      with Not_found ->
        CErrors.user_err (Pp.str "Invalid reference"))
    opaques

(* From Coq's redexpr.ml ... *)
let make_flag_constant r =
  match r with
  | EvalVarRef id -> fVAR id
  | EvalConstRef sp -> fCONST sp

(* Normalize without unfolding any locally set opaques *)
let normalize_term env trm sigma =
  let red = all in
  let red = red_add_transparent red (Conv_oracle.get_transp_state (Environ.oracle env)) in
  let red = 
    List.fold_left
      (fun red v ->
        RedFlags.red_sub
          red
          (make_flag_constant (evaluable_of_global_reference env v)))
      red
      (List.of_seq (OpaquesCache.to_seq_keys opaques_cache))
  in Reductionops.clos_norm_flags red env sigma trm


(* Normalize but ignore opaques *)
let normalize_ignore_opaques env trm sigma =
  Reductionops.clos_norm_flags all env sigma trm

(*
 * Reduce/simplify a term
 *)
let reduce_term env trm sigma =
  Reductionops.nf_betaiotazeta env sigma trm

(*
 * Infer the type, then normalize the result
 *)
let normalize_type env trm sigma =
  let sigma, typ = Typing.type_of ~refresh:true env sigma trm in
  sigma, normalize_term env typ sigma

(*
 * Infer the type, then reduce/simplify the result
 *)
let reduce_type env trm sigma =
  let sigma, typ = Typing.type_of ~refresh:true env sigma trm in
  sigma, reduce_term env typ sigma

(* --- Unification --- *)

(*
 * Creates a list of the range of min to max, excluding max
 * This is an auxiliary function renamed from seq in template-coq
 *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []

(* Creates a list from the index 1 to max, inclusive *)
let from_one_to (max : int) : int list =
  range 1 (max + 1)

(* Make n relative indices, from highest to lowest *)
let mk_n_rels n =
  List.map mkRel (List.rev (from_one_to n))

(*
 * fold_left with state
 *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(*
 * For a function that takes and returns state, map that function over a 
 * list of arguments, threading the state through the application to the result.
 *
 * The order here is left-to-right since that is the way functions are applied 
 * in Coq (arguments may depend on earlier arguments). This is sometimes
 * significant.
 *)
let map_state f l sigma =
  let sigma, bs =
    fold_left_state
      (fun bs a sigma -> let sigma, b = f a sigma in sigma, (b :: bs))
      []
      l
      sigma
  in sigma, List.rev bs

(*
 * Make n new evars of any type
 *)
let mk_n_evars n env sigma =
  let open Evarutil in
  map_state
    (fun r sigma ->
      let sigma, (earg_typ, _) = new_type_evar env sigma Evd.univ_flexible in
      let sigma, earg = new_evar env sigma earg_typ in
      sigma, earg)
    (mk_n_rels n)
    sigma

let unify env trm1 trm2 sigma =
  try
    Evarconv.unify_delay ?flags:None env sigma trm1 trm2, true
  with _ ->
    sigma, false

let unify_resolve_evars env trm1 trm2 sigma =
  let sigma, unifies = unify env trm1 trm2 sigma in
  if unifies then
    try
      let sigma, trm1 = Typing.solve_evars env sigma trm1 in
      let sigma, trm2 = Typing.solve_evars env sigma trm2 in
      sigma, Some (trm1, trm2) 
    with _ ->
      sigma, None
  else
    sigma, None

(* --- Functions and Application --- *)

(*
 * Get all arguments of a function, recursing into recursive applications
 * when functions have the form ((f x) y), to get both x and y, and so on.
 * Return list of arguments if it is a function application, and otherwise
 * return the empty list.
 *)
let all_args trm sigma =
  match kind sigma trm with
  | Constr.App (f, args) ->
     let rec unfold t =
       match kind sigma t with
       | Constr.App (f, args) ->
          List.append (unfold f) (Array.to_list args)
       | _ ->
          [t]
     in List.append (List.tl (unfold f)) (Array.to_list args)
  | _ ->
     []

(*
 * Like all_args, but rather than get [x y] for ((f x) y), get f,
 * the first function.
 *)
let rec first_fun trm sigma =
  match kind sigma trm with
  | Constr.App (f, args) ->
     first_fun f sigma
  | _ ->
     trm

(*
 * Make a list of n arguments, starting with the nth most recently bound
 * variable, and ending with the most recently bound variable
 *)
let mk_n_args n =
  List.map mkRel (List.rev (Collections.range 1 (n + 1)))

(*
 * Lift mkApp from arrays to lists
 *)
let mkAppl (f, args) = mkApp (f, Array.of_list args)

(*
 * Apply, then reduce
 * If args are empty, then return f
 *)
let apply_reduce reducer env f args sigma =
  if List.length args = 0 then
    f
  else
    reducer env (mkAppl (f, args)) sigma

(*
 * Get the arity of the function/product
 *)
let rec arity f sigma =
  match kind sigma f with
  | Constr.Lambda (_, _, b) ->
     1 + arity b sigma
  | Constr.Prod (_, _, b) ->
     1 + arity b sigma
  | _ ->
     0

(*
 * Expand a partially applied curried function to take all arguments
 * explicitly. For example, (add 0) becomes (fun n => add 0 n).
 * This is known as eta-expansion.
 *)
let expand_eta env trm sigma =
  let shift_by n trm sigma =
    EConstr.of_constr (Constr.liftn n 0 (EConstr.to_constr sigma trm))
  in
  let sigma, typ = reduce_type env trm sigma in
  let curried_args = mk_n_args (arity typ sigma) in
  let _, expanded =
    reconstruct_lambda
      (fst (push_all_locals_prod (Environ.empty_env) typ sigma))
      (mkAppl (shift_by (List.length curried_args) trm sigma, curried_args))
  in sigma, expanded

(*
 * Return true if f is exactly the same as (syntactically) the first
 * function inside of term, and term is an application.
 *)
let applies f trm sigma =
  match kind sigma trm with
  | Constr.App (g, _) ->
     Constr.equal (EConstr.to_constr sigma f) (EConstr.to_constr sigma g)
  | _ ->
     false

(*
 * Check if trm' is exactly the same as (syntactically) the first
 * function inside of trm and trm is an application, or if trm' and trm
 * are equal to each other.
 *
 * If true, return Some list containing all arguments args to trm' (empty if
 * trm is exactly trm') such that trm' args = trm. Otherwise, return None.
 *)
let is_or_applies trm' trm sigma =
  let can_unify =
    applies trm' trm sigma ||
    Constr.equal (EConstr.to_constr sigma trm') (EConstr.to_constr sigma trm)
  in if can_unify then Some (all_args trm sigma) else None
