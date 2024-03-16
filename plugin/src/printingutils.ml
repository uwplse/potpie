open Pp
(* open EConstr *)

let debug_print t =
  db_print_pp Format.std_formatter t

let econstr_debug_print env ?(sigma=Evd.empty) term =
  debug_print (Printer.pr_econstr_env env sigma term)

let print_warn t =
  Feedback.msg_warning t

let econstr_pp env ?(sigma=Evd.empty) term =
  Printer.pr_econstr_env env sigma term

let econstr_string env sigma term =
  Pp.string_of_ppcmds (econstr_pp env ~sigma:sigma term)

let econstrs_to_strings env sigma econstrs =
  (List.map Pp.string_of_ppcmds (List.map (Printer.pr_constr_env env sigma) (List.map (EConstr.to_constr sigma) econstrs)))

let parenthesize mylist =
  List.map (fun s -> "(" ^ s ^ ")") mylist

let inductive_to_string (i: Names.inductive) : string =
  match i with
  | (mind, k) ->
    Names.MutInd.to_string mind



let rec print_kinds env term sigma =
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
      
            


(* from coq-plugin-lib *)
(*
 * Auxiliary functions for printing.
 *
 * Some of these implementations are incomplete right now.
 * Those pieces will show the wrong environments, so indexes will
 * appear to be incorrect.
 *)

open Format
open Names
open Univ
open Constr
open Environ
open Printer
open Utilities
open Goptions
open Declarations
open Termutils
(* open Envutils *)
open Contextutils

module CRD = Context.Rel.Declaration

(* Pretty-print a `global_reference` with fancy `constr` coloring. *)
(* let pr_global_as_constr gref = *)
(*   let env = Global.env () in *)
(*   let sigma = Evd.from_env env in *)
(*   pr_constr_env env sigma (Universes.constr_of_global gref) *)

(* Using pp, prints directly to a string *)
let print_to_string (pp : formatter -> 'a -> unit) (trm : 'a) : string =
  Format.asprintf "%a" pp trm

(* Gets n as a string *)
let name_as_string (n : Name.t) : string =
  match n with
  | Name id -> Id.to_string id
  | Anonymous -> "_"

(* Pretty prints a term using Coq's pretty printer *)
let print_constr (fmt : formatter) (c : constr) : unit  =
  Pp.pp_with fmt (Printer.pr_constr_env (Global.env ()) Evd.empty c)

(* Pretty prints a universe level *)
let print_univ_level (fmt : formatter) (l : Level.t) =
  Pp.pp_with fmt (Level.pr l)

(* Prints a universe *)
let universe_as_string u =
  match Universe.level u with
  | Some l ->
     print_to_string print_univ_level l
  | None ->
     Printf.sprintf
       "Max{%s}"
       (String.concat
          ", "
          (List.map
             (print_to_string print_univ_level)
             (Level.Set.elements (Universe.levels u))))

(* Gets a sort as a string *)
let sort_as_string s =
  match s with
  | Term.Prop -> if s = Sorts.prop then "Prop" else "Set"
  | Term.Set -> "Set"
  | Term.SProp -> "SProp"
  | Term.Type u -> Printf.sprintf "Type %s" (universe_as_string u)

(* let bindings_for_fix (names : Names.name array) (typs : constr array) = *)
(*   Array.to_list *)
(*     (CArray.map2_i *)
(*        (fun i name typ -> (name, None, Vars.lift i typ)) *)
(*        names (Array.map of_constr typs)) *)

(* from https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/logicutils/typesandequality/inference.ml *)
(* Get the type of an inductive type (TODO do we need evar_map here?) *)
(* let type_of_inductive env index mutind_body : types = *)
(*   let ind_bodies = mutind_body.mind_packets in *)
(*   let ind_body = Array.get ind_bodies index in *)
(*   let univs = Declareops.inductive_polymorphic_context mutind_body in *)
(*   let univ_instance = Univ.make_abstract_instance univs in *)
(*   let mutind_spec = (mutind_body, ind_body) in *)
(*   Inductive.type_of_inductive (mutind_spec, univ_instance) *)

(* these bindings functions are from https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/logicutils/contexts/contextutils.ml *)
(*
 * Inductive types
 *)
(* let bindings_for_inductive env mutind_body ind_bodies : rel_declaration list = *)
(*   Array.to_list *)
(*     (Array.mapi *)
(*        (fun i ind_body -> *)
(*          let name_id = ind_body.mind_typename in *)
(*          let typ = type_of_inductive env i mutind_body in *)
(*          CRD.LocalAssum (Context.nameR name_id, typ)) *)
(*        ind_bodies) *)

(*
 * Fixpoints
 *)
(* let bindings_for_fix (names : Names.Name.t Context.binder_annot array) (typs : types array) : rel_declaration list = *)
(*   (\* let open engine.Vars in *\) *)
(*   Array.to_list *)
(*     (CArray.map2_i *)
(*        (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ)) *)
(*        names (typs)) *)



(* Prints a term *)
let rec term_as_string (env : env) (trm : types) =
  match kind trm with
  | Rel i ->
     (try
       let (n, _, _) = CRD.to_tuple @@ lookup_rel i env in
       Printf.sprintf "(%s [Rel %d])" (name_as_string (Context.binder_name n)) i
     with
       Not_found -> Printf.sprintf "(Unbound_Rel %d)" i)
  | Var v ->
     Id.to_string v
  | Evar (k, cs) ->
     Printf.sprintf "??"
  | Sort s ->
     sort_as_string s
  | Cast (c, k, t) ->
     Printf.sprintf "(%s : %s)" (term_as_string env c) (term_as_string env t)
  | Prod (n, t, b) ->
     Printf.sprintf
       "(Π (%s : %s) . %s)"
       (name_as_string (Context.binder_name n))
       (term_as_string env t)
       (term_as_string (push_local (n, EConstr.of_constr t) env) b)
  | Lambda (n, t, b) ->
     Printf.sprintf
       "(λ (%s : %s) . %s)"
       (name_as_string (Context.binder_name n))
       (term_as_string env t)
       (term_as_string (push_local (n, EConstr.of_constr t) env) b)
  | LetIn (n, trm, typ, e) ->
     Printf.sprintf
       "(let (%s : %s) := %s in %s)"
       (name_as_string (Context.binder_name n))
       (term_as_string env typ)
       (term_as_string env trm)
       (term_as_string (push_let_in (n, EConstr.of_constr trm, EConstr.of_constr typ) env) e)
  | App (f, xs) ->
     Printf.sprintf
       "(%s %s)"
       (term_as_string env f)
       (String.concat " " (List.map (term_as_string env) (Array.to_list xs)))
  | Const (c, u) ->
     let ker_name = Constant.canonical c in
     KerName.to_string ker_name
  | Construct (((i, i_index), c_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     let constr_name_id = ind_body.mind_consnames.(c_index - 1) in
     Id.to_string constr_name_id
  | Ind ((i, i_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_bodies = mutind_body.mind_packets in
     let name_id = (ind_bodies.(i_index)).mind_typename in
     Id.to_string name_id
  | Fix ((is, i), (ns, ts, ds)) ->
     let env_fix = push_rel_context (bindings_for_fix ns ds) env in
     String.concat
       " with "
       (map3
          (fun n t d ->
            Printf.sprintf
             "(Fix %s : %s := %s)"
             (name_as_string n)
             (term_as_string env t)
             (term_as_string env_fix d))
          (List.map Context.binder_name (Array.to_list ns))
          (Array.to_list ts)
          (Array.to_list ds))
  | Case (ci, u, _, ct, _, m, bs) ->
     (* let (i, i_index) = ci.ci_ind in *)
     (* let mutind_body = lookup_mind i env in *)
     (* let ind_body = mutind_body.mind_packets.(i_index) in *)
     Printf.sprintf
       "(match %s : %s with %s)"
       (term_as_string env m)
       ""
       ""
       (* (term_as_string env ct) *)
       (* (String.concat *)
       (*    " " *)
       (*    (Array.to_list *)
       (*       (Array.mapi *)
       (*          (fun c_i b -> *)
       (*            Printf.sprintf *)
       (*              "(case %s => %s)" *)
       (*              (Id.to_string (ind_body.mind_consnames.(c_i))) *)
       (*              (term_as_string env b)) *)
       (*          bs))) *)
  | Meta mv -> (* TODO *)
     Printf.sprintf "(%s)" (print_to_string print_constr trm)
  | CoFix (i, (ns, ts, ds)) -> (* TODO *)
     Printf.sprintf "(%s)" (print_to_string print_constr trm)
  | Proj (p, c) -> (* TODO *)
    Printf.sprintf "(%s)" (print_to_string print_constr trm)
  | Int i ->
    Printf.sprintf "Int[%s]" (Uint63.to_string i)
  | Float f ->
    Printf.sprintf "Float[%s]" (Float64.to_string f)
  | Array (u, vals, def, t) ->
    Printf.sprintf "Array"

(* Debug a term *)
let debug_term (env : env) (trm : types) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (term_as_string env trm)

(* Debug a list of terms *)
let debug_terms (env : env) (trms : types list) (descriptor : string) : unit =
  List.iter (fun t -> debug_term env t descriptor) trms

let print_separator unit : unit =
  Printf.printf "%s\n\n" "-----------------"

(* --- Coq environments --- *)

(* from https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/logicutils/contexts/envutils.ml *)
(* Return a list of all indexes in env, starting with 1 *)
let all_rel_indexes (env : env) : int list =
  from_one_to (nb_rel env)
(* Gets env as a string *)
let env_as_string (env : env) : string =
  let all_relis = all_rel_indexes env in
  String.concat
    ",\n"
    (List.map
       (fun i ->
         let (n, b, t) = CRD.to_tuple @@ lookup_rel i env in
         Printf.sprintf
           "%s (Rel %d): %s"
           (name_as_string (Context.binder_name n))
           i
           (term_as_string (pop_rel_context i env) t))
       all_relis)

(* Debug an environment *)
let debug_env (env : env) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (env_as_string env)

(* --- TODO move me --- *)

(* Print a patch to stdout in the standard Coq format *)
let print_patch env sigma patch_id patch : unit =
  let opts = get_tables () in
  let print_all =
    match (OptionMap.find ["Printing"; "All"] opts).opt_value with
    | BoolValue b -> b
    | _ -> true
  in
  let _ = set_bool_option_value ["Printing"; "All"] true in
  Pp.pp_with
    Format.std_formatter
    (Pp.pr_sequence
       id
       [(Pp.str "\nBEGIN PATCH");
        (Pp.str patch_id);
        (Pp.str "\nDefinition");
        (Pp.str patch_id);
        (Pp.str ":=");
        (pr_lconstr_env env sigma patch);
        (Pp.str ".\nEND PATCH");
        (Pp.str "\n")]);
  set_bool_option_value ["Printing"; "All"] print_all

let binding_to_string env (b: rel_declaration) sigma =
  match b with
  | CRD.LocalAssum (binder, tipe) ->
    "LocalAssum[" ^ (Pp.string_of_ppcmds (Names.Name.print (Context.binder_name binder))) ^ ":" ^ (term_as_string env tipe) ^ "]"
  | CRD.LocalDef (binder, value, tipe) ->
    "LocalDef[" ^ (Pp.string_of_ppcmds (Names.Name.print (Context.binder_name binder))) ^ ":" ^ (term_as_string env tipe) ^ " := " ^ (term_as_string env value) ^ "]"
