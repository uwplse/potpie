open Locationutils
open Termutils

(* Constants and utilities for accessing and creating Coq's core
   inductive datatypes, including nat, bool, option, eq, and list. *)

(* Booleans *)
let coq_bool = get_inductive "Coq.Init.Datatypes.bool" ~index:0
let coq_bool_constructors_tbl =
  get_constructors_hashtbl ~env:(Global.env ()) ~trm:(EConstr.mkInd coq_bool) ~sigma:Evd.empty

let inject_bool_into_coq_bool b =
  if b then
    Hashtbl.find coq_bool_constructors_tbl "true"
  else
    Hashtbl.find coq_bool_constructors_tbl "false"

let coq_bool_to_bool env sigma b =
  let sigma, eq = Termutils.equal env b (Hashtbl.find coq_bool_constructors_tbl "true") sigma in
  if eq then
    true
  else
    (let sigma, eq = Termutils.equal env b (Hashtbl.find coq_bool_constructors_tbl "false") sigma in
     if eq then
       false
     else
       failwith ("Expected a coq bool but found " ^ (Printingutils.print_kinds env b sigma)))

(* Equality *)
let coq_eq = get_inductive "Coq.Init.Logic.eq" ~index:0
let coq_eq_refl =
  Hashtbl.find
    (get_constructors_hashtbl ~env:(Global.env ()) ~trm:(EConstr.mkInd coq_eq) ~sigma:Evd.empty) "eq_refl"

(* Options *)
let coq_option = get_inductive "Coq.Init.Datatypes.option" ~index:0
let coq_option_constructors_tbl =
  get_constructors_hashtbl ~env:(Global.env ()) ~trm:(EConstr.mkInd coq_option) ~sigma:Evd.empty

let coq_Some = Hashtbl.find coq_option_constructors_tbl "Some"

let coq_None = Hashtbl.find coq_option_constructors_tbl "None"

let constructor_to_string (c: Names.Construct.t) =
  match c with
  | (ind, i) ->
    (match ind with
     | (mind, k) ->
       "(" ^ (Names.MutInd.to_string mind) ^ ", " ^ (string_of_int k) ^ ", " ^ (string_of_int i) ^ ")")
       

(* Turn a Coq option into an OCaml option instead, so you can pattern
   match on it. Uses unification *)
let unwrap_option env sigma term =
  let sigma, evars = mk_n_evars 2 env sigma in
  let some_x = mkAppl (coq_Some, evars) in
  let sigma, unifier_o = unify_resolve_evars env some_x term sigma in
  match unifier_o with
  | Some (app, _) ->
     sigma, Some (Array.of_list (all_args app sigma)) 
  | None ->
     let none = coq_None in
     let sigma, unifier_o = unify_resolve_evars env none term sigma in
     match unifier_o with
     | Some unifier -> sigma, None
     | None -> 
        failwith ("Not an option " ^ (Printingutils.print_kinds env term sigma))

let coq_nat = get_inductive "Coq.Init.Datatypes.nat" ~index:0
let coq_nat_constructors_tbl =
  get_constructors_hashtbl ~env:(Global.env ()) ~trm:(EConstr.mkInd coq_nat) ~sigma:Evd.empty

let coq_nat_S = Hashtbl.find coq_nat_constructors_tbl "S"
let coq_nat_O = Hashtbl.find coq_nat_constructors_tbl "O"
let coq_nat_constructors =
  let s = coq_nat_S in
  let o = coq_nat_O in
  let succ arg = (EConstr.mkApp (s, Array.of_list [arg])) in
  (o, s, succ)

let int_to_coq_nat i =
  let o, s, succ = coq_nat_constructors in
  let rec helper i res =
    if i > 0 then
      (match res with
       | Some t ->
         helper (i - 1) (Some (succ t))
       | None -> None)
    else
      (if i < 0 then failwith ("Cannot turn a negative number " ^ (string_of_int i) ^ " into a nat")
       else res)
  in
  helper i (Some o)

let coq_list = get_inductive "Coq.Init.Datatypes.list" ~index:0
let coq_list_cons_tbl =
  get_constructors_hashtbl ~env:(Global.env ()) ~trm:(EConstr.mkInd coq_list) ~sigma:Evd.empty

(* Convenience function for making lists of certain types *)
let coq_list_constructors env sigma trm =
  let _, tipe = Termutils.normalize_type env trm sigma in
  let tbl = coq_list_cons_tbl in
  let nil' = Hashtbl.find tbl "nil" in
  let cons = Hashtbl.find tbl "cons" in
  let app_cons arg lst =
    (EConstr.mkApp (cons, Array.of_list [tipe; arg; lst])) in
  let nil = EConstr.mkApp (nil', Array.of_list [tipe]) in
  (nil', cons, nil, app_cons)

(* Get all of the econstrs in a coq list as a list *)
let coq_list_to_list env trm sigma =
  let open Constr in
  let open EConstr in
  let trm = Termutils.normalize_ignore_opaques env trm sigma in
  let rec helper env sigma trm res =
    (match kind sigma trm with
     | App (name, args) ->
       (match is_constructor_of_inductive env sigma coq_list (to_constr sigma name) with
        | Some (cons, name) ->
          if String.equal name "cons" && Array.length args == 3 then
            helper env sigma (Array.get args 2) ((Array.get args 1) :: res)
          else
            (List.rev res)
        | _ ->
          failwith "Not a constructor of list")
     | _ -> failwith "Not an application")
  in
  let tipe = (match kind sigma trm with
      | App (name, args) ->
        (* First arg should be the type *)
        if Array.length args >= 1 then
          Array.get args 0
        else
          failwith "Not enough args for coq_list_to_list"
      | _ -> failwith "Not an application") in
  (tipe, helper env sigma trm [])
