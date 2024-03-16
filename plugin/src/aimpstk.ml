open EConstr
open Termutils
open CheckerConstants
open Locationutils

type abs_stack =
  | AbsStkTrue
  | AbsStkSize of types

type abs_state =
  | BaseState of abs_stack * types
  | AbsAnd of abs_state * abs_state
  | AbsOr of abs_state * abs_state

let is_abs_stack_constructor env sigma =
  Locationutils.is_constructor_of_inductive env sigma absstack

let is_abs_state_constructor env sigma =
  Locationutils.is_constructor_of_inductive env sigma absstate

let getAbsStackString a =
  match a with
  | AbsStkTrue -> "AbsStkTrue"
  | AbsStkSize _ -> "AbsStkSize"

let getAbsStateString a =
  match a with
  | BaseState _ -> "BaseState"
  | AbsAnd _ -> "AbsAnd"
  | AbsOr _ -> "AbsOr"

let getAbsStack env a sigma =
  match kind sigma a with
  | Constr.App (name, args) ->
    (match is_abs_stack_constructor env sigma (to_constr sigma name) with
     | Some (c, n) ->
       let num_args = Array.length args in
       let largs = List.map (fun e -> unwrap_definition env e sigma) ((Array.to_list args)) in
       let open List in
       let arg n = nth largs n in
       (match n with
        | "AbsStkTrue" ->
          Some AbsStkTrue
        | "AbsStkSize" ->
          if num_args == 1 then
            Some (AbsStkSize (arg 0))
          else
            (* let () = print_endline ("Number of args isn't 1: " ^ (string_of_int num_args)) in *)
            None
        | _ ->
          (* let () = print_endline ("Name isn't a constructor of absstack: " ^ n) in *)
          None)
     |  None ->
       (* let () = print_endline ("Name isn't a constructor of absstack: " ^ (Printingutils.print_kinds env name sigma)) in *)
       None)
  | Constr.Construct (c, u) ->
    (match c with
     | (i, k) ->
       if k == 1 then
         (* let () = print_endline ("Got AbsStkTrue") in *)
         Some AbsStkTrue
       else
         (* let () = print_endline ("Got a constructor index other than 1: " ^ (Printingutils.print_kinds env a sigma)) in *)
         None)
  | _ ->
    (* let () = print_endline ("Not an app: " ^ (Printingutils.print_kinds env a sigma)) in *)
    None

let absStackToEconstr env a sigma =
  let name = getAbsStackString a in
  let tbl = absstack_tbl env sigma in
  match a with
  | AbsStkTrue ->
    Hashtbl.find tbl name
  | AbsStkSize n ->
    make_app (Hashtbl.find tbl name) [n]
    

let option_map2 f a b =
  match a with
  | Some a' ->
    Option.map (f a') b
  | None -> None

let rec absStateToEconstr env a sigma =
  let name = getAbsStateString a in
  let tbl = absstate_tbl env sigma in
  let const = Hashtbl.find tbl name in
  match a with
  | BaseState (s, m) ->
    Some (make_app const [absStackToEconstr env s sigma; m])
  | AbsAnd (a1, a2) ->
    option_map2 (fun b1 b2 -> make_app const [b1; b2])
      (absStateToEconstr env a1 sigma)
      (absStateToEconstr env a2 sigma)
  | AbsOr (a1, a2) ->
    option_map2 (fun b1 b2 -> make_app const [b1; b2])
      (absStateToEconstr env a1 sigma)
      (absStateToEconstr env a2 sigma)
       
let rec getAbsState env a sigma =
  match kind sigma a with
  | Constr.App (name, args)  ->
    (match is_abs_state_constructor env sigma (to_constr sigma name) with
     | Some (c, n) ->
       let num_args = Array.length args in
       let largs = List.map (fun e -> unwrap_definition env e sigma) ((Array.to_list args)) in
       let open List in
       let arg n = nth largs n in
       if num_args == 2 then
         (match n with
          | "BaseState" ->
            Option.bind (getAbsStack env (arg 0) sigma)
              (fun s -> Some (BaseState (s, (arg 1))))
          | "AbsAnd" | "AbsOr" ->
            option_map2 (fun a1 a2 ->
                if String.equal n "AbsAnd" then
                  AbsAnd (a1, a2)
                else AbsOr (a1, a2))
              (getAbsState env (arg 0) sigma)
              (getAbsState env (arg 1) sigma)
          | _ ->
            let () = print_endline ("Found " ^ n ^ " instead of the name of a constructor of AbsState") in
            None)
       else let () = print_endline "Number of args not 2" in
         None
     | None ->
       let () = print_endline ("Didn't get a constructor for a name: " ^ (Printingutils.print_kinds env name sigma)) in
       None)
  | _ ->
    let () = print_endline ("Found [" ^ (Printingutils.print_kinds env a sigma) ^ "] instead of an app in making AbsState") in
    None
        


let prove_aimpstk env p p' fenv sigma =
  let normP = normalize_ignore_opaques env (unwrap_definition env p sigma) sigma in
  let normP' = normalize_ignore_opaques env (unwrap_definition env p' sigma) sigma in
  let sigma, eq = equal env normP normP' sigma in
  if eq then
    Some (make_app aimp_self [p; fenv])
  else
    let asP = getAbsState env normP sigma in
    let asP' = getAbsState env normP' sigma in
    (match asP, asP' with
     | Some ap, Some ap' ->
       (match ap, ap' with
        | AbsAnd (a1, (BaseState (AbsStkTrue, m1))), AbsAnd (a2, (BaseState (AbsStkSize size, m2))) ->
          let a1_econstr = absStateToEconstr env a1 sigma in
          let a2_econstr = absStateToEconstr env a2 sigma in
          let sigma, eq = equal env m1 m2 sigma in
          let sigmaeqoption = option_map2 (fun a1' a2' -> equal env a1' a2' sigma) a1_econstr a2_econstr in
          (match sigmaeqoption with
           | Some (sigma, eq2) -> 
             if eq && eq2 then
               (* let () = print_endline (Stkhoaretree.econstr_to_string env sigma size) in *)
               let max_stack_size = Option.map (fun a1' -> (make_app maximum_stack_size_implied [a1'])) (a1_econstr) in
               let max_stack_size' = try Option.map (fun m -> normalize_ignore_opaques env m sigma) max_stack_size
                 with e -> failwith "couldn't normalize max_stack_size" in
               (* let () = print_endline "aimpstk.ml: trying to normalize size_leq_max_option"; *)
                 (* print_endline (match max_stack_size' with *)
                     (* | Some m -> *)
                       (* (Stkhoaretree.econstr_to_string env sigma m) *)
                        (* ^ " = " ^ (Printingutils.print_kinds env m sigma) *)
                     (* | None -> "None") in *)
               let size_leq_max_option =
                 Option.bind
                   a1_econstr
                   (fun a1' ->
                      Option.map
                        (fun max_stack ->
                          make_app
                            construct_n_leq_m
                            [size; max_stack])
                        max_stack_size') in
               let sigma, opt =
                 match size_leq_max_option with
                 | Some x -> CoqCoreInductives.unwrap_option env sigma x
                 | None -> sigma, None
               in
               (match opt, a1_econstr with
                | Some args, Some a1' ->
                  if Array.length args == 2 then
                    let size_leq_max = Array.get args 1 in
                    Some (make_app increase_absstack_okay
                            [size; a1'; m1; fenv;
                             size_leq_max])
                  else None
                | _, _ -> None)
             else None
           | None -> None)
        | _, _ -> None
       )
     | None, Some _ ->
       let () = print_endline "left absstate was none";
         print_endline (Stkhoaretree.econstr_to_string env sigma normP) in
       None
     | Some _, None ->
       let () = print_endline "right absstate was none";
         print_endline (Stkhoaretree.econstr_to_string env sigma normP') in
       None
     | None, None ->
       let () = print_endline "both absstates were none";
         print_endline (Stkhoaretree.econstr_to_string env sigma normP);
         print_endline (Stkhoaretree.econstr_to_string env sigma normP') in
       None)
    
