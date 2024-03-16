open Termutils
open Locationutils
open CheckerConstants
open MutualInductives

let add_frame_rules env sigma =
  let mind_body, one_body = Global.lookup_inductive aexp_stack_frame in
  let bodies = mind_body.mind_packets in
  let bindings = Contextutils.bindings_for_inductive env mind_body bodies in
  (List.fold_left
    (fun acc elmt ->
       Environ.push_rel elmt acc)
    env
    bindings,
   bindings, mind_body)

let construct_aexp_frame_rule env sigma =
  let newenv, bindings, mind_body = add_frame_rules env sigma in
  let bexp_frame_rule = Names.ith_mutual_inductive aexp_stack_frame 2 in
  (* let bodies = mind_body.mind_packets in *)
  (* let bexp_frame_rule = Array.get bodies 1 in *)
  (* let bexp_name = bexp_frame_rule.mind_typename in *)
  Printingutils.inductive_to_string bexp_frame_rule

let aexp_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let aexp_tbl env sigma frame_tbl =
  let tbl = !aexp_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(Hashtbl.find frame_tbl "aexp_frame_rule") ~sigma:sigma
    else
      tbl
  in aexp_tbl_ref := new_tbl; new_tbl

let args_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let args_tbl env sigma frame_tbl =
  let tbl = !args_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(Hashtbl.find frame_tbl "args_frame_rule") ~sigma:sigma
    else
      tbl
  in args_tbl_ref := new_tbl; new_tbl

let bexp_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let bexp_tbl env sigma frame_tbl =
  let tbl = !bexp_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(Hashtbl.find frame_tbl "bexp_frame_rule") ~sigma:sigma
    else
      tbl
  in bexp_tbl_ref := new_tbl; new_tbl

let imp_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let imp_tbl env sigma frame_tbl =
  let tbl = !imp_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(Hashtbl.find frame_tbl "imp_frame_rule") ~sigma:sigma
    else
      tbl
  in imp_tbl_ref := new_tbl; new_tbl

let setup env sigma =
  let open Declarations in
  let env, bindings, mind_body, bodies, num_types = add_mutual_inductive_defs_to_env env aexp_stack_frame in
  let env, frame_tbl = get_mutind_hashtbl env aexp_stack_frame in
  let aexp_tbl = aexp_tbl env sigma frame_tbl in
  let args_tbl = args_tbl env sigma frame_tbl in
  let bexp_tbl = bexp_tbl env sigma frame_tbl in
  let imp_tbl = imp_tbl env sigma frame_tbl in
  (env, aexp_tbl, args_tbl, bexp_tbl, imp_tbl)

let print_bodies_typenames env sigma =
  let open Declarations in
  let env, bindings, mind_body, bodies, num_types = add_mutual_inductive_defs_to_env env aexp_stack_frame in
  (* let newenv, bindings, mind_body = add_frame_rules env sigma in *)
  (* let bodies = Array.to_list mind_body.mind_packets in *)
  let typenames = List.map (fun b -> Names.Id.to_string b.mind_typename) bodies in
  let () = List.iter (fun i -> print_endline ("Type names: " ^ i)) typenames in
  let () = print_endline ("Num types: " ^ (string_of_int mind_body.mind_ntypes)) in
  env, List.map (fun i -> EConstr.mkVar i) (List.map (fun b -> b.mind_typename) bodies)


(* let construct_bexp_frame_rule env sigma b = *)
(*   let newenv, bindings, mind_body = add_frame_rules env sigma in *)
(*   (fun args -> mkAppl (mkInd  *)


(* constructing terms --
   if you pass something to a function that refers to something in your local environment, you'll need to shift it so that it matches


env: standard environment, variables to types, has some global info too
sigma: state, stores universe constraints, evars (and their constraints), etc. can often ignore in theory, but will mess up with tactics. sometimes with automation you'll get "Universe 37 is not defined!" :(
(every time you reduce/typecheck/etc. -> modifies the constraints, mostly around universes, mostly invisible to the user, but really matters with automation)

plugin: https://github.com/coq/coq/tree/master/doc/plugin_tutorial
   https://github.com/coq/coq/blob/master/doc/plugin_tutorial/tuto1/src/g_tuto1.mlg#L102

good practice to always have sigma

nothing well-defined without env and sigma
*)
