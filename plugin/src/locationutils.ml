open EConstr
open Names
open Termutils
open Induction

open Printingutils
open Stateutils
open Environ
open Declarations
open Indrec


let _coq_module parts =
  ModPath.MPfile (DirPath.make (List.map Id.of_string parts))

let coq_module mystr =
  _coq_module (List.rev (String.split_on_char '.' mystr))

(* mutually inductive bodies, if there's parameters, you have to push them *)

let get_inductive qualified_string ?(index = 0) =
  let parts = List.rev (String.split_on_char '.' qualified_string) in
  match parts with
  | hd :: tl -> (MutInd.make1 (KerName.make (_coq_module tl) (Label.make hd)), index)
  | _ -> failwith ("Empty parts for string" ^ (String.concat " " parts))

let get_constant qualified_string =
  let parts = List.rev (String.split_on_char '.' qualified_string) in
  match parts with
  | hd :: tl -> Constant.make2 (_coq_module tl) (Label.make hd)
  | _ -> failwith ("No parts found for " ^ qualified_string)
 

let get_inductive_econstr qualified_string ?(index = 0) =
  mkInd (get_inductive qualified_string ~index:index)
  (* let parts = List.rev (String.split_on_char '.' qualified_string) in *)
  (* let name = List.hd parts in *)
  (* let coq_mod = List.tl parts in *)
  (* mkInd (MutInd.make1 (KerName.make (_coq_module coq_mod) (Label.make name)), index) *)


let make_constructor c n =
  mkConstruct (fst (destInd (Evd.empty) c), n)
(* mkInd ((MutInd.make1 (Constant.canonical c)), 0) *)

let get_names_num_constructors ~env ~trm ~sigma =
  let ind = destInd sigma trm in
  let m_o = lookup_mind (fst (fst ind)) env in
  let b_o = m_o.mind_packets.(0) in
  let cs_o = b_o.mind_consnames in
  let ncons = Array.length cs_o in
  (cs_o, ncons)

let _get_constructors ?(sigma=Evd.empty) trm ncons =
  let ind = destInd sigma trm in
  List.map (fun i -> mkConstructUi (ind, i)
      (* make_constructor trm i *)
    ) (Collections.range 1 (ncons + 1))

let get_constructors ~env ~trm ~sigma =
  let _, ncons  = get_names_num_constructors ~env:env ~trm:trm ~sigma:sigma in
  _get_constructors ~sigma:sigma trm ncons
  (* let ind = destInd sigma trm in *)
  (* let m_o = lookup_mind (fst (fst ind)) env in *)
  (* let b_o = m_o.mind_packets.(0) in *)
  (* let cs_o = b_o.mind_consnames in *)
  (* let ncons = Array.length cs_o in *)
  (* (List.map (fun i -> make_constructor trm i ) (Collections.range 1 (ncons + 1))) *)
(* map_constructors (fun i -> fun evd -> i) env trm sigma *)

let get_constructors_hashtbl ~env ~trm ~sigma =
  let names, ncons = get_names_num_constructors ~env:env ~trm:trm ~sigma:sigma in
  let trm_cons = _get_constructors ~sigma:sigma trm ncons in
  Hashtbl.of_seq (List.to_seq (List.combine (List.map Names.Id.to_string (Array.to_list names)) trm_cons))

let is_constructor_of_inductive env sigma (i: inductive) t =
  let names, num_constructors = get_names_num_constructors env (mkInd i) sigma in
  let names_strings = List.map Names.Id.to_string (Array.to_list names) in
  let constructors =
    List.map (fun k -> ith_constructor_of_inductive i k)
      (Collections.range 1 (num_constructors + 1)) in
  (* let () = debug_print (Constr.debug_print t) in *)
  let ename = of_constr t in
  let equal_constructors =
    List.filter_map
      (fun p ->
         let _, is_eq = equal env ename (mkConstruct (fst p)) sigma in
         if is_eq then Some p
         else None)
      (List.combine constructors names_strings) in
  match equal_constructors with
  | [] -> None
  | hd :: _ -> Some hd

let sht: inductive =
  get_inductive "Imp_LangTrick.Stack.StkHoareTree.stk_hoare_tree" ~index:0

let prod: inductive =
  get_inductive "Coq.Init.Datatypes.prod" ~index:0

let is_stk_hoare_tree_constructor env sigma t =
  is_constructor_of_inductive env sigma sht t

let rec get_pair_from_prod env t sigma =
  let open Constr in
  match kind t with
  | App (name, args) ->
    let arg = Array.get args in
    if Array.length args == 4 then
      (match is_constructor_of_inductive env sigma prod name with
       | None -> failwith ("not a pair " ^ (print_kinds env (of_constr name) sigma))
       | Some _ ->
         (arg 2, arg 3))
    else failwith ("not a pair with args " ^ (string_of_int (Array.length args)) ^ " " ^ (print_kinds env (of_constr t) sigma))
  | _ -> failwith ("not a pair " ^ (print_kinds env (of_constr t) sigma))

let make_pair_type env sigma t1 t2 =
  mkApp ((mkInd prod), (Array.of_list [t1;t2]))

let prod_pair_constructor env sigma =
  let tbl = get_constructors_hashtbl env (mkInd prod) sigma in
  Hashtbl.find tbl "pair"

let make_pair env sigma t1 t2 =
  let pair = prod_pair_constructor env sigma in
  let _, type1 = normalize_type env t1 sigma in
  let _, type2 = normalize_type env t2 sigma in
  (make_pair_type env sigma type1 type2, mkApp (pair, Array.of_list [type1; type2; t1; t2]))


(* let get_inductive_constructor ind name = *)
(*   mkConstruct (fst (destInd (Evd.empty) ind *)
