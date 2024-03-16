open Locationutils
open EConstr

let make_constant qualified_name =
  try (mkConst (get_constant qualified_name))
  with Not_found -> failwith ("Name " ^ qualified_name ^ " not found")


let imp_stack = get_inductive "Imp_LangTrick.Stack.StackLanguage.imp_stack" ~index:0

let aexp_stack = get_inductive "Imp_LangTrick.Stack.StackLanguage.aexp_stack" ~index:0

let bexp_stack = get_inductive "Imp_LangTrick.Stack.StackLanguage.bexp_stack" ~index:0

let fun_stk = get_inductive "Imp_LangTrick.Stack.StackLanguage.fun_stk" ~index:0

let aexp_stack_frame = get_inductive "Imp_LangTrick.Stack.StackFrameBase.aexp_frame_rule" ~index:0

let fun_stk_constructor = make_constructor (mkInd fun_stk) 1

let funcs_frame = make_constant "Imp_LangTrick.Stack.FuncsFrame.funcs_frame"

let frame_of_aexp = make_constant "Imp_LangTrick.Stack.FuncsFrame.frame_of_aexp"

let frame_of_bexp = make_constant "Imp_LangTrick.Stack.FuncsFrame.frame_of_bexp"

let absstate = get_inductive "Imp_LangTrick.Stack.StackLogicGrammar.AbsState" ~index:0

let absstack = get_inductive "Imp_LangTrick.Stack.StackLogicGrammar.AbsStack" ~index:0
let absstate_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let absstate_tbl env sigma =
  let tbl = !absstate_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(mkInd absstate) ~sigma:sigma
    else
      tbl
  in absstate_tbl_ref := new_tbl; new_tbl

let absstack_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let absstack_tbl env sigma =
  let tbl = !absstack_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(mkInd absstack) ~sigma:sigma
    else
      tbl
  in absstack_tbl_ref := new_tbl; new_tbl

let imp_stack_cons_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let imp_stack_cons_tbl env sigma =
  let tbl = !imp_stack_cons_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(mkInd imp_stack) ~sigma:sigma
    else
      tbl
  in imp_stack_cons_tbl_ref := new_tbl; new_tbl

let sarray e = Array.of_list (e :: [])


let construct_update = make_constant "Imp_LangTrick.Stack.StateUpdateReflection.construct_state_update_rel"

(* let coq_option_bind = make_constant "Imp_LangTrick.BaseUtils.MyOptionUtils.option_bind" *)

let coq_state_update = make_constant "Imp_LangTrick.Stack.StackLogicBase.state_update"

let construct_state_stk_size_inc = make_constant "Imp_LangTrick.Stack.StackIncreaseAdequacy.construct_state_stk_size_inc"

let state_stack_size_inc = make_constant "Imp_LangTrick.Stack.StackIncrease.absstate_stack_size_inc"

let construct_aexp_stack_pure_rel = make_constant "Imp_LangTrick.Stack.StackPurestBaseReflection.construct_aexp_stack_pure_rel"

let construct_bexp_stack_pure_rel = make_constant "Imp_LangTrick.Stack.StackPurestBaseReflection.construct_bexp_stack_pure_rel"

(* aimp helpers *)

let aimp_self = make_constant "Imp_LangTrick.Stack.StackLogic.self_implication"

let coq_option_map = make_constant "Coq.Init.Datatypes.option_map"

let atruestk = make_constant "Imp_LangTrick.Stack.StackLogic.atruestk"
    
let afalsestk = (make_constant "Imp_LangTrick.Stack.StackLogic.afalsestk")

let aimpstk = make_constant "Imp_LangTrick.Stack.StackLogic.aimpstk"

let make_app myfun args =
  mkApp (myfun, Array.of_list args)

let get_precondition = make_constant "Imp_LangTrick.Stack.StkHoareTree.get_precondition"

let get_postcondition = make_constant "Imp_LangTrick.Stack.StkHoareTree.get_postcondition"

let increase_absstack_okay = make_constant "Imp_LangTrick.ProofCompiler.PluginHelpers.increase_absstack_okay'"

let construct_n_leq_m = make_constant "Imp_LangTrick.Stack.StackFrameReflection.construct_n_le_m"

let maximum_stack_size_implied = make_constant "Imp_LangTrick.ProofCompiler.PluginHelpers.maximum_stack_size_implied"

let nth_error = make_constant "Coq.Lists.List.nth_error"

let fact_env_valid_means_aimpstk = make_constant "Imp_LangTrick.ProofCompiler.PluginHelpers.fact_env_valid_means_aimpstk"
