open Termutils
open Locationutils
(* open CheckerConstants *)
open EConstr

type aexp_stk =
  | Const_Stk of types
  | Var_Stk of types
  | Plus_Stk of aexp_stk * aexp_stk
  | Minus_Stk of aexp_stk * aexp_stk
  | App_Stk of types * (aexp_stk list)

type bexp_stk =
  | True_Stk
  | False_Stk
  | Neg_Stk of bexp_stk
  | And_Stk of bexp_stk * bexp_stk
  | Or_Stk of bexp_stk * bexp_stk
  | Leq_Stk of aexp_stk * aexp_stk
  | Eq_Stk of aexp_stk * aexp_stk

type imp_stk =
  | Skip_Stk
  | Assign_Stk of types * aexp_stk
  | Push_Stk
  | Pop_Stk
  | Seq_Stk of imp_stk * imp_stk
  | If_Stk of bexp_stk * imp_stk * imp_stk
  | While_Stk of bexp_stk * imp_stk

type fun_stk = {name: types; args: types; body: imp_stk; return_expr: aexp_stk; return_pop: types}

let aexp_stack_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let aexp_stack_tbl env sigma =
  let tbl = !aexp_stack_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(mkInd CheckerConstants.aexp_stack) ~sigma:sigma
    else
      tbl
  in aexp_stack_tbl_ref := new_tbl; new_tbl

let bexp_stack_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let bexp_stack_tbl env sigma =
  let tbl = !bexp_stack_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(mkInd CheckerConstants.bexp_stack) ~sigma:sigma
    else
      tbl
  in bexp_stack_tbl_ref := new_tbl; new_tbl

let imp_stack_tbl env sigma = CheckerConstants.imp_stack_cons_tbl env sigma

let rec aexp_stk_of_econstr env sigma a =
  match kind sigma a with
  | Constr.App (name, args) ->
    (match is_constructor_of_inductive env sigma CheckerConstants.aexp_stack (to_constr sigma name) with
     | Some (c, n) ->
       aexp_stk_of_name_and_args env sigma n (Array.to_list args)
     | None ->
       None)
  | _ -> None
and aexp_stk_of_name_and_args env sigma name args =
  match name with
  | "Const_Stk" ->
    (match args with
     | [n] -> Some (Const_Stk n)
     | _ -> None)
  | "Var_Stk" ->
    (match args with
     | [k] -> Some (Const_Stk k)
     | _ -> None)
  | "Plus_Stk" ->
    (match args with
     | [a1; a2] ->
       (match aexp_stk_of_econstr env sigma a1, aexp_stk_of_econstr env sigma a2 with
        | Some a1', Some a2' ->
          Some (Plus_Stk (a1', a2'))
        | _, _ -> None)
     | _ -> None)
  | "Minus_Stk" ->
    (match args with
     | [a1; a2] ->
       (match aexp_stk_of_econstr env sigma a1, aexp_stk_of_econstr env sigma a2 with
        | Some a1', Some a2' ->
          Some (Minus_Stk (a1', a2'))
        | _, _ -> None)
     | _ -> None)
  | "App_Stk" ->
    (match args with
     | [f; fun_args] ->
       let _, args_list = CoqCoreInductives.coq_list_to_list env fun_args sigma in
       let aexp_args = List.fold_left
           (fun acc elmt ->
              Option.bind acc (fun res -> Option.map (fun k -> k :: res) elmt))
           (Some [])
           (List.map (aexp_stk_of_econstr env sigma) args_list) in
       Option.lift (fun b -> App_Stk (f, b)) aexp_args
     | _ -> None)
  | _ -> None

let rec bexp_stk_of_econstr env sigma b =
  match kind sigma b with
  | Constr.App (name, args') ->
    let args = Array.to_list args' in
    (match is_constructor_of_inductive env sigma CheckerConstants.bexp_stack (to_constr sigma name) with
     | Some (c, n) ->
       (match n with
        | "True_Stk" -> Some True_Stk
        | "False_Stk" -> Some False_Stk
        | "Neg_Stk" ->
          (match args with
           | [b'] -> Option.map (fun b -> Neg_Stk b) (bexp_stk_of_econstr env sigma b')
           |  _ -> None)
        | "And_Stk" | "Or_Stk" ->
          (match args with
           | [b1; b2] ->
             Option.lift2 (fun e1 e2 ->
                 if String.equal n "And_Stk" then
                   And_Stk (e1, e2)
                 else Or_Stk (e1, e2))
               (bexp_stk_of_econstr env sigma b1)
               (bexp_stk_of_econstr env sigma b2)
           | _ -> None)
        | "Leq_Stk" | "Eq_Stk" ->
          (match args with
           | [a1; a2] ->
             Option.lift2 (fun e1 e2 ->
                 if String.equal n "Leq_Stk" then
                   Leq_Stk (e1, e2)
                 else Eq_Stk (e1, e2))
               (aexp_stk_of_econstr env sigma a1)
               (aexp_stk_of_econstr env sigma a2)
           | _ -> None)
        | _ -> None)
     | None -> None)
  | _ -> None

let rec imp_stk_of_econstr env sigma i =
  match kind sigma i with
  | Constr.App (name, args') ->
    let args = Array.to_list args' in
    (match is_constructor_of_inductive env sigma CheckerConstants.imp_stack (to_constr sigma name) with
     | Some (c, n) ->
       (match n with
        | "Skip_Stk" -> Some Skip_Stk
        | "Assign_Stk" ->
          (match args with
           | [k; a] ->
             Option.lift (fun aexp -> Assign_Stk (k, aexp))
               (aexp_stk_of_econstr env sigma a)
           | _ -> None)
        | "Push_Stk" -> Some Push_Stk
        | "Pop_Stk" -> Some Pop_Stk
        | "Seq_Stk" ->
          (match args with
           | [i1; i2] ->
             Option.lift2 (fun imp1 imp2 -> Seq_Stk (imp1, imp2))
               (imp_stk_of_econstr env sigma i1)
               (imp_stk_of_econstr env sigma i2)
           | _ -> None)
        | "If_Stk" ->
          (match args with 
           | [b; i1; i2] ->
             (match (bexp_stk_of_econstr env sigma b) with
              | Some b' ->
                Option.lift2 (fun imp1 imp2 -> If_Stk (b', imp1, imp2))
                  (imp_stk_of_econstr env sigma i1)
                  (imp_stk_of_econstr env sigma i2)
              | _ -> None)
           | _ -> None)
        | "While_Stk" ->
          (match args with
           | [b; i'] ->
             Option.lift2 (fun bexp imp -> While_Stk (bexp, imp))
               (bexp_stk_of_econstr env sigma b)
               (imp_stk_of_econstr env sigma i')
           | _ -> None)
        | _ -> None)
     | None -> None)
  | _ -> None


let fun_stk_of_econstr env sigma f =
  match kind sigma f with
  | Constr.App (name, args) ->
    let _, eq = equal env name CheckerConstants.fun_stk_constructor sigma in
    if eq then
      (match (Array.to_list args) with
       | [name; args; body; ret_expr; ret_pop] ->
         (match imp_stk_of_econstr env sigma body, aexp_stk_of_econstr env sigma ret_expr with
          | Some b, Some r ->
            Some { name = name;
                   args = args;
                   body = b;
                   return_expr = r;
                   return_pop = ret_pop }
          | _, _ -> None)
       | _ -> None)
    else None
  | _ -> None
         
         
      
    
