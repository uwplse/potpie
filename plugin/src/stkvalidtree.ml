open Stkhoaretree
open Locationutils
open EConstr

let svt = get_inductive "Imp_LangTrick.Stack.StkHoareTree.stk_valid_tree" ~index:0
let svt_constructors_tbl_ref = ref (Hashtbl.of_seq (List.to_seq []))
let svt_constructors_tbl env sigma =
  let tbl = !svt_constructors_tbl_ref in
  let new_tbl =
    if Hashtbl.length tbl = 0 then
      get_constructors_hashtbl ~env:env ~trm:(mkInd svt) ~sigma:sigma
    else
      tbl
  in svt_constructors_tbl_ref := new_tbl; new_tbl

let sur = get_inductive "Imp_LangTrick.Stack.StackLogicBase.state_update_rel" ~index:0

type inputs =
  {p : types;
   i : types;
   q : types;
   fenv : types;
   fact_env : types}

let inputs_to_array (i: inputs) =
  Array.of_list (i.p :: i.i :: i.q :: i.fenv :: i.fact_env :: [])
   
type stk_valid_tree =
  | StkValidHTSkip of inputs *
                      types * (* P = Q *)
                      types * (* i = Skip_Stk *)
                      types (* fact_env_valid fact_env fenv *)
  | StkValidHTAssign of
      inputs *
      types * (* k *)
      types * (* a *)
      types * (* state_update_rel k a q p *)
      types * (* i = Assign_Stk k a *)
      types * (* fact_env_valid fact_env fenv *)
      types (* StackPurestBase.aexp_stack_pure_rel a fenv *)
  | StkValidHTPush of
      inputs *
      types * (* state_stk_size_inc 1 p q *)
      types * (* i = Push_Stk *)
      types (* fact_env_valid fact_env fenv *)
  | StkValidHTPop of
      inputs *
      types * (* p1 *)
      types * (* p2 *)
      types * (* p = AbsAnd p1 p2 *)
      types * (* state_stk_size_inc q p1 *)
      types * (* i = Pop_Stk *)
      types (* fact_env_valid *)
  | StkValidHTSeq of
      inputs *
      types * (* R *)
      stk_hoare_tree * (* h1: stk_hoare_tree *)
      stk_hoare_tree * (* h2: stk_hoare_tree *)
      types * (* i1 *)
      types * (* i2 *)
      types * (* i = Seq_Stk *)
      types * (* valid facts *)
      stk_valid_tree * (* stk_valid_tree P i1 R fenv fact_env H1 -> *)
      stk_valid_tree (* stk_valid_tree R i2 Q fenv fact_env H2 -> *)
  | StkValidHTIf of
      inputs *
      types * (*forall (b : bexp_stack) *)
      types * types * (* (i1 i2 : imp_stack) *)
      stk_hoare_tree * stk_hoare_tree * (* (H1 H2 : stk_hoare_tree), *)
      types * (* i = If_Stk b i1 i2 -> *)
      types * (* fact_env_valid fact_env fenv -> *)
      types * (* StackPurestBase.bexp_stack_pure_rel b fenv -> *)
      stk_valid_tree * (* stk_valid_tree (atruestk b P) i1 Q fenv fact_env H1 -> *)
      stk_valid_tree (* stk_valid_tree (afalsestk b P) i2 Q fenv fact_env H2 -> *)
  | StkValidHTWhile of
      inputs *
      types * types * (* forall (b : bexp_stack) (i' : imp_stack) *)
      stk_hoare_tree * (* (H : stk_hoare_tree), *)
      types * (* i = While_Stk b i' -> *)
      types * (* Q = afalsestk b P -> *)
      types * (* fact_env_valid fact_env fenv -> *)
      types * (* StackPurestBase.bexp_stack_pure_rel b fenv -> *)
      stk_valid_tree (* stk_valid_tree (atruestk b P) i' P fenv fact_env  H *)
  | StkValidHTCon of
      inputs *
      (types * types) * (types * types) * (* forall (Impl1 Impl2 : AbsState * AbsState) *)
      stk_hoare_tree * types * types * (* (H : stk_hoare_tree) (P' Q' : AbsState), *)
      types * (* Impl1 = (P, P') -> *)
      types * (* Impl2 = (Q', Q) -> *)
      types * (* (P --->>> P') fenv -> *)
      types * (* (Q' --->>> Q) fenv -> *)
      stk_valid_tree (* stk_valid_tree P' i Q' fenv fact_env H -> *)
  | StkValidHTConLeft of
      inputs *
      (types * types) * (* forall (Impl : AbsState * AbsState) *)
      types * stk_hoare_tree * (* (P' : AbsState) (H : stk_hoare_tree) *)
      types * (* (n : nat), *)
      types * (* Impl = (P, P') -> *)
      types * (* fact_env_valid fact_env fenv -> *)
      types * (* (P --->>> P') fenv -> *)
      types * (* nth_error fact_env n = Some Impl -> *)
      stk_valid_tree (* stk_valid_tree P' i Q fenv fact_env H -> *)
  | StkValidHTConRight of
      inputs *
      (types * types) * (* forall (Impl : AbsState * AbsState) *)
      types * stk_hoare_tree * (* (Q' : AbsState) (H : stk_hoare_tree) *)
      types * (* (n : nat), *)
      types * (* Impl = (Q', Q) -> *)
      types * (* fact_env_valid fact_env fenv -> *)
      types * (* (Q' --->>> Q) fenv -> *)
      types * (* nth_error fact_env n = Some Impl -> *)
      stk_valid_tree (* stk_valid_tree P i Q' fenv fact_env H -> *)


let get_svt_name (s: stk_valid_tree) =
  match s with
  | StkValidHTSkip _ -> "StkValidHTSkip"
  | StkValidHTAssign _ -> "StkValidHTAssign"
  | StkValidHTPush _ -> "StkValidHTPush"
  | StkValidHTPop _ -> "StkValidHTPop"
  | StkValidHTSeq _ -> "StkValidHTSeq"
  | StkValidHTIf _ -> "StkValidHTIf"
  | StkValidHTWhile _ -> "StkValidHTWhile"
  | StkValidHTCon _ -> "StkValidHTCon"
  | StkValidHTConLeft _ -> "StkValidHTConLeft"
  | StkValidHTConRight _ -> "StkValidHTConRight"

let get_stk_valid_inputs (s: stk_valid_tree) =
  match s with
  | StkValidHTSkip (i, _, _, _) -> i
  | StkValidHTAssign (i, _, _, _, _, _, _) -> i
  | StkValidHTPush (i, _, _, _) -> i
  | StkValidHTPop (i, _, _, _, _, _, _) -> i
  | StkValidHTSeq (i, _, _, _, _, _, _, _, _, _) -> i
  | StkValidHTIf (i, _, _, _, _, _, _, _, _, _, _) -> i
  | StkValidHTWhile (i, _, _, _, _, _, _, _, _) -> i
  | StkValidHTCon (i, _, _, _, _, _, _, _, _, _, _) -> i
  | StkValidHTConLeft (i, _, _, _, _, _, _, _, _, _) -> i
  | StkValidHTConRight (i, _, _, _, _, _, _, _, _, _) -> i


let rec make_stk_valid_tree env sigma (s: stk_valid_tree) =
  let tbl = svt_constructors_tbl env sigma in
  let construct_stk_valid_tree =
    (fun n -> fun args -> mkApp (Hashtbl.find tbl n, args)) in
  let name = get_svt_name s in
  (* let () = print_endline ("make stk valid tree name: " ^ name) in *)
  let args_array = (fun other_args ->
      Array.append (inputs_to_array (get_stk_valid_inputs s))
        (Array.of_list other_args)) in
  let open Termutils in
  match s with
  | StkValidHTSkip (i, peqq, ieq, facts_valid) ->
    let e = construct_stk_valid_tree name
        (args_array (peqq :: ieq :: facts_valid :: [])) in
    (* let () = (try print_message env e sigma *)
              (* with Not_found -> failwith "not found execption 6") in *)
    Some e
  | StkValidHTAssign (i, k, a, state_update, i_eq, facts_valid, pure) ->
    Some (
      construct_stk_valid_tree name
        (args_array (k :: a :: state_update :: i_eq :: facts_valid :: pure :: [])))
  | StkValidHTPush (i, size_inc, i_eq, facts_valid) ->
    (* None *)
    Some (
      construct_stk_valid_tree name
        (args_array [size_inc; i_eq; facts_valid]))
  | StkValidHTPop (_, p1, p2, p_eq, size_inc, i_eq, facts_valid) ->
    Some (
      construct_stk_valid_tree name
        (args_array [p1; p2; p_eq; size_inc; i_eq; facts_valid]))
  | StkValidHTSeq (_, r, h1, h2, i1, i2, i_eq, facts_valid, valid1, valid2) ->
    let h1o = make_stk_hoare_tree env sigma h1 in
    let h2o = make_stk_hoare_tree env sigma h2 in
    let v1o = make_stk_valid_tree env sigma valid1 in
    let v2o = make_stk_valid_tree env sigma valid2 in
    (match h1o, h2o, v1o, v2o with
     | Some h1', Some h2', Some v1', Some v2' ->
       Some (
         construct_stk_valid_tree name
           (args_array [r;
                        h1'; h2'; i1; i2; i_eq;
                        facts_valid; v1'; v2']))
     | _, _, _, _ ->
       let () = print_endline "Failed at valid seq" in
       None)
  | StkValidHTIf (_, b, i1, i2, h1, h2, i_eq, facts_valid, pure, valid1, valid2) ->
    let h1o = make_stk_hoare_tree env sigma h1 in
    let h2o = make_stk_hoare_tree env sigma h2 in
    let v1o = make_stk_valid_tree env sigma valid1 in
    let v2o = make_stk_valid_tree env sigma valid2 in
    (match h1o, h2o, v1o, v2o with
     | Some h1', Some h2', Some v1', Some v2' ->
       Some (
         construct_stk_valid_tree name
           (args_array [b; i1; i2;
                        h1'; h2'; i_eq; facts_valid; pure; v1'; v2']))
     | _, _, _, _ ->
       let () = print_endline "Failed at valid if" in
       None
    )
  | StkValidHTWhile (_, b, i', tree, i_eq, q_eq, facts_valid, pure, valid) ->
    let valid_econstr = make_stk_valid_tree env sigma valid in
    let treeo = make_stk_hoare_tree env sigma tree in
    (match valid_econstr, treeo with
     | Some v, Some tree' -> 
       Some (
         construct_stk_valid_tree name
           (args_array [b; i'; tree'; i_eq; q_eq; facts_valid; pure; v]))
     | _, _ ->
       let () = print_endline "Failed at valid while" in
       None)
  | StkValidHTCon (_, impl1, impl2, tree, p', q', impl1_eq, impl2_eq, aimp1, aimp2, valid) ->
    let ho = make_stk_hoare_tree env sigma tree in
    let vo = make_stk_valid_tree env sigma valid in
    (match impl1, impl2, ho, vo with
     | (p1, p2), (q1, q2), Some h, Some v ->
       Some (
         construct_stk_valid_tree name
           (args_array [snd (make_pair env sigma p1 p2);
                        snd (make_pair env sigma q1 q2);
                        h;
                        p';
                        q';
                        impl1_eq;
                        impl2_eq;
                        aimp1;
                        aimp2;
                        v]))
     | _, _, _, _ ->
       let () = print_endline "Failed at valid con" in
       None)
  | StkValidHTConLeft (_, impl1, p', tree, n, impl_eq, valid_facts, aimp, nth, valid) ->
    let ho = make_stk_hoare_tree env sigma tree in
    let vo = make_stk_valid_tree env sigma valid in
    (match impl1, ho, vo with
     | (p1, p2), Some h, Some v ->
       Some (
         construct_stk_valid_tree name
           (args_array [snd (make_pair env sigma p1 p2);
                        p';
                        h;
                        n;
                        impl_eq;
                        valid_facts;
                        aimp;
                        nth;
                        v]))
     | _, _, _ -> None)
  | StkValidHTConRight (_, impl2, q', tree, n, impl_eq, valid_facts, aimp, nth, valid) ->
    let ho = make_stk_hoare_tree env sigma tree in
    let vo = make_stk_valid_tree env sigma valid in
    (match impl2, ho, vo with
     | (q1, q2), Some h, Some v ->
       Some (
         construct_stk_valid_tree name
           (args_array [snd (make_pair env sigma q1 q2);
                        q';
                        h;
                        n;
                        impl_eq;
                        valid_facts;
                        aimp;
                        nth;
                        v]))
     | _, _, _ -> None)
