open Termutils
open EConstr
open CheckerConstants
open Locationutils

type stk_hoare_tree =
  | StkHTSkip of types (*  (P: AbsState) *)
  | StkHTAssign of types * types * types (* (P: AbsState) (k: stack_index) (a: aexp_stack) *)
  | StkHTPush of types (* (P: AbsState) *)
  | StkHTPop of types * types * types (* (P Q P': AbsState) *)
  | StkHTSeq of types * types * types * types * types * stk_hoare_tree * stk_hoare_tree (* (P Q R: AbsState) (i1 i2: imp_stack) (H1 H2: stk_hoare_tree) *)
  | StkHTIf of types * types * types * types * types * stk_hoare_tree * stk_hoare_tree (* (P Q: AbsState) (b: bexp_stack) (i1 i2: imp_stack) (H1 H2: stk_hoare_tree) *)
  | StkHTWhile of types * types *  types * stk_hoare_tree
  (* (P: AbsState) (b: bexp_stack) (i: imp_stack) (H: stk_hoare_tree) *)
  | StkHTConLeft of (types * types) * types * types * types * stk_hoare_tree (* StkHTConLeft (Impl: AbsState * AbsState) (i: imp_stack) (Q: AbsState) (n: nat) (H: stk_hoare_tree) *)
  | StkHTConRight of types * types * (types * types) * types * stk_hoare_tree (* (P: AbsState) (i: imp_stack) (Impl: AbsState * AbsState) (n: nat) (H: stk_hoare_tree) *)
  | StkHTCon of (types * types) * (types * types) * types * stk_hoare_tree  (* (Impl1 Impl2: AbsState * AbsState) (i: imp_stack) (H: stk_hoare_tree). *)


let get_pre env sigma tree =
  let open Locationutils in
  let open EConstr in
  match tree with
  | StkHTSkip p -> p
  | StkHTAssign (p, k, a) ->
    make_app coq_state_update [k; a; p]
  | StkHTPush p -> p
  | StkHTPop (p1, p2, q) ->
    make_app (Hashtbl.find (absstate_tbl env sigma) "AbsAnd") [p1; p2]
  | StkHTSeq (p, q, r, _, _, _, _) -> p
  | StkHTIf (p, _, _, _, _, _, _)  -> p
  | StkHTWhile (p, _, _, _) -> p
  | StkHTConLeft (impl, _, _, _, _) ->
    let (p, _) = impl in p
  | StkHTConRight (p, _, _, _, _) -> p
  | StkHTCon (impl, _, _, _) ->
    let (p, _) = impl in p


let get_post env sigma tree =
  let open EConstr in
  match tree with
  | StkHTSkip p -> p
  | StkHTAssign (p, k, a) ->
    p
  | StkHTPush p -> make_app state_stack_size_inc [Option.get (CoqCoreInductives.int_to_coq_nat 1); p]
  | StkHTPop (_, _, p') -> p'
  | StkHTSeq (_, _, r, _, _, _, _) -> r
  | StkHTIf (_, q, _, _, _, _, _) -> q
  | StkHTWhile (p, b, _, _) ->
    make_app afalsestk [b; p]
  | StkHTConLeft (_, _, q, _, _) -> q
  | StkHTConRight (_, _, impl, _, _) ->
    let (_, q) = impl in q
  | StkHTCon (_, impl, _, _) ->
    let (_, q) = impl in q

let get_imp env sigma tree =
  let open EConstr in
  let imp_table = imp_stack_cons_tbl env sigma in
  let open Hashtbl in
  match tree with
  |  StkHTSkip _ -> find imp_table "Skip_Stk"
  | StkHTAssign (p, k, a) -> make_app (find imp_table "Assign_Stk") [k; a]
  | StkHTPush _ -> find imp_table "Push_Stk"
  | StkHTPop _ -> find imp_table "Pop_Stk"
  | StkHTSeq (_, _, _, i1, i2, _, _) -> make_app (find imp_table "Seq_Stk") [i1; i2]
  | StkHTIf (_, _, b, i1, i2, _, _) -> make_app (find imp_table "If_Stk") [b; i1; i2]
  | StkHTWhile (_, b, i', _) -> make_app (find imp_table "While_Stk") [b; i']
  | StkHTConLeft (_, i, _, _, _) -> i
  | StkHTConRight (_, i, _, _, _) -> i
  | StkHTCon (_, _, i, _) -> i
    


let to_string sht =
  match sht with
  | StkHTSkip _ -> "StkHTSkip"
  | StkHTAssign _ -> "StkHTAssign"
  | StkHTPush _ -> "StkHTPush"
  | StkHTPop _ -> "StkHTPop"
  | StkHTSeq _ -> "StkHTSeq"
  | StkHTIf _ -> "StkHTIf"
  | StkHTWhile _ -> "StkHTWhile"
  | StkHTConLeft _ -> "StkHTConLeft"
  | StkHTConRight _ -> "StkHTConRight"
  | StkHTCon _ -> "StkHTCon"

let econstrs_to_strings env sigma econstrs =
  (List.map Pp.string_of_ppcmds (List.map (Printer.pr_constr_env env sigma) (List.map (to_constr sigma) econstrs)))

let econstr_to_string env sigma econstr =
  Pp.string_of_ppcmds (Printer.pr_constr_env env sigma (to_constr sigma econstr))


let parenthesize ?(left="(") ?(right=")") mylist =
  List.map (fun s -> left ^ s ^ right) mylist

let rec to_string_with_args sht env sigma =
  let tswa tree = "(" ^ (to_string_with_args tree env sigma) ^ ")" in
  match sht with
  | StkHTSkip (p) -> ("StkHTSkip ") ^ (Pp.string_of_ppcmds (Constr.debug_print (to_constr sigma p)))
  | StkHTAssign (p, k, a) ->
    "StkHTAssign " ^
      (String.concat " " (econstrs_to_strings env sigma [p;k;a]))
  | StkHTPush _ -> "StkHTPush"
  | StkHTPop _ -> "StkHTPop"
  | StkHTSeq (p, q, r, i1, i2, h1, h2) ->
    "StkHTSeq" ^
    (String.concat " " (List.append (econstrs_to_strings env sigma [p;q;r;i1;i2])
                          (List.map tswa [h1;h2])))
  | StkHTIf (p, q, b, i1, i2, h1, h2) ->
    "StkHTIf" ^
    (String.concat " " (List.append (econstrs_to_strings env sigma [p;q;b;i1;i2])
                          (List.map tswa [h1;h2])))
  | StkHTWhile _ -> "StkHTWhile"
  | StkHTConLeft _ -> "StkHTConLeft"
  | StkHTConRight _ -> "StkHTConRight"
  | StkHTCon (impl1, impl2, i, h) -> "StkHTCon"

let absstate_to_string env sigma a =
  let absstate_tbl = absstate_tbl env sigma in
  let base = Hashtbl.find absstate_tbl "BaseState" in
  let aand = Hashtbl.find absstate_tbl "AbsAnd" in
  let aor = Hashtbl.find absstate_tbl "AbsOr" in
  let open Termutils in
  let bargs = is_or_applies base a sigma in
  let andargs = is_or_applies aand a sigma in
  let orargs = is_or_applies aor a sigma in
  let rec helper a =
    match bargs, andargs, orargs with
    | Some _, None, None ->
      "BaseState"
    | None, Some args, None ->
      "AbsAnd[" ^ (String.concat "&" (List.map helper args)) ^ "]"
    | None, None, Some args ->
      "AbsOr[" ^ (String.concat "|" (List.map helper args)) ^ "]"
    | Some _, Some _, None -> "wrong 1"
    | Some _, None, Some _ -> "wrong 2"
    | Some _, Some _, Some _ -> "wrong 3"
    | None, Some _, Some _ -> "wrong 4"
    | None, None, None ->
      "[" ^ (String.concat " " (List.map (fun a -> Printingutils.print_kinds env a sigma) [base;aand;aor])) ^ "]" ^
      (* (string_of_bool (applies ba *)
      (Printingutils.print_kinds env a sigma)
      (* "[" ^ (String.concat " " (econstrs_to_strings env sigma [base; aand; aor])) ^ "]" *)
      (* (econstr_to_string env sigma a) *)
  in
  helper a

let rec max_depth tree =
  match tree with
  | StkHTSeq (_, _, _, _, _, h1, h2) ->
    1 + (max (max_depth h1) (max_depth h2))
  | StkHTIf (_, _, _, _, _, h1, h2) ->
    1 + (max (max_depth h1) (max_depth h2))
  | StkHTWhile (_, _, _, h) ->
    1 + max_depth h
  | StkHTConLeft (_, _, _, _, h) ->
    1 + max_depth h
  | StkHTConRight (_, _, _, _, h) ->
    1 + max_depth h
  | StkHTCon (_, _, _, h) ->
    1 + max_depth h
  | _ -> 0

let to_string_with_args_abbr_tl_rec env sigma tree =
  let rec helper iters t res =
    if iters >= 2 then
      res "..."
    else 
    match t with
    | StkHTAssign (_, k, a) ->
      res ("StkHTAssign(" ^ (String.concat ":=" (econstrs_to_strings env sigma [k; a])) ^ ")")
    | StkHTSeq (p, q, r, i1, i2, h1, h2) ->
      helper (iters + 1) h2 (fun s' -> res ((helper (iters + 1) h1 (fun s -> "StkHTSeq(" ^ (String.concat "," (List.append (parenthesize ~left:"[" ~right:"]" (List.rev_map (absstate_to_string env sigma) [r; q; p]))
                                                                                    (econstrs_to_strings env sigma [i1;i2]))) ^ "," ^ s)) ^ "," ^ s' ^ ")"))
    | StkHTIf (_, _, b, i1, i2, h1, h2) ->
      helper (iters + 1) h2 (fun s' -> (helper (iters + 1) h1 (fun s -> "StkHTIf" ^ "(" ^ "if " ^ (econstr_to_string env sigma b) ^ " then " ^ (econstr_to_string env sigma i1) ^ " else " ^ (econstr_to_string env sigma i2) ^ " " ^ "[" ^ s ^ "]")) ^ "[" ^ s' ^ "]" ^ ")")
    | StkHTWhile (_, b, i, h) ->
      helper (iters + 1) h (fun s -> res ( "StkHTWhile(" ^ "while " ^ (econstr_to_string env sigma b) ^ " do " ^ (econstr_to_string env sigma i) ^ " " ^ s ^ ")"))
    | StkHTConLeft (_, _, _, _, h) ->
      helper (iters + 1)  h (fun s -> res ("StkHTConLeft(" ^ s ^ ")"))
    | StkHTConRight (_, _, _, _, h) ->
      helper (iters + 1)  h (fun s -> res ("StkHTConRight(" ^ s ^ ")"))
    | StkHTCon (_, _, _, h) -> helper (iters + 1) h (fun s' -> res ("StkHTCon(" ^ s' ^ ")"))
    | _ -> to_string t
  in
  helper 0 tree (fun i -> i)
    

let rec to_string_with_args_abbr ?(max_level=5) tree env sigma =
  let tswa tree = "(" ^ (to_string_with_args_abbr ~max_level:(max_level - 1) tree env sigma) ^ ")" in
  let name = to_string tree in
  if max_level == 0 then
    "..."
  else
    name ^ (
      match tree with
      | StkHTAssign (_, k, a) ->
        "(" ^ (String.concat ":=" (econstrs_to_strings env sigma [k; a])) ^ ")"
      | StkHTSeq (p, q, r, i1, i2, h1, h2) ->
        "(" ^ (String.concat "," (List.append (parenthesize ~left:"[" ~right:"]" (List.map (absstate_to_string env sigma) [p;q;r])) ( List.append (econstrs_to_strings env sigma [i1; i2]) (List.map tswa [h1;h2])))) ^ ")"
      | StkHTIf (_, _, b, i1, i2, h1, h2) ->
        "(" ^ "if " ^ (econstr_to_string env sigma b) ^ " then " ^ (econstr_to_string env sigma i1) ^ " else " ^ (econstr_to_string env sigma i2) ^ " " ^ (String.concat " " (List.map tswa [h1; h2])) ^ ")"
      | StkHTWhile (_, b, i, h) ->
        "(" ^ "while " ^ (econstr_to_string env sigma b) ^ " do " ^ (econstr_to_string env sigma i) ^ " " ^ (tswa h) ^ ")"
      | StkHTConLeft (_, _, _, _, h) ->
        tswa h
      | StkHTConRight (_, _, _, _, h) ->
        tswa h
      | StkHTCon (_, _, _, h) ->
        tswa h
      | _ -> "")

let collect_trees ?(max=10) pred t =
  let rec helper tree res =
    if (List.length res) >= max then
      res
    else
      let newres = if pred tree then tree :: res else res in
      (* let () = print_endline (string_of_int (List.length newres)) in *)
      (* let () = print_endline (string_of_int max) in *)
      if (List.length newres) >= max then
        (* let () = print_endline "return early 1" in *)
        newres
      else 
        (match tree with
         | StkHTSeq (_, _, _, _, _, h1, h2) ->
           (* let () = print_endline "seq" in *)
           let newnewres = helper h1 newres in
           if (List.length newnewres) >= max then
             (* let () = print_endline "return early 2" in *)
             newnewres
           else
             helper h2 newnewres
         | StkHTIf (_, _, _, _, _, h1, h2) ->
           (* let () = print_endline "if" in *)
           let res' = helper h1 newres in
           if (List.length res') >= max then
             (* let () = print_endline "return early 3" in *)
             res'
           else
             helper h2 res'
         | StkHTWhile (_, _, _, h) ->
           (* let () = print_endline "while" in *)
           helper h newres
         | StkHTConLeft (_, _, _, _, h) ->
           (* let () = print_endline "left" in *)
           helper h newres
         | StkHTConRight (_, _, _, _, h) ->
           (* let () = print_endline "right" in *)
           helper h newres
         | StkHTCon (_, _, _, h) ->
           (* let () = print_endline "con" in *)
           helper h newres
         | _ -> newres)
  in
  helper t []
      
                                                     

let construct_hoare_tree name args =
  let num_args = Array.length args in
  let largs = Array.to_list args in
  let open List in
  match name with
  | "StkHTSkip" ->
    if num_args == 1 then
      Some (StkHTSkip (hd largs))
    else None
  | "StkHTAssign" ->
    (if num_args == 3 then
      Some (StkHTAssign ((nth largs 0), nth largs 1, (nth largs 2)))
    else None)
  | "StkHTPush" ->
    if num_args == 1 then
      Some (StkHTSkip (hd largs))
    else None
  | "StkHTPop" ->
    if num_args == 3 then
      Some (StkHTPop (nth largs 0, nth largs 1, (nth largs 2)))
    else None
  | "StkHTSeq" ->
    None
  | _ -> None
      


let rec recurse_over_constr env t sigma =
  (* let () = Printingutils.print_warn (Constr.debug_print t) in *)
  let open Constr in
  match kind t with
  | App (name, args) ->
    (* let () = Printingutils.print_warn (Constr.debug_print name) in *)
    (match Locationutils.is_stk_hoare_tree_constructor env sigma name with
     | None -> failwith "Recursed over wrong part"
     | Some (c, n) ->
       construct_hoare_tree env sigma n args)
  | _ -> None
and construct_hoare_tree env sigma name args =
  let num_args = Array.length args in
  let largs = List.map (fun e -> unwrap_definition env e sigma) (List.map of_constr  (Array.to_list args)) in
  let open List in
  (* may need more eta expansions in here if we have partially applied terms *)
  let arg n = nth largs n in
  match name with
  | "StkHTSkip" ->
    if num_args == 1 then
      Some (StkHTSkip (arg 0))
    else None
  | "StkHTAssign" ->
    (if num_args == 3 then
      Some (StkHTAssign (arg 0, arg 1, arg 2))
    else None)
  | "StkHTPush" ->
    if num_args == 1 then
      Some (StkHTSkip (arg 0))
    else None
  | "StkHTPop" ->
    if num_args == 3 then
      Some (StkHTPop (arg 0, arg 1, arg 2))
    else None
  | "StkHTSeq" | "StkHTIf" ->
    if num_args == 7 then
      (let h1 = to_constr sigma (nth largs 5) in
       let h2 = to_constr sigma (nth largs 6) in
       (match (recurse_over_constr env h1 sigma, recurse_over_constr env h2 sigma) with
        | (Some h1', Some h2') ->
          let a1, a2, a3, a4, a5, a6, a7 = (arg 0,
                          nth largs 1,
                          nth largs 2,
                          nth largs 3,
                          nth largs 4,
                          h1', h2') in
          Some
            (if String.equal name "StkHTSeq"
             then (StkHTSeq (a1, a2, a3, a4, a5, a6, a7))
             else (StkHTIf (a1, a2, a3, a4, a5, a6, a7)))
        | _ -> None)
       )
    else None
  | "StkHTWhile" ->
    if num_args == 4 then
      (let h = to_constr sigma (arg 3) in
       match recurse_over_constr env h sigma with
       | Some h' ->
         Some (StkHTWhile (arg 0, arg 1, arg 2, h'))
       | _ -> None)
    else None
  | "StkHTConLeft" | "StkHTConRight" ->
    let is_left = String.equal name "StkHTConLeft" in
    if num_args == 5 then
      (let h = to_constr sigma (arg 4) in
       match recurse_over_constr env h sigma with
       | Some h' ->
         let a1, a2 = Locationutils.get_pair_from_prod env (to_constr sigma (arg (if is_left then 0 else 2))) sigma in
         Some (
           if is_left then
             StkHTConLeft ((of_constr a1, of_constr a2),
                           arg 1,
                           arg 2,
                           arg 3,
                           h')
           else
             StkHTConRight (arg 0,
                            arg 1,
                            (of_constr a1, of_constr a2),
                            arg 3,
                            h'))
       | None -> None)
    else None
  | "StkHTCon" ->
    if num_args == 4 then
      let p1, p2 = Locationutils.get_pair_from_prod env (to_constr sigma (arg 0)) sigma in
      let q1, q2 = Locationutils.get_pair_from_prod env (to_constr sigma (arg 1)) sigma in
      let h = to_constr sigma (arg 3) in
      (match recurse_over_constr env h sigma with
       | Some h' ->
         Some (StkHTCon ((of_constr p1, of_constr p2), (of_constr q1, of_constr q2), (arg 2), h'))
       | None -> None)
    else None
  | _ -> None


let rec make_stk_hoare_tree env sigma (s: stk_hoare_tree) =
  let open Locationutils in
  let tbl = get_constructors_hashtbl env (mkInd sht) sigma in
  let name = to_string s in
  let to_array = Array.of_list in
  let construct_sht =
    (fun args -> mkApp (Hashtbl.find tbl name, to_array args)) in
  match s with
  | StkHTSkip t ->
    Some (construct_sht [t])
  | StkHTAssign (p, i, q) ->
    Some (construct_sht [p; i; q])
  | StkHTPush (p) ->
    Some (construct_sht [p])
  | StkHTPop (p, p', q) ->
    Some (construct_sht [p;p';q])
  | StkHTSeq (p, q, r, i1, i2, h1, h2) ->
    let h1' = make_stk_hoare_tree env sigma h1 in
    let h2' = make_stk_hoare_tree env sigma h2 in
    (match h1', h2' with
     | Some h1'', Some h2'' -> Some (construct_sht [p;q;r;i1;i2;h1'';h2''])
     | _, _ -> None)
  | StkHTIf (p, q, b, i1, i2, h1, h2) ->
    let h1' = make_stk_hoare_tree env sigma h1 in
    let h2' = make_stk_hoare_tree env sigma h2 in
    (match h1', h2' with
     | Some h1'', Some h2'' -> Some (construct_sht [p; q; b; i1; i2; h1''; h2''])
     | _, _ -> None)
  | StkHTWhile (p, b, i, h) ->
    (match make_stk_hoare_tree env sigma h with
     | Some h' -> Some (construct_sht [p; b; i; h'])
     | None -> None)
  | StkHTConLeft (impl, i, q, n, h) ->
    (match make_stk_hoare_tree env sigma h, impl with
     | Some h', (p1, p2) ->
       let _, mypair = make_pair env sigma p1 p2 in
       Some (construct_sht [mypair; i; q; n; h'])
     | None, _ -> None)
  | StkHTConRight (p, i, impl, n, h) ->
    (match make_stk_hoare_tree env sigma h, impl with
     | Some h', (q1, q2) ->
       let _, mypair = make_pair env sigma q1 q2 in
       Some (construct_sht [p; i; mypair; n; h'])
     | None, _ -> None)
  | StkHTCon (impl1, impl2, i, h) ->
    (match make_stk_hoare_tree env sigma h, impl1, impl2 with
     | Some h', (p1, p2), (q1, q2) ->
       let _, mypair1 = make_pair env sigma p1 p2 in
       let _, mypair2 = make_pair env sigma q1 q2 in
       Some (construct_sht [mypair1; mypair2; i; h'])
     | _, _, _ -> 
       None)
