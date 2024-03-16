open Termutils
open CheckerConstants
open EConstr
open Names
open Locationutils
open Pp
open Printingutils

let imp_langtrick_stack_stkhoaretree =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["StkHoareTree"; "Stack"; "Imp_LangTrick"]))

let lookup_constant c = Nametab.locate_constant (Libnames.qualid_of_string c)

let get_app_name env t sigma =
  let constr_t = to_constr sigma (unwrap_definition env t sigma) in
  match Constr.kind constr_t with
  | Constr.App (name, args) ->
    Some (name, args)
  | _ -> None


let unwrap_to_definition env t sigma =
  to_constr sigma (unwrap_definition env t sigma)


let interpret_tree env t sigma =
  let constr_t = to_constr sigma (unwrap_definition env t sigma) in
  let names, num_constructors = get_names_num_constructors env (mkInd sht) sigma in
  let names_strings = List.map Names.Id.to_string (Array.to_list names) in
  let () = List.iter (fun n -> print_endline n) names_strings in
  let constructors = List.map (fun i -> ith_constructor_of_inductive sht i) (Collections.range 1 (num_constructors + 1)) in
  let () = print_warn (Constr.debug_print constr_t) in
  match get_app_name env t sigma with
  | Some (name, args) ->
    let () = debug_print (Constr.debug_print name) in
    let ename = of_constr name in
    let equal_constructors =
      List.filter_map
        (fun i ->
           let _, is_eq = equal env ename (mkConstruct (fst i)) sigma in
           if is_eq then Some i
           else None
        )
        (List.map2 (fun a b -> (a, b)) constructors names_strings) in
    (match equal_constructors with
    | [] -> failwith "Couldn't find a constructor to match it"
    | hd :: _ ->
      let constr_name = snd hd in
      let open Stkhoaretree in
      let len_args = Array.length args in
      let () = print_endline "Name" in
      let () = print_endline constr_name in
      if String.equal constr_name "StkHTSkip" then
        if len_args == 1 then
          Some (StkHTSkip (of_constr (Array.get args 0)))
        else None
      else None)
  | _ -> None

let try_normalize_term env t sigma ignore_opaques =
  try
    if ignore_opaques then
      normalize_ignore_opaques env t sigma
    else
      normalize_term env t sigma
  with e -> failwith ("Failed  to normalize " ^ (Printingutils.econstr_string env sigma t))


let try_print env p sigma k =
  try (print_message env p sigma)
  with Not_found -> failwith ("not found exception " ^ k)

let time_op ?(name="operation") thnk =
  let start = Unix.gettimeofday () in
  let ret = thnk () in
  let time_end = Unix.gettimeofday () in
  let () = print_endline ("Time to complete " ^ name ^ ": " ^ (string_of_float (time_end -. start))) in
  ret

let rec csp env sigma tree fenv facts valid_facts =
  let open Stkhoaretree in
  let open Stkvalidtree in
  let _eq_refl = CoqCoreInductives.coq_eq_refl in
  let eq_refl = (fun a ->
      let sigma, tipe = Typing.type_of ~refresh:true env sigma a in
      mkApp (_eq_refl, Array.of_list [tipe; a])) in
  let isct = imp_stack_cons_tbl env sigma in
  match tree with
  | StkHTSkip p ->
    let i: inputs = { p=p;
                      i=Hashtbl.find isct "Skip_Stk";
                      q=p;
                      fenv=fenv;
                      fact_env=facts } in
    let eq_refl_p = eq_refl p in
    Some (StkValidHTSkip (i, eq_refl_p,
            (eq_refl i.i), valid_facts))
  | StkHTAssign (q, k, a) ->
    let p = make_app coq_state_update [k; a; q] in
    let imp = make_app (Hashtbl.find isct "Assign_Stk") [k; a] in
    let i = { p = p;
              i = imp;
              q = q;
              fenv = fenv;
              fact_env = facts } in
    let constructed_update = make_app construct_update [k; a; q] in
    let sigma, update = CoqCoreInductives.unwrap_option env sigma constructed_update in
    let start = Unix.gettimeofday () in
    let constructed_pure = make_app construct_aexp_stack_pure_rel [fenv; a] in
    let time_end = Unix.gettimeofday () in
    let () = print_endline ("Time to complete normalizing construct aexp pure: " ^ (string_of_float (time_end -. start))) in
    let sigma, pure = CoqCoreInductives.unwrap_option env sigma constructed_pure in
    let () = print_endline (match update, pure with
        | Some _, Some _ -> "assign update, pure succeeded"
        | Some _, None -> "assign update failed"
        | None, Some _ -> "assign pure failed"
        | None, None -> "assign update, pure failed") in
    (match update, pure with
     |  Some args, Some args' ->
       if Array.length args == 2 && Array.length args' == 2 then
         Some (
           StkValidHTAssign (i, k, a,
                             (Array.get args 1),
                               (eq_refl i.i),
                             valid_facts,
                             (Array.get args' 1)))
       else
         let () = print_endline ("Array length of args failed: " ^ (string_of_int (Array.length args)) ^ " " ^ (string_of_int (Array.length args'))) in
         None
     | _, _ ->
       None)
  | StkHTPush p ->
    let o, s, succ = CoqCoreInductives.coq_nat_constructors in
    let q = make_app state_stack_size_inc [(succ o); p] in
    let sigma, construct_size_inc = CoqCoreInductives.unwrap_option env sigma (make_app construct_state_stk_size_inc [(succ o); p]) in
    let i: inputs = { p = p;
                     i = (make_app (Hashtbl.find isct "Push_Stk") []);
                     q = q;
                     fenv = fenv;
                     fact_env = facts } in
    (match construct_size_inc with
     | Some args ->
       Some (StkValidHTPush (i,
                             Array.get args 1,
                             (eq_refl i.i),
                             valid_facts))
     | _ ->
       let () = print_endline "push construct size inc failed" in
       None)
  | StkHTPop (p1, p2, q) ->
    let o, s, succ = CoqCoreInductives.coq_nat_constructors in
    let p = make_app (Hashtbl.find (absstate_tbl env sigma) "AbsAnd") [p1; p2] in
    let sigma, construct_size_inc = CoqCoreInductives.unwrap_option env sigma (make_app construct_state_stk_size_inc [(succ o); q]) in
    let i: inputs = { p = p;
                      i = (make_app (Hashtbl.find isct "Pop_Stk") []);
                      q = q;
                      fenv = fenv;
                      fact_env = facts } in
    (match construct_size_inc with
     | Some args ->
       Some (StkValidHTPop (i,
                            p1,
                            p2,
                            (eq_refl p),
                            (Array.get args 1),
                            (eq_refl i.i),
                            valid_facts))
     | _ ->
       let () = print_endline "Failed at pop" in
       None)
   | StkHTSeq (p, r, q, i1, i2, h1, h2) -> 
     let v1 = (csp env sigma h1 fenv facts valid_facts) in
     let v2 = (csp env sigma h2 fenv facts valid_facts) in
     let i: inputs = { p=p;
                       i=(make_app (Hashtbl.find isct "Seq_Stk")
                         [i1; i2]);
                       q=q;
                       fenv=fenv;
                       fact_env=facts } in
     (match v1, v2 with
      | Some v1', Some v2' ->
        Some (StkValidHTSeq (i, r, h1, h2, i1, i2,
                             (eq_refl i.i),
                             valid_facts,
                             v1', v2'))
      | _, _ ->
        let () = print_endline "Failed at seq" in
        None)
   | StkHTIf (p, q, b, i1, i2, h1, h2) ->
     let v1 = (csp env sigma h1 fenv facts valid_facts) in
     let v2 = (csp env sigma h2 fenv facts valid_facts) in
     let sigma, pure_b = time_op ~name:"if pure b" (fun () -> CoqCoreInductives.unwrap_option env sigma (make_app construct_bexp_stack_pure_rel [fenv; b])) in
     let i: inputs = { p=p;
                       i=(make_app (Hashtbl.find isct "If_Stk")
                         [b; i1; i2]);
                       q=q;
                       fenv=fenv;
                       fact_env=facts } in
     (match v1, v2, pure_b with
      | Some v1', Some v2', Some args ->
        if Array.length args == 2 then
          Some (StkValidHTIf (i, b, i1, i2, h1, h2,
                              (eq_refl i.i),
                              valid_facts,
                              Array.get args 1,
                              v1', v2'))
        else None
      | _, _, _ ->
        let () = print_endline "Failed at if" in
        None)
   | StkHTWhile (p, b, i', h) -> 
     let v = (csp env sigma h fenv facts valid_facts) in
     let i: inputs = { p=p;
                       i=(make_app (Hashtbl.find isct "While_Stk")
                            [b; i']);
                       q=make_app afalsestk [b; p];
                       fenv=fenv;
                       fact_env=facts } in
     let sigma, pure_b = time_op ~name:"while pure b" (fun () -> CoqCoreInductives.unwrap_option env sigma (make_app construct_bexp_stack_pure_rel [fenv; b])) in
     (match v, pure_b with
      | Some v', Some args ->
        if Array.length args == 2 then
          Some (StkValidHTWhile (i, b, i', h, (eq_refl i.i),
                           eq_refl i.q,
                           valid_facts,
                           Array.get args 1,
                                 v'))
        else None
      | None, Some args ->
        let () = print_endline "Proving while body failed!";
          print_endline (to_string_with_args_abbr ~max_level:1 h env sigma) in
        None
      | Some _, None ->
        let () = print_endline "Proving pure b failed!";
          print_endline (econstr_to_string env sigma b) in
        None
      | _, _ -> None)
   | StkHTCon (impl1, impl2, i', h) ->
     (match impl1, impl2 with
      | (p, p'), (q', q) ->
        let aimp1 = Aimpstk.prove_aimpstk env p p' fenv sigma in
        let aimp2 = Aimpstk.prove_aimpstk env q' q fenv sigma in
        let v = csp env sigma h fenv facts valid_facts in
        let pairtypeP, mypairP = make_pair env sigma p p' in
        let pairtypeQ, mypairQ = make_pair env sigma q' q in
        let i: inputs = {p = p;
                         i = i';
                         q = q;
                         fenv = fenv;
                         fact_env=facts;}
        in
        let () = print_endline "Trying to prove StkHTCon" in
        (match aimp1, aimp2, v with
         | Some aimp1', Some aimp2', Some v' ->
           let () = print_endline "All are some" in 
           Some (StkValidHTCon (i, impl1, impl2, h, p', q',
                                (eq_refl mypairP),
                                (eq_refl mypairQ),
                                aimp1',
                                aimp2',
                                v'))
         | None, None, Some _ ->
           let () = print_endline "aimpstk both failed!";
             print_endline (econstr_to_string env sigma mypairP);
             print_endline (econstr_to_string env sigma mypairQ) in
           None
         | Some _, None, Some _ ->
           let () = print_endline "aimpstk right failed!";

             print_endline (econstr_to_string env sigma mypairQ) in
           None
         | None, Some _, Some _ ->
           let () = print_endline "aimpstk left failed!";
             print_endline (econstr_to_string env sigma mypairP) in
           None
         | None, None, None ->
           let () = print_endline "Proving everything failed!";
             print_endline (econstr_to_string env sigma mypairP);
             print_endline (econstr_to_string env sigma mypairQ);
             print_endline (to_string_with_args_abbr ~max_level:1 h env sigma) in
           None
         | _, _, None ->
           let () = print_endline "proving hoare tree valid failed!";
             print_endline (econstr_to_string env sigma p');
             print_endline (econstr_to_string env sigma i');
             print_endline (econstr_to_string env sigma q') in
           
           None
           
         | _, _, _ ->
           let () = print_endline "All failed" in
           None)
     )
   | StkHTConLeft (impl, i', q, n, h) -> 
     (match impl with
      | (p, p') ->
        let i : inputs = {p = p;
                          i = i';
                          q = q;
                          fenv = fenv;
                          fact_env = facts;
                         } in
        let pairtype, mypair = make_pair env sigma p p' in
        let nth_error' = make_app nth_error [make_pair_type env sigma (mkInd absstate) (mkInd absstate); facts; n] in
        let nth_pair' = make_app CoqCoreInductives.coq_Some [pairtype;mypair] in
        let sigma, nthEq = equal env nth_error' nth_pair' sigma in
        let nth_error_proof = if nthEq then
            try Some (eq_refl nth_error')
            with Not_found ->
              let () = print_endline ("not found while evaluating " ^ (econstr_to_string env sigma (eq_refl nth_error'))) in
              None
          else
            None in
        let aimp = (match Option.map (fun nth -> make_app fact_env_valid_means_aimpstk [p; p'; n; facts; fenv; nth; valid_facts]) nth_error_proof with
            | Some a ->
              (try Some a
               with e ->
                 let () = print_endline "Error occurred while trying to create aimpstk" in
                 None)
            | None -> None) in
        let () = print_endline "trying to check StkHTConLeft" in
        (* (construct nth_error fact_env n = Some impl) in *)
        let v = (csp env sigma h fenv facts valid_facts) in
        let () = print_endline (match v, nth_error_proof, aimp with
            | Some _, Some _, Some _-> "valid and nth error and aimp proofs succeeded for stkhtconleft"
            |  Some _, None, Some _ -> "valid hoare tree failed in stkhtconleft"
            | None, Some _, Some _ -> "nth error proof failed in stkhtconleft"
            | None, None, Some _ -> "valid and nth error proof failed in stkhtconleft"
            | Some _, Some _, None -> "aimp proof failed in stkhtconleft"
            | Some _, None, None -> "nth error and aimp failed for stkhtconleft"
            | None, Some _, None -> "valid and aimp failed in stkhtconleft"
            | None, None, None -> "valid, nth error, aimp failed in stkhtconleft"
          ) in
        (match aimp with
        | Some aimp' ->
          Option.bind
            v
            (fun v' ->
               Option.map
                 (fun nth_error_proof ->
                    StkValidHTConLeft
                      (i, impl, p', h, n,
                       (eq_refl mypair),
                       valid_facts,
                       aimp',
                       nth_error_proof,
                       v')
                 )
                 nth_error_proof
            )
        | None -> None)
   )
   | StkHTConRight (p, i', impl, n, h) ->
     (match impl with
      | (q', q) ->
        let i : inputs = {p = p;
                          i = i';
                          q = q;
                          fenv = fenv;
                          fact_env = facts;
                         } in
        let pairtype, mypair = make_pair env sigma q' q in
        let nth_error' = make_app nth_error [make_pair_type env sigma (mkInd absstate) (mkInd absstate); facts; n] in
        let nth_pair' = make_app CoqCoreInductives.coq_Some [pairtype;mypair] in
        let sigma, nthEq = equal env nth_error' nth_pair' sigma in
        let nth_error_proof = if nthEq then
            try Some (eq_refl nth_error')
            with Not_found ->
              let () = print_endline ("not found while evaluating " ^ (econstr_to_string env sigma (eq_refl nth_error'))) in
              None
          else
            None in
        let aimp =
          (match Option.map (fun nth -> make_app fact_env_valid_means_aimpstk [q'; q; n; facts; fenv; nth; valid_facts]) nth_error_proof with
           | Some a ->
             (try Some a
              with e ->
                let () = print_endline "Error while trying to normalize aimpstk in stkhtconright" in
                None)
           | None -> None)
         in
        let () = print_endline "Trying to evaluate StkHTConRight" in
        let v = (csp env sigma h fenv facts valid_facts) in
        let () = print_endline (match v, nth_error_proof, aimp with
            | Some _, Some _, Some _ -> "valid, nth error proofs, aimp succeeded for stkhtconright"
            |  Some _, None, Some _ -> "valid hoare tree failed in stkhtconright"
            | None, Some _, Some _ -> "nth error proof failed in stkhtconright"
            | None, None, Some _ -> "valid and nth error proof failed in stkhtconright"
            | Some _, Some _, None  -> "aimp failed for stkhtconright"
            | None, Some _, None -> "valid and aimp failde for stkhtconright"
            | Some _, None, None -> "nth_error and aimp failed for stkhtconright"
            | None, None, None -> "all failed for stkhtconright"
            (* | _, _, _ -> "Something else" *)
          ) in
        (match aimp with
         | Some aimp' ->
           Option.bind
             v
             (fun v' ->
                (Option.map
                   (fun nth_error_proof ->
                      StkValidHTConRight
                        (i, impl, q', h, n,
                         (eq_refl mypair),
                         valid_facts,
                         aimp',
                         nth_error_proof,
                         v'))
                   nth_error_proof)
             )
         | None -> None)
     )

(*
 * Check a stack Hoare logic proof tree
 *)
let check_stack_proof env p fenv facts valid_facts sigma =
  (* let c = lookup_constant "Coq.Init.Logic.eq" in *)
  let () = print_endline "1" in
  (* let () = print_endline "2" in *)
  let tree = Option.get (Stkhoaretree.recurse_over_constr env (to_constr sigma (try_normalize_term env (of_constr (unwrap_to_definition env p sigma)) sigma false)) sigma) in
  (* let () = print_endline "3" in *)
  let validity_tree = csp env sigma tree fenv facts valid_facts in
  (* let () = print_endline "4" in *)
  (* let () = print_endline (Stkhoaretree.to_string_with_args tree env sigma) in *)
  (* let () = print_endline "5" in *)
  (* let () = print_message env p sigma in *)
  (* let _ = econstr_debug_print env skip in *)
  (* if List.length constructor > 1 then *)
  let valid_tree_econstr = Option.bind validity_tree (Stkvalidtree.make_stk_valid_tree env sigma) in
  let () = print_endline (match valid_tree_econstr with
      | Some v -> "valid tree succeeded"
      | None -> "valid tree failed") in
  sigma, valid_tree_econstr
  (* Option.bind validity_tree (Stkvalidtree.make_stk_valid_tree env sigma)  *)
  (*match (Option.bind validity_tree (Stkvalidtree.make_stk_valid_tree env sigma)) (*None*) with
   | Some t ->
     (* let () = (try ( *)
       (* let () = print_endline "6" in *)
     (*   print_message env (make_constant "Imp_LangTrick.Stack.StackLogic.afalsestk") sigma *)
     (* ) with Not_found -> failwith "not found exception") in *)
     (* let () = (try econstr_debug_print env t *)
     (*           with Not_found -> failwith "not found exception 2") in *)
     (* let () = (try print_message env t sigma *)
     (*           with Not_found -> failwith "not found exception 1") in *)
     (*   let () = print_warn (print env (CoqCoreInductives.coq_eq_refl env sigma) sigma) in *)
     (* (sigma, CoqCoreInductives.coq_eq_refl env sigma) *)
     (sigma, Termutils.normalize_term env t sigma)
   | None ->
     (* let () = print_endline "7" in *)
     (sigma, (make_constant "Imp_LangTrick.Stack.StackLogic.afalsestk"))*)
(* (sigma, CoqCoreInductives.inject_bool_into_coq_bool env sigma true) *)
    (* (sigma, ((List.hd (List.tl (constructor))))) *)
  (* else *)
  (*   (\* let () = print_endline "8" in *\) *)
  (*   (sigma, skip) *)
  (* sigma,  *)
    (* (mkInd ((MutInd.make1 (Constant.canonical c)), 0)) (\* TODO code goes here *\) *)

(* I'm assuming p is the tree????? *)
(* Hopefully we also give it fact_env_valid, i'm going to assume that (fact_env_valid fact_env fenv) = valid_facts *)
(*
   
   
*)


(*
Inductive
stk_valid_tree (P : AbsState) (i : imp_stack) (Q : AbsState)
(fenv : fun_env_stk) (fact_env : implication_env_stk)
  : stk_hoare_tree -> Type :=
    StkValidHTSkip : P = Q ->
                     i = Skip_Stk ->
                     fact_env_valid fact_env fenv ->
                     stk_valid_tree P i Q fenv fact_env (StkHTSkip P)
  | StkValidHTAssign : forall (k : stack_index) (a : aexp_stack),
                       state_update_rel k a Q P ->
                       i = Assign_Stk k a ->
                       fact_env_valid fact_env fenv ->
                       StackPurestBase.aexp_stack_pure_rel a fenv ->
                       stk_valid_tree P i Q fenv fact_env
                         (StkHTAssign Q k a)
  | StkValidHTPush : state_stk_size_inc 1 P Q ->
                     i = Push_Stk ->
                     fact_env_valid fact_env fenv ->
                     stk_valid_tree P i Q fenv fact_env (StkHTPush P)
  | StkValidHTPop : forall P1 P2 : AbsState,
                    P = AbsAnd P1 P2 ->
                    state_stk_size_inc 1 Q P1 ->
                    i = Pop_Stk ->
                    fact_env_valid fact_env fenv ->
                    stk_valid_tree P i Q fenv fact_env
                      (StkHTPop P1 P2 Q)
  | StkValidHTSeq : forall (R : AbsState) (H1 H2 : stk_hoare_tree)
                      (i1 i2 : imp_stack),
                    i = Seq_Stk i1 i2 ->
                    fact_env_valid fact_env fenv ->
                    stk_valid_tree P i1 R fenv fact_env H1 ->
                    stk_valid_tree R i2 Q fenv fact_env H2 ->
                    stk_valid_tree P i Q fenv fact_env
                      (StkHTSeq P R Q i1 i2 H1 H2)
  | StkValidHTIf : forall (b : bexp_stack) (i1 i2 : imp_stack)
                     (H1 H2 : stk_hoare_tree),
                   i = If_Stk b i1 i2 ->
                   fact_env_valid fact_env fenv ->
                   StackPurestBase.bexp_stack_pure_rel b fenv ->
                   stk_valid_tree (atruestk b P) i1 Q fenv fact_env H1 ->
                   stk_valid_tree (afalsestk b P) i2 Q fenv fact_env H2 ->
                   stk_valid_tree P i Q fenv fact_env
                     (StkHTIf P Q b i1 i2 H1 H2)
  | StkValidHTWhile : forall (b : bexp_stack) (i' : imp_stack)
                        (H : stk_hoare_tree),
                      i = While_Stk b i' ->
                      Q = afalsestk b P ->
                      fact_env_valid fact_env fenv ->
                      StackPurestBase.bexp_stack_pure_rel b fenv ->
                      stk_valid_tree (atruestk b P) i' P fenv fact_env
                        H ->
                      stk_valid_tree P i Q fenv fact_env
                        (StkHTWhile P b i' H)
  | StkValidHTCon : forall (Impl1 Impl2 : AbsState * AbsState)
                      (H : stk_hoare_tree) (P' Q' : AbsState),
                    Impl1 = (P, P') ->
                    Impl2 = (Q', Q) ->
                    (P --->>> P') fenv ->
                    (Q' --->>> Q) fenv ->
                    stk_valid_tree P' i Q' fenv fact_env H ->
                    stk_valid_tree P i Q fenv fact_env
                      (StkHTCon Impl1 Impl2 i H)
  | StkValidHTConLeft : forall (Impl : AbsState * AbsState)
                          (P' : AbsState) (H : stk_hoare_tree)
                          (n : nat),
                        Impl = (P, P') ->
                        fact_env_valid fact_env fenv ->
                        (P --->>> P') fenv ->
                        nth_error fact_env n = Some Impl ->
                        stk_valid_tree P' i Q fenv fact_env H ->
                        stk_valid_tree P i Q fenv fact_env
                          (StkHTConLeft Impl i Q n H)
  | StkValidHTConRight : forall (Impl : AbsState * AbsState)
                           (Q' : AbsState) (H : stk_hoare_tree)
                           (n : nat),
                         Impl = (Q', Q) ->
                         fact_env_valid fact_env fenv ->
                         (Q' --->>> Q) fenv ->
                         nth_error fact_env n = Some Impl ->
                         stk_valid_tree P i Q' fenv fact_env H ->
                         stk_valid_tree P i Q fenv fact_env
                           (StkHTConRight P i Impl n H).

Arguments stk_valid_tree P i Q fenv fact_env _
Arguments StkValidHTSkip P i Q fenv fact_env _ _ _
Arguments StkValidHTAssign P i Q fenv fact_env 
  k a%stack_arith_scope _ _ _ _
Arguments StkValidHTPush P i Q fenv fact_env _ _ _
Arguments StkValidHTPop P i Q fenv fact_env P1 P2 _ _ _ _
Arguments StkValidHTSeq P i Q fenv fact_env R H1 H2 i1 i2 _ _ _ _
Arguments StkValidHTIf P i Q fenv fact_env b%stack_bool_scope 
  i1 i2 H1 H2 _ _ _ _ _
Arguments StkValidHTWhile P i Q fenv fact_env b%stack_bool_scope 
  i' H _ _ _ _ _
Arguments StkValidHTCon P i Q fenv fact_env Impl1 
  Impl2 H P' Q' _ _ _ _ _
Arguments StkValidHTConLeft P i Q fenv fact_env 
  Impl P' H n%nat_scope _ _ _ _ _
Arguments StkValidHTConRight P i Q fenv fact_env 
  Impl Q' H n%nat_scope _ _ _ _ _
                         *)
