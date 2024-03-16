open EConstr
open CheckerConstants
open Locationutils
open Termutils
open Printingutils

let typechecks env term sigma =
  try (
    let sigma, tipe = normalize_type env term sigma in
    Some (sigma, tipe))
  with Not_found -> failwith "Couldn't find term "

let option_to_bool o =
  match o with
  | Some _ -> true
  | None -> false

let is_inductive_type =
  fun ind -> let mind = mkInd ind in
    fun env sigma term ->
      let termType = typechecks env term sigma in
      Utilities.pair (fun i -> fst i) (fun k -> option_to_bool (snd k)) (Option.get (Option.bind termType (fun t -> let sigma, t' = t in Some ( sigma, is_or_applies t' mind sigma))))

let is_basic_aimpstk env sigma p1 p2 =
  let sigma, peq = equal env p1 p2 sigma in
  if peq then
    sigma, true
  else
    let absand = Hashtbl.find (absstate_tbl env sigma) "AbsAnd" in
    let basestate = Hashtbl.find (absstate_tbl env sigma) "BaseState" in
    let stktrue = Hashtbl.find (absstack_tbl env sigma) "AbsStkTrue" in
    let stksize = Hashtbl.find (absstack_tbl env sigma) "AbsStkSize" in
    let p1args = is_or_applies absand p1 sigma in
    let p2args = is_or_applies absand p2 sigma in
    match p1args, p2args with
    |  Some args1, Some args2 ->
      (match args1, args2 with
       | [a1; b1], [a2; b2] ->
         (* we have AbsAnd a1 b1, and AbsAnd a2 b2 *)
         let _, aeq = equal env a1 a2 sigma in
         if aeq then
           (let b1args = is_or_applies basestate b1 sigma in
            let b2args = is_or_applies basestate b2 sigma in
            match b1args, b2args with
            | Some argsb1, Some argsb2 ->
              (match argsb1, argsb2 with
               | [s1; m1], [s2; m2] ->
                 (* we have BaseState s1 m1 and BaseState s2 m2 *)
                 let sigma, meq = equal env m1 m2 sigma in
                 if meq then
                   let s1args = is_or_applies stktrue s1 sigma in
                   let s2args = is_or_applies stksize s2 sigma in
                   (match s1args, s2args with
                    | Some sargs1, Some [size] ->
                      (* let [size] = sargs2 in *)
                      let leq = make_app construct_n_leq_m [size; make_app maximum_stack_size_implied [a1]] in
                      let sigma, oleq = CoqCoreInductives.unwrap_option env sigma leq in
                      sigma, option_to_bool oleq
                    | _, _ -> sigma, false)
                 else sigma, false
               | _, _ -> sigma, false
               (* else false *)
              )
            | _, _ -> sigma, false)
         else
           (* let () = print_endline ("Aeq")  *)
          sigma, false
       | _, _ -> sigma, false)
    | _, _ -> sigma, false

let print_results name bools =
  print_endline (name ^ "(" ^ (String.concat " " (List.map string_of_bool bools)) ^ ")")

let rec csp env sigma fenv facts valid_facts funcs tree =
  let open Stkhoaretree in
  let open Stkvalidtree in
  let unwrap_option = CoqCoreInductives.unwrap_option env sigma in
  let is_absstate p sigma =
    is_inductive_type absstate env sigma p in
  let is_nat p sigma =
    is_inductive_type CoqCoreInductives.coq_nat env sigma p in
  (* let is_bexp b = *)
    (* is_inductive_type bexp_stack env sigma b in *)
  (* let isct = imp_stack_cons_tbl env sigma in *)
  let is_pre h p sigma = equal env p (get_pre env sigma h) sigma in
  let is_post h p sigma = equal env p (get_post env sigma h) sigma in
  let is_imp h i sigma = equal env i (get_imp env sigma h) sigma in
  let none_nat = make_app CoqCoreInductives.coq_None [(mkInd (CoqCoreInductives.coq_nat))] in
  (* let normalize_and_make_app n args = *)
    (* normalize_term env (make_app n args) sigma in *)
  match tree with
  | StkHTSkip p ->
    is_absstate p sigma
  | StkHTAssign (q, k, a) ->
     let constructed_pure = make_app construct_aexp_stack_pure_rel [fenv; a] in
    (* let () = print_endline (Printingutils.print_kinds env constructed_pure sigma) in *)
    (* if this is Some, then it's definitely preserving the stack. if not, then it could be preserving the stack...but we don't know *)
    let sigma, pure = CoqCoreInductives.unwrap_option env sigma constructed_pure in
    (* let frame = (normalize_term env (make_app frame_of_aexp [funcs; fenv; a]) sigma) in *)
    (* let () = print_endline (print_kinds env frame sigma) in *)
    let frameb = CoqCoreInductives.coq_bool_to_bool env sigma (make_app frame_of_aexp [funcs; fenv; none_nat; a]) in
    let pureb = ((option_to_bool pure) || frameb) in
    let sigma, isaq = is_absstate q sigma in
    let sigma, isnatk = is_nat k sigma in
    let sigma, isaexpstack = (is_inductive_type aexp_stack env sigma a) in
    let sigma, construct_o = unwrap_option (make_app construct_update [k; a; q]) in
    let can_construct = (option_to_bool construct_o) in
    let bools = [pureb; isaq; isnatk; isaexpstack; can_construct] in
    (* let () = print_results "StkHTAssign" bools in *)
    (sigma, List.fold_left (&&) true bools)
    (* ((option_to_bool pure) || false) && is_absstate q && is_nat k && (is_inductive_type aexp_stack env sigma a) && (option_to_bool (unwrap_option (normalize_term env (make_app construct_update [k; a; q]) sigma))) *)
  | StkHTPush p ->
    is_absstate p sigma 
  | StkHTPop (p1, p2, q) ->
    let sigma, isEq = equal env (make_app state_stack_size_inc [Option.get (CoqCoreInductives.int_to_coq_nat 1); q]) p1 sigma in
    let sigma, absp1 = is_absstate p1 sigma in
    let sigma, absp2 = is_absstate p2 sigma in
    let sigma, absq = is_absstate q sigma in
    (sigma, isEq && absp1 && absp2 && absq)
  | StkHTSeq (p, r, q, i1, i2, h1, h2) ->
    let sigma, isEq1 = is_pre h1 p sigma in
    let sigma, isEq2 = is_pre h2 r sigma in
    let sigma, isEq3 = is_post h1 r sigma in
    let sigma, isEq4 = is_post h2 q sigma in 
    let sigma, isEq5 = is_imp h1 i1 sigma in
    let sigma, isEq6 = is_imp h2 i2 sigma in
    let sigma, h1proof = (csp env sigma fenv facts valid_facts funcs h1) in
    let sigma, h2proof = (csp env sigma fenv facts valid_facts funcs h2) in
    let bools = [isEq1; isEq2; isEq3; isEq4; isEq5; isEq6; h1proof; h2proof] in
    (* let () = print_results "StkHTSeq" bools in *)
    (* let () = print_endline ("StkHTSeq(" ^ (String.concat " " (List.map (string_of_bool) bools)) ^ ")") in *)
    (sigma, isEq1 && isEq2 && isEq3 && isEq4 && isEq5 && isEq6
    && h1proof
    && h2proof)
  | StkHTIf (p, q, b, i1, i2, h1, h2) ->
    let sigma, isEq1 = is_pre h1 (make_app atruestk [b; p]) sigma in
    let sigma, isEq2 = is_post h1 q sigma in
    let sigma, isEq3 = is_pre h2 (make_app afalsestk [b; p]) sigma in
    let sigma, isEq4 = is_post h2 q sigma in
    let sigma, isEq5 = is_imp h1 i1 sigma in
    let sigma, isEq6 = is_imp h2 i2 sigma in
    let sigma, pure_b = CoqCoreInductives.unwrap_option env sigma (make_app construct_bexp_stack_pure_rel [fenv; b]) in
    let frame_b = CoqCoreInductives.coq_bool_to_bool env sigma (make_app frame_of_bexp [funcs; fenv; none_nat; b]) in
    let sigma, hproof1 = csp env sigma fenv facts valid_facts funcs h1 in
    let sigma, hproof2 = csp env sigma fenv facts valid_facts funcs h2 in
    (sigma, ((option_to_bool pure_b) || frame_b) && isEq1 && isEq2 && isEq3 && isEq4 && isEq5 && isEq6
    && hproof1
    && hproof2)
  | StkHTWhile (p, b, i', h) ->
    let sigma, isEq1 = is_pre h (make_app atruestk [b; p]) sigma in
    let sigma, isEq2 = is_post h p sigma in
    let sigma, isEq3 = is_imp h i' sigma in
    let sigma, pure_b = CoqCoreInductives.unwrap_option env sigma (make_app construct_bexp_stack_pure_rel [fenv; b]) in
    let frame_b = CoqCoreInductives.coq_bool_to_bool env sigma (make_app frame_of_bexp [funcs; fenv; none_nat; b]) in
    let sigma, hproof = (csp env sigma fenv facts valid_facts funcs h) in
    (sigma, ((option_to_bool pure_b) || frame_b) && isEq1 && isEq2 && isEq3
    && hproof)
  | StkHTConLeft (impl, i, q, n, h) ->
    let (p, p') = impl in
    let sigma, isEq1 = is_pre h p' sigma in
    let sigma, isEq2 = is_post h q sigma in
    let sigma, isEq3 = is_imp h i sigma in
    let pairtype, mypair = (make_pair env sigma p p') in
    let nth_error' = make_app nth_error [make_pair_type env sigma (mkInd absstate) (mkInd absstate); facts; n] in
    let nth_pair' = make_app CoqCoreInductives.coq_Some [pairtype;mypair] in
    let sigma, nthEq = equal env nth_error' nth_pair' sigma in
        (* (make_app nth_error [make_pair_type env sigma (mkInd absstate) (mkInd absstate); facts; n]) (make_app (CoqCoreInductives.coq_Some env sigma) [(make_pair env sigma p p')]) sigma in *)
    let sigma, hproof = (csp env sigma fenv facts valid_facts funcs h) in
    let bools = [isEq1; isEq2; isEq3; nthEq; hproof] in
    (* let () = print_results "StkHTConLeft" bools in *)
    (* let () = if not nthEq then *)
        (* (print_endline (print_kinds env nth_error' sigma); *)
         (* print_endline (print_kinds env nth_pair' sigma)) *)
        (* else () in *)
    (* let () = print_endline (String.concat " " (List.map string_of_bool bools)) in *)
    (sigma, nthEq && isEq1 && isEq2 && isEq3
    && hproof)
  | StkHTConRight (p, i, impl, n, h) ->
    let (q', q) = impl in
    let sigma, isEq1 = is_pre h p sigma in
    let sigma, isEq2 = is_post h q' sigma in
    let sigma, isEq3 = is_imp h i sigma in
    let pairtype,mypair = (make_pair env sigma q' q) in
    let sigma, nthEq = equal env (make_app nth_error [make_pair_type env sigma (mkInd absstate) (mkInd absstate); facts; n]) (make_app CoqCoreInductives.coq_Some [pairtype;mypair]) sigma in
    let sigma, hproof = (csp env sigma fenv facts valid_facts funcs h) in
    (sigma, nthEq && isEq1 && isEq2 && isEq3
    && hproof)
  | StkHTCon (impl1, impl2, i, h) ->
    let (p, p') = impl1 in
    let (q', q) = impl2 in
    let sigma, isEq1 = is_pre h p' sigma in
    let sigma, isEq2 = is_post h q' sigma in
    let sigma, isEq3 = is_imp h i sigma in
    let sigma, hproof = (csp env sigma fenv facts valid_facts funcs h) in
    let sigma, aimp1 = (is_basic_aimpstk env sigma (normalize_term env p sigma) (normalize_term env p' sigma)) in
    let sigma, aimp2 = (is_basic_aimpstk env sigma q' q) in
    (* let () = print_endline ("StkHTCon(" ^ (String.concat " " (List.map string_of_bool [isEq1; isEq2; isEq3; hproof; aimp1; aimp2])) ^ ")") in *)
    (* let () = if not aimp1 then *)
        (* (print_endline (econstr_to_string env sigma p); *)
         (* print_endline (econstr_to_string env sigma p')) *)
        (* else () in *)
    (* let () = print_message env p sigma; *)
      (* print_message env p' sigma in *)
    (sigma, isEq1 && isEq2 && isEq3
    && hproof
    && aimp1
    && aimp2)

                                                                                                
let check_stack_proof env tree fenv facts valid_facts funcs sigma =
  (* let () = print_endline "hi" in *)
  let tree = Option.get (Stkhoaretree.recurse_over_constr env (to_constr sigma (normalize_term env (of_constr (to_constr sigma (unwrap_definition env tree sigma))) sigma)) sigma) in
  let funcs_have_frame = CoqCoreInductives.coq_bool_to_bool env sigma (make_app funcs_frame [funcs; fenv]) in
  (* let () = print_endline "bye" in *)
  let () = print_endline ("Functions all have frame: " ^ (string_of_bool funcs_have_frame)) in 
  let sigma, valid = csp env sigma fenv facts valid_facts funcs tree in
  let mind_body, one_body = Global.lookup_inductive aexp_stack_frame in
  let bodies = mind_body.mind_packets in
  let bindings = Contextutils.bindings_for_inductive env mind_body bodies in
  let () = List.iter (fun i -> print_endline (Printingutils.binding_to_string env i sigma)) bindings in
  let () = print_endline (ConstructPure.construct_aexp_frame_rule env sigma) in
  let env, typenames = ConstructPure.print_bodies_typenames  env sigma in
  let () = print_endline (print_kinds env (List.nth typenames 1) sigma ) in
  let (env, _, args_tbl, bexp_tbl, _) = ConstructPure.setup env sigma in
  let () = Seq.iter print_endline (Hashtbl.to_seq_keys args_tbl) in
  let () = Seq.iter (fun i -> print_endline (print_kinds env i sigma)) (Hashtbl.to_seq_values args_tbl) in
  let () = Seq.iter print_endline (Hashtbl.to_seq_keys bexp_tbl) in
  let env, frame_tbl = MutualInductives.get_mutind_hashtbl env aexp_stack_frame in
  let () = Seq.iter print_endline (Hashtbl.to_seq_keys frame_tbl) in
  let () = Seq.iter (fun i -> print_endline (print_kinds env i sigma)) (Hashtbl.to_seq_values frame_tbl) in
  (* let () = print_endline (Printingutils.econstr_string env sigma (Hashtbl.find bexp_tbl "FrameTrue")) in *)
  (* let sigma, tipe = normalize_type env (List.nth typenames 1) sigma in *)
  (* let () = print_endline (print_kinds env tipe sigma) in *)
  (* let () = print_endline "nope" in *)
  (* let () = print_endline (Stkhoaretree.to_string_with_args_abbr ~max_level:10 tree env sigma) in *)
  (* let () = print_int (Stkhoaretree.max_depth tree) in *)
  (* let con_trees = (Stkhoaretree.collect_trees ~max:10 (fun i -> *)
      (* match i with *)
      (* | Stkhoaretree.StkHTCon _ -> true *)
      (* | _ -> false) tree) in *)
  (* let () = print_endline "hi again" in *)
  (* let print_tree = (fun tree -> Stkhoaretree.to_string_with_args_abbr_tl_rec env sigma tree) in *)
  (* let sorted_trees = List.sort (fun t1 t2 -> Stkhoaretree.max_depth t1 - Stkhoaretree.max_depth t2) con_trees in *)
  (* let () = print_endline "bye again" in *)
  (* let () = (match sorted_trees with *)
    (* | hd :: _  -> print_endline (print_tree hd) *)
  (* | _ -> ()) in *)
  let checked = (funcs_have_frame && valid) in
  let () = Feedback.msg_notice (Pp.str (string_of_bool checked)) in
  sigma, (CoqCoreInductives.inject_bool_into_coq_bool checked)
                                                                                                               
