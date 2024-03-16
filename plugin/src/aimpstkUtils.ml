open Locationutils


(*
Lemma nth_error_facts_implies_aimpstk :
  forall (facts: implication_env_stk) (fenv: fun_env_stk) (n: nat) (P Q: AbsState),
    fact_env_valid facts fenv ->
    nth_error facts n = Some (P, Q) ->
    aimpstk P Q fenv.
*)
let nth_error_facts_valid_to_aimpstk = get_constant "Imp_LangTrick.Stack.StkHoareTree.nth_error_facts_implies_aimpstk"

let construct_nth_error_facts env sigma facts fenv p q =
  let open Termutils in
  let open CoqCoreInductives in
  let nfacts = normalize_term env facts sigma in
  let () = print_endline (Printingutils.print_kinds env nfacts sigma) in
  let facts_list = coq_list_to_list env facts sigma in
  ()
