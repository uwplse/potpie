open Termutils
open Locationutils
open CheckerConstants

let add_mutual_inductive_defs_to_env env (i: Names.inductive) =
  let mind_body, one_body = Global.lookup_inductive i in
  let bodies = mind_body.mind_packets in
  let bindings = Contextutils.bindings_for_inductive env mind_body bodies in
  (List.fold_left (fun acc elmt -> Environ.push_rel elmt acc) env bindings,
   bindings,
   mind_body,
   Array.to_list bodies,
   mind_body.mind_ntypes)

let get_mutind_names mind_body =
  let open Declarations in
  List.map (fun b -> b.mind_typename) (Array.to_list mind_body.mind_packets)

let get_mutind_name_strings mind_body =
  List.map (Names.Id.to_string) (get_mutind_names mind_body)
                       

let get_mutind_hashtbl env (i: Names.inductive) =
  let env, bindings, mind_body, bodies, numtypes = add_mutual_inductive_defs_to_env env i in
  let inductives = List.map (fun k -> EConstr.mkInd (Names.ith_mutual_inductive i k)) (Collections.range 0 numtypes) in
  let names = get_mutind_name_strings mind_body in
  (env, Hashtbl.of_seq (List.to_seq (List.combine names inductives)))
