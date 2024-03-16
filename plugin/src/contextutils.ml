open Constr
open Declarations
module CRD = Context.Rel.Declaration
               
(* from https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/logicutils/typesandequality/inference.ml *)
(* Get the type of an inductive type (TODO do we need evar_map here?) *)
let type_of_inductive env index mutind_body : types =
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = Array.get ind_bodies index in
  let univs = Declareops.inductive_polymorphic_context mutind_body in
  let univ_instance = Univ.make_abstract_instance univs in
  let mutind_spec = (mutind_body, ind_body) in
  Inductive.type_of_inductive (mutind_spec, univ_instance)

(* these bindings functions are from https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/logicutils/contexts/contextutils.ml *)
(*
 * Inductive types
 *)
let bindings_for_inductive env mutind_body ind_bodies : rel_declaration list =
  Array.to_list
    (Array.mapi
       (fun i ind_body ->
         let name_id = ind_body.mind_typename in
         let typ = type_of_inductive env i mutind_body in
         CRD.LocalAssum (Context.nameR name_id, typ))
       ind_bodies)

(*
 * Fixpoints
 *)
let bindings_for_fix (names : Names.Name.t Context.binder_annot array) (typs : types array) : rel_declaration list =
  (* let open engine.Vars in *)
  Array.to_list
    (CArray.map2_i
       (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ))
       names (typs))

