(* Largely adapted from https://github.com/uwplse/coq-plugin-lib/blob/8.11/src/coq/representationutils/defutils.ml *)

(*
 * Utilities for defining terms
 *)

open Names
open Evd
open Constrexpr
open Constrextern

(* --- Defining Coq terms --- *)

(* https://github.com/ybertot/plugin_tutorials/blob/master/tuto1/src/simple_declare.ml 

TODO do we need to return the updated evar_map? *)
let edeclare ident poly ~opaque sigma udecl body tyopt imps hook refresh =
  let open EConstr in
  (* XXX: "Standard" term construction combinators such as `mkApp`
     don't add any universe constraints that may be needed later for
     the kernel to check that the term is correct.

     We could manually call `Evd.add_universe_constraints`
     [high-level] or `Evd.add_constraints` [low-level]; however, that
     turns out to be a bit heavyweight.

     Instead, we call type inference on the manually-built term which
     will happily infer the constraint for us, even if that's way more
     costly in term of CPU cycles.

     Beware that `type_of` will perform full type inference including
     canonical structure resolution and what not.
   *)
  let env = Global.env () in
  let sigma =
    if refresh then
      fst (Typing.type_of ~refresh:false env sigma body)
    else
      sigma
  in
  let sigma =
    if Option.has_some tyopt && refresh then
      fst (Typing.type_of ~refresh:false env sigma (Option.get tyopt))
    else
      sigma
  in
  let sigma = Evd.minimize_universes sigma in (* todo: is this necessary/bad? *)
  (* let sigma, ce = DeclareDef.prepare_definition ~allow_evars:true ~opaque ~poly sigma udecl ~types:tyopt ~body in *)
  (* let ubinders = Evd.universe_binders sigma in *)
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let info = Declare.Info.make ~scope ~kind ~udecl ~poly () in
  let cinfo = Declare.CInfo.make ~name:ident ~typ:tyopt () in
  Declare.declare_definition ~info ~cinfo ~opaque ~body sigma
    (* ~name:ident ~opaque ~scope ~kind ?hook_data:hook ubinders ce imps *)

(* Equivalent-ish of Termutils.define  *)
let define ?typ name sigma (body: EConstr.types) (refresh: bool) =
  let poly = Attributes.is_universe_polymorphism () in
  let udecl = UState.default_univ_decl in
  let etyp = Option.map EConstr.of_constr typ in
  edeclare name poly ~opaque:false sigma udecl body etyp [] None refresh
                


(* Define a new Coq term *)
let define_term ?typ (n : Id.t) (evm : evar_map) (trm : Constr.types) (refresh : bool) =
  (* let k = (Global, Flags.is_universe_polymorphism(), Definition) in *)
  let poly = Attributes.is_universe_polymorphism() in
  let udecl = UState.default_univ_decl in
  (* let nohook = DeclareDef.Hook.make (fun x -> x) in *)
  let etrm = EConstr.of_constr trm in
  let etyp = Option.map EConstr.of_constr typ in
  edeclare n poly ~opaque:false evm udecl etrm etyp [] None refresh

(* Define a Canonical Structure *)
let define_canonical ?typ (n : Id.t) (evm : evar_map) (trm : Constr.types) (refresh : bool) =
  (* let k = (Global, Flags.is_universe_polymorphism(), Definition) in *)
  let poly = Attributes.is_universe_polymorphism() in
  let udecl = UState.default_univ_decl in
  let hook = Declare.Hook.make (fun x -> let open Declare.Hook.S in Canonical.declare_canonical_structure x.dref) in
  let etrm = EConstr.of_constr trm in
  let etyp = Option.map EConstr.of_constr typ in
  edeclare n poly ~opaque:false evm udecl etrm etyp [] (Some (hook, Evd.evar_universe_context evm, [])) refresh (* todo: check if last empty list is correct to pass *)

(* --- Converting between representations --- *)

(*
 * See defutils.mli for explanations of these representations.
 *)

(* Intern a term (for now, ignore the resulting evar_map) *)
let intern env sigma t : evar_map * Constr.types =
  let (sigma, trm) = Constrintern.interp_constr_evars env sigma t in
  sigma, EConstr.to_constr sigma trm

(* Extern a term *)
let extern env sigma t : constr_expr =
  Constrextern.extern_constr ~inctx:true env sigma (EConstr.of_constr t)

(* Construct the external expression for a definition *)
let expr_of_global (g : Names.GlobRef.t) : constr_expr =
  let r = extern_reference Id.Set.empty g in
  CAst.make @@ (CAppExpl ((r, None), []))

(* Convert a term into a global reference with universes (or raise Not_found) *)
let pglobal_of_constr term =
  let open Constr in 
    match Constr.kind term with
    | Const (const, univs) -> Names.GlobRef.ConstRef const, univs
    | Ind (ind, univs) ->  Names.GlobRef.IndRef ind, univs
    | Construct (cons, univs) -> Names.GlobRef.ConstructRef cons, univs
    | Var id -> Names.GlobRef.VarRef id, Univ.Instance.empty
    | _ -> raise Not_found

(* Convert a global reference with universes into a term *)
let constr_of_pglobal (glob, univs) =
  match glob with
  | Names.GlobRef.ConstRef const -> Constr.mkConstU (const, univs)
  | Names.GlobRef.IndRef ind -> Constr.mkIndU (ind, univs)
  | Names.GlobRef.ConstructRef cons -> Constr.mkConstructU (cons, univs)
  | Names.GlobRef.VarRef id -> Constr.mkVar id
