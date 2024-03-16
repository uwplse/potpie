open Evd

(* --- State monad --- *)

(*
 * All terms in Coq have to carry around evar_maps (found in the Evd module),
 * which store a bunch of constraints about terms that help with things like
 * unification, type inference, and equality checking. This is annoying to
 * deal with, so I usually define some helper functions to make it easier.
 *
 * These come from https://github.com/uwplse/coq-plugin-lib in stateutils.mli,
 * and the idea to use this design pattern comes from my grad school advisor
 * Dan Grossman.
 *
 * For any type 'a, a 'a state is a tuple of an evar_map and a 'a.
 * So basically, a 'a that carries around an evar_map.
 *)
type 'a state = evar_map * 'a

(*
 * These are monadic return and bind. Basically, they let you kind of pretend
 * you're not in the state monad (that is, pretend you're not carrying around
 * an evar_map with you everywhere). If you've ever used Haskell, it's common
 * to have syntax that makes this kind of thing look even nicer.
 *
 * Bind lets you chain calls with state:
 *)
val bind :
  (evar_map -> 'a state) -> (* f1 *)
  ('a -> evar_map -> 'b state) -> (* f2 *)
  evar_map -> (* state *)
  'b state (* stateful f1; f2 *)

(* Ret lets you forget the state in the final call: *)
val ret :
  'a -> (* a *)
  evar_map -> (* state *)
  'a state (* stateful a *)

(* --- Threading state through arguments --- *)

(*
 * Stateful HOFs
 *)
val fold_left_state :
  ('b -> 'a -> evar_map -> 'b state) ->
  'b ->
  'a list ->
  evar_map ->
  'b state

val fold_left2_state :
  ('c -> 'a -> 'b -> evar_map -> 'c state) ->
  'c ->
  'a list ->
  'b list ->
  evar_map ->
  'c state

val fold_right_state :
  ('a -> 'b -> evar_map -> 'b state) ->
  'a list ->
  'b ->
  evar_map ->
  'b state

val fold_right2_state :
  ('a -> 'b -> 'c -> evar_map -> 'c state) ->
  'a list ->
  'b list ->
  'c ->
  evar_map ->
  'c state

val map_tuple_state:
  ('a -> evar_map -> 'b state) ->
  ('a * 'a) ->
  evar_map ->
  ('b * 'b) state

val fold_tuple_state:
  ('a -> 'b -> evar_map -> 'c state) ->
  ('a * 'b) ->
  evar_map ->
  'c state
                               
val map_state :
  ('a -> evar_map -> 'b state) ->
  'a list ->
  evar_map ->
  ('b list) state

val map2_state :
  ('a -> 'b -> evar_map -> 'c state) ->
  'a list ->
  'b list ->
  evar_map ->
  ('c list) state

val map_state_array :
  ('a -> evar_map -> 'b state) ->
  'a array ->
  evar_map ->
  ('b array) state

val flatten_state :
  'a list list ->
  evar_map ->
  'a list state

val flat_map_state :
  ('a -> evar_map -> ('b list) state) ->
  'a list ->
  evar_map ->
  ('b list) state

val branch_state :
  ('a -> evar_map -> bool state) -> (* predicate *)
  ('a -> evar_map -> 'b state) -> (* run if true *)
  ('a -> evar_map -> 'b state) -> (* run if false *)
  'a ->
  evar_map ->
  'b state

val and_state :
  ('a -> evar_map -> bool state) -> (* first predicate *)
  ('b -> evar_map -> bool state) -> (* second predicate *)
  'a -> (* first argument *)
  'b -> (* second argument *)
  evar_map ->
  bool state

val or_state :
  ('a -> evar_map -> bool state) -> (* first predicate *)
  ('b -> evar_map -> bool state) -> (* second predicate *)
  'a -> (* first argument *)
  'b -> (* second argument *)
  evar_map ->
  bool state

val and_state_fold :
  ('a -> evar_map -> bool state) -> (* first predicate *)
  ('a -> evar_map -> bool state) -> (* second predicate *)
  'a ->
  evar_map ->
  bool state

val or_state_fold :
  ('a -> evar_map -> bool state) -> (* first predicate *)
  ('a -> evar_map -> bool state) -> (* second predicate *)
  'a ->
  evar_map ->
  bool state

val not_state :
  ('a -> evar_map -> bool state) ->
  'a ->
  evar_map ->
  bool state
            
val exists_state :
  ('a -> evar_map -> bool state) ->
  'a list ->
  evar_map ->
  bool state

val exists2_state :
  ('a -> 'b -> evar_map -> bool state) ->
  'a list ->
  'b list ->
  evar_map ->
  bool state

val forall_state :
  ('a -> evar_map -> bool state) ->
  'a list ->
  evar_map ->
  bool state

val forall2_state :
  ('a -> 'b -> evar_map -> bool state) ->
  'a list ->
  'b list ->
  evar_map ->
  bool state

val find_state :
  ('a -> evar_map -> bool state) ->
  'a list ->
  evar_map ->
  'a state

val find2_state :
  ('a -> 'b -> evar_map -> bool state) ->
  'a list ->
  'b list ->
  evar_map ->
  ('a * 'b) state

val filter_state :
  ('a -> evar_map -> bool state) ->
  'a list ->
  evar_map ->
  ('a list) state

val filter2_state :
  ('a -> 'b -> evar_map -> bool state) ->
  'a list ->
  'b list ->
  evar_map ->
  (('a * 'b) list) state

val partition_state :
  ('a -> evar_map -> bool state) ->
  'a list ->
  evar_map ->
  ('a list * 'a list) state
