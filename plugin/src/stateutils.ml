open Evd
open Utilities

(* --- State monad --- *)

(*
 * All terms in Coq have to carry around evar_maps (found in the Evd module),
 * which store a bunch of constraints about terms that help with things like
 * unification, type inference, and equality checking. This is annoying to
 * deal with, so I usually define some helper functions to make it easier.
 *
 * These come from https://github.com/uwplse/coq-plugin-lib in stateutils.ml,
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
 *)
let ret a = fun sigma -> sigma, a
let bind f1 f2 = (fun sigma -> let sigma, a = f1 sigma in f2 a sigma)

(* --- Threading state through arguments --- *)
(* from coq plugin lib *)

(* Internal utilities *)
let sconsr bs b = ret (b :: bs)
let srev l = ret (List.rev l)
let sarray_of_list l = ret (Array.of_list l)
let sappendr l1 l2 = ret (List.append l1 l2)
let shas_some o = ret (Option.has_some o)
let ssome a = ret (Some a)
let snone = ret None
let sget o = ret (Option.get o)
      
(*
 * fold_left with state
 *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (ret b sigma) l

(*
 * fold_left2 with state
 *)
let fold_left2_state f c l1 l2 sigma =
  List.fold_left2 (fun (sigma, c) a b -> f c a b sigma) (ret c sigma) l1 l2

(*
 * for correct evar_map threading, fold_right is defined in terms of fold_left
 *)
let fold_right_state f l b =
  fold_left_state (fun b a -> f a b) b (List.rev l)

(*
 * Same over two lists
 *)
let fold_right2_state f l1 l2 b =
  fold_left2_state (fun c a b -> f a b c) b (List.rev l1) (List.rev l2)

(*
 * mapping over tuples
 *)
let map_tuple_state f (p1, p2) =
  bind (f p1) (fun r1 -> bind (f p2) (fun r2 -> ret (r1, r2)))

(*
 * folding over tuples
 *)
let fold_tuple_state f (p1, p2) sigma =
  f p1 p2 sigma

(*
 * For a function that takes and returns state, map that function over a 
 * list of arguments, threading the state through the application to the result.
 *
 * The order here is left-to-right since that is the way functions are applied 
 * in Coq (arguments may depend on earlier arguments). This is sometimes
 * significant.
 *)
let map_state f l =
  bind (fold_left_state (fun bs a -> bind (f a) (sconsr bs)) [] l) srev

(*
 * map2 version
 *)
let map2_state f l1 l2 =
  bind (fold_left2_state (fun cs a b -> bind (f a b) (sconsr cs)) [] l1 l2) srev

(*
 * Array version
 *)
let map_state_array f arr =
  bind (map_state f (Array.to_list arr)) sarray_of_list

(*
 * flatten
 *)
let flatten_state l =
  fold_left_state sappendr [] l

(*
 * flat_map version
 *)
let flat_map_state f l =
  bind (map_state f l) flatten_state
       
(*
 * Stateful if/else
 *)
let branch_state p f g a =
  bind
    (fun sigma_f ->
      bind
        (p a)
        (fun b sigma_t -> ret b (if b then sigma_t else sigma_f))
        sigma_f)
    (fun b -> if b then f a else g a)

(*
 * Stateful and (pa a && pb b)
 *)
let and_state pa pb a b =
  branch_state pa (fun _ -> pb b) (fun _ -> ret false) a

(*
 * Stateful or (pa a || pb b)
 *)
let or_state pa pb a b =
  branch_state pa (fun _ -> ret true) (fun _ -> pb b) a

(*
 * Stateful and (pa a && pb b)
 *)
let and_state_fold pa1 pa2 a =
  and_state pa1 pa2 a a

(*
 * Stateful or (pa a || pb b)
 *)
let or_state_fold pa1 pa2 a =
  or_state pa1 pa2 a a

(*
 * Stateful not
 * Note that if p holds, this returns false and the evar_map from p
 * If p does not hold, this returns true and the evar_map argument
 *)
let not_state p a =
  branch_state p (fun _ -> ret false) (fun _ -> ret true) a
               
(*
 * Predicate version, for exists
 *)
let exists_state p l =
  fold_left_state
    (fun bool -> branch_state (fun _ -> ret bool) (fun _ -> ret bool) p)
    false
    l

(*
 * exists2
 *)
let exists2_state p l1 l2 =
  exists_state
    (fold_tuple_state p)
    (List.combine l1 l2)

(*
 * Stateful forall
 *)
let forall_state p l =
  fold_left_state
    (fun b -> branch_state p (fun _ -> ret b) (fun _ -> ret false))
    true
    l

(*
 * forall2
 *)
let forall2_state p l1 l2 =
  forall_state
    (fold_tuple_state p)
    (List.combine l1 l2)

(*
 * Predicate version, for find
 *)
let find_state p l =
  bind
    (fold_left_state
       (fun o a ->
         branch_state
           shas_some
           ret
           (fun _ -> branch_state p ssome (fun _ -> snone) a)
           o)
       None
       l)
    (branch_state shas_some sget (fun _ _ -> raise Not_found))

(*
 * find2
 *)
let find2_state p l1 l2 =
  find_state
    (fold_tuple_state p)
    (List.combine l1 l2)

(*
 * Filter
 *)
let filter_state p l =
  bind
    (fold_left_state
       (fun a_l ->
         branch_state
           p
           (sconsr a_l)
           (fun _ -> ret a_l))
       []
       l)
    srev

(*
 * filter2
 *)
let filter2_state p l1 l2 =
  filter_state
    (fold_tuple_state p)
    (List.combine l1 l2)

(*
 * Partition
 *)
let partition_state p l =
  bind
    (fold_left_state
       (fun (a_l1, a_l2) ->
         branch_state
           p
           (fun a -> ret (a :: a_l1, a_l2))
           (fun a -> ret (a_l1, a :: a_l2)))
       ([], [])
       l)
    (fun (l1, l2) -> ret (map_tuple List.rev (l1, l2)))

(* (\* Like List.fold_left, but threading state *\) *)
(* let fold_left_state f b l sigma = *)
(*   List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l *)

(* (\* List List.map, but threading state *\) *)
(* let map_state f args = *)
(*   bind *)
(*     (fold_left_state *)
(*        (fun bs a sigma -> *)
(*          let sigma, b = f a sigma in *)
(*          sigma, b :: bs) *)
(*        [] *)
(*        args) *)
(*     (fun fargs -> ret (List.rev fargs)) *)

(* (\* Like fold_left_state, but over arrays *\) *)
(* let fold_left_state_array f b args = *)
(*   fold_left_state f b (Array.to_list args) *)

(* (\* Like map_state, but over arrays *\) *)
(* let map_state_array f args = *)
(*   bind *)
(*     (map_state f (Array.to_list args)) *)
(*     (fun fargs -> ret (Array.of_list fargs)) *)
