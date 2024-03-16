From Coq Require Import List Arith Bool String.

From Imp_LangTrick Require Import StackLanguage StackLogicBase ReflectionMachinery MyOptionUtils StateUpdateAdequacy.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition construct_stack_large_enough (k: stack_index) (P: AbsStack) : option (stack_large_enough k P) :=
  match P with
  | AbsStkTrue => None
  | AbsStkSize geq_num =>
      match (le_gt_dec k geq_num) with
      | left H =>
          Some (LargeEnoughGeq k geq_num H)
      | _ => None
      end
  end.


Section construct_state_update_rel_section.
  Let construct_base_state_update (k: stack_index) (newval: aexp_stack) (P: AbsState): option (state_update_rel k newval P (state_update k newval P)) :=
  match P with
  | BaseState s m =>
      let update_m := meta_update k newval m in
      let mu := match (meta_update_adequacy k newval m update_m) with
                | conj A _ =>
                    A (eq_refl update_m)
                end in
      let awf := StackExprWellFormed.construct_aexp_well_formed newval in
      let mwf := StackExprWellFormed.construct_mv_well_formed m in
      let sle := construct_stack_large_enough k s in
      match awf, mwf, sle with
      | Some A, Some M, Some SL =>
          Some (UpBaseState k newval s m update_m mu A M SL)
      | _ , _, _=> None
      end
  | _ => None
  end.

Fixpoint construct_state_update_rel (k: stack_index) (newval: aexp_stack) (P: AbsState): option (state_update_rel k newval P (state_update k newval P)) :=
  let binary_case := (fun A1 A2 => let wf1 := StackExprWellFormed.construct_absstate_well_formed A1 in
                               let wf2 := StackExprWellFormed.construct_absstate_well_formed A2 in
                               let su1 := construct_state_update_rel k newval A1 in
                               let su2 := construct_state_update_rel k newval A2 in
                               (* let A1' := state_update k newval A1 in *)
                               (* let A2' := state_update k newval A2 in *)
                               let awf := StackExprWellFormed.construct_aexp_well_formed newval in
                               (wf1, wf2, su1, su2, (*A1', A2',*) awf)) in
  match P with
  | BaseState s m =>
      construct_base_state_update k newval (BaseState s m) (* helper function to make types better *)
  | AbsAnd A1 A2 =>
      match binary_case A1 A2 with
      | (wf1, wf2, su1, su2, awf) =>
          let A1' := state_update k newval A1 in
          let A2' := state_update k newval A2 in
          match wf1, wf2, su1, su2, awf with
          | Some W1, Some W2, Some U1, Some U2, Some WFa =>
              Some (UpAbsAnd k newval A1 A2 A1' A2' U1 U2 WFa W1 W2)
          | _, _, _, _, _ => None
          end
      end
  | AbsOr A1 A2 =>
      match binary_case A1 A2 with
      | (wf1, wf2, su1, su2, awf) =>
          let A1' := state_update k newval A1 in
          let A2' := state_update k newval A2 in
          match wf1, wf2, su1, su2, awf with
          | Some W1, Some W2, Some U1, Some U2, Some WFa =>
              Some (UpAbsOr k newval A1 A2 A1' A2' U1 U2 W1 W2 WFa)
          | _, _, _, _, _ => None
          end
      end
        
  end.
End construct_state_update_rel_section.
      
