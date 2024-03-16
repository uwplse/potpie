From Coq Require Import Psatz List.

From Imp_LangTrick Require Import StackUpdateAdequacy StackLogicBase StackPurestBase StackLanguage LogicProp ImpVarMap StackLogicGrammar Imp_LangLogProp Imp_LangTrickLanguage ReflectionMachinery Imp_LangImpHigherOrderRel ProofCompilerBase.

Local Open Scope list_scope.

Ltac prove_stack_large_enough_for_state :=
  match goal with
  | [ |- stack_large_enough_for_state _ _ ] =>
      econstructor; prove_stack_large_enough_for_state
  | [ |- stack_large_enough _ _ ] =>
      simpl; econstructor; try lia
  end.


Ltac prove_expr_stack_pure :=
  match goal with
  | [ |- bexp_stack_pure_rel _ _ ] =>
      econstructor; try prove_expr_stack_pure
  | [ |- aexp_stack_pure_rel _ _ ] =>
      econstructor; try prove_expr_stack_pure
  | [ |- args_stack_pure_rel _ _ ] =>
      econstructor; try prove_expr_stack_pure
  | [ |- _ <= _ ] =>
      lia
  | [ |- _ = _ ] =>
      reflexivity
  end.


Fixpoint stack_mutation (n: nat) (c: nat) (xs: list nat) : option (list nat) :=
  match n with
  | 0 => None
  | 1 =>
      match xs with
      | nil =>
          None
      | x :: xs' =>
          Some (c :: xs')
      end
  | S (S n') =>
      match xs with
      | nil =>
          None
      | x :: xs' =>
          match stack_mutation (S n') c xs' with
          | Some xs'' =>
              Some (x :: xs'')
          | None =>
              None
          end
      end
  end.



Ltac smash_stack_mutated_at_index :=
  simpl;
  match goal with
  | [ |- stack_mutated_at_index _ (S (S ?n)) ?c (?x :: ?xs) ] =>
      idtac xs;
      eapply stk_mut_rest with
        (stk :=
           match stack_mutation (S n) c (xs) with
           | Some x' => x'
           | _ => nil
           end);
      try smash_stack_mutated_at_index
  | [ |- stack_mutated_at_index (?c :: ?xs) 1 ?c (_ :: ?xs) ] =>
      econstructor; smash_stack_mutated_at_index
  | [ |- stack_mutated_at_index _ 1 ?c (_ :: ?xs) ] =>
      eapply stk_mut_first with (stk := xs); try smash_stack_mutated_at_index
  | [ |- _ > _ ] =>
      simpl; lia
  | [ |- _ <= _ ] =>
      simpl; lia
  | [ |- _ = _ ] =>
      simpl; try reflexivity
  | [ |- _ ] =>
      simpl
  end.

Ltac save_val_simpl :=
  let myval := fresh "myval" in
  match goal with
  | [ |- b_Imp_Lang _ _ _ _ ?bval ] =>
      let mybval := fresh "bval" in
      remember bval as mybval;
      simpl;
      subst mybval
  | [ |- a_Imp_Lang (PLUS_Imp_Lang _ _) _ _ _ ?val ] =>
      match val with
      | Nat.add _ _ =>
          remember val as myval;
          simpl;
          subst myval
      | _ => simpl
      end
  | [ |- _ ] =>
      simpl
  end.

(** Get things to their bare bones *)
Ltac meta_smash :=
  save_val_simpl;
  (* match goal with *)
  (* | [ |- b_Imp_Lang _ _ _ _ _ ?bval ] => *)
  (*     let mybval := fresh "bval" in *)
  (*     remember bval as mybval; *)
  (*     simpl; *)
  (*     subst mybval *)
  (* | [ |- _ ] => *)
  (*     simpl *)
  (* end; *)
    match goal with
    | [ |- absstate_match_rel _ _ _ ] =>
        econstructor; meta_smash
    | [ |- absstack_match_rel _ _ ] =>
        econstructor; meta_smash
    | [ |- AbsEnv_rel _ _ _ _ ] =>
        econstructor; meta_smash
    | [ |- meta_match_rel _ _ _ ] =>
        econstructor; meta_smash
    | [ |- eval_prop_rel _ _ ] =>
        econstructor; meta_smash
    | [ |- Imp_Lang_lp_prop_rel _ _ _ ] =>
        econstructor; meta_smash
    | [ |- bexp_stack_sem (?comp_bool _ _) _ _ _ ] =>
        progress unfold comp_bool; save_val_simpl; meta_smash
    | [ |- bexp_stack_sem _ _ _ _ ] =>
        econstructor; meta_smash
    | [ |- b_Imp_Lang _ _ _ _ _ ] =>
        econstructor; meta_smash
    | [ |- aexp_stack_sem _ _ _ _ ] =>
        econstructor; try unfold stack_mapping; save_val_simpl; try lia; try reflexivity; meta_smash
    | [ |- a_Imp_Lang _ _ _ _ _ ] =>
        econstructor; save_val_simpl; try lia; try reflexivity; meta_smash
    | [ |- args_stack_sem nil _ _ _ ] =>
        econstructor
    | [ |- args_Imp_Lang nil _ _ _ _ ] =>
        econstructor
    | [ |- args_Imp_Lang _ _ _ _ _ ] =>
        econstructor; simpl; meta_smash
    | [ |- args_stack_sem _ _ _ _ ] =>
        econstructor; simpl; meta_smash
    | [ |- imp_stack_sem (Assign_Stk _ _) _ _ _ ] =>
        econstructor; try unfold stack_mapping; simpl; try smash_stack_mutated_at_index; meta_smash
    | [ |- i_Imp_Lang (ASSIGN_Imp_Lang _ _) _ _ _ _ ] =>
        econstructor; simpl; meta_smash
    | [ |- imp_stack_sem (Seq_Stk _ _) _ _ _ ] =>
        econstructor; simpl; meta_smash
    | [ |- i_Imp_Lang (SEQ_Imp_Lang _ _) _ _ _ _ ] =>
        econstructor; simpl; meta_smash
    | [ |- imp_stack_sem Push_Stk _ _ _ ] =>
        econstructor; simpl; try reflexivity; meta_smash
    | [ |- _ = _ ] =>
        try reflexivity
    | [ |- _ <= _ ] =>
        try lia
    | [ |- _ ] =>
        idtac
    end;
    try unfold stack_mapping.

Definition imp_rec_rel_constructor (phi: imp_Imp_Lang -> Prop) (i: imp_Imp_Lang) : option (phi i -> imp_rec_rel phi i) :=
  match i as i' return option (phi i' -> imp_rec_rel phi i') with
  | SKIP_Imp_Lang =>
      Some (fun P => ImpRecRelSkip phi P)
  | ASSIGN_Imp_Lang x a =>
      Some (fun P => ImpRecRelAssign phi x a P)
  | IF_Imp_Lang b i1 i2 =>
      @None _
  | SEQ_Imp_Lang i1 i2 =>
      @None _
  | WHILE_Imp_Lang b i' =>
      @None _
  end.

Ltac prove_imp_rec_rel P :=
  match goal with
  | [ |- imp_rec_rel (var_map_wf_wrt_imp ?idents) ?i ] =>
      exact
        ((optionOut
            ((var_map_wf_wrt_imp idents i)
             -> imp_rec_rel (var_map_wf_wrt_imp idents) i)
            (imp_rec_rel_constructor (var_map_wf_wrt_imp idents) i)) P)
  end.

Fixpoint prop_rel_arith_constructor (phia: aexp_Imp_Lang -> Prop) (l: LogicProp nat aexp_Imp_Lang) : option (prop_rel phia l) :=
  match l as l' return option (prop_rel phia l') with
  | TrueProp _ _ =>
      Some (PropRelTrueProp phia)
  | FalseProp _ _ =>
      Some (RelFalseProp phia)
  | UnaryProp _ _ f a =>
      @None _
      (* Some (PropRelUnaryProp phia f a (phia a)) *)
  | BinaryProp _ _ f a1 a2 =>
      @None _
  | AndProp _ _ p1 p2 =>
      @None _
  | OrProp _ _ p1 p2 =>
      @None _
  | TernaryProp _ _ f a1 a2 a3 =>
      @None _
  | NaryProp _ _ f args =>
      @None _
  end.

Fixpoint prop_rel_bool_constructor (phia: bexp_Imp_Lang -> Prop) (l: LogicProp bool bexp_Imp_Lang) : option (prop_rel phia l) :=
  match l as l' return (option (prop_rel phia l')) with
  | TrueProp _ _ =>
      Some (PropRelTrueProp phia)
  | FalseProp _ _ =>
      Some (RelFalseProp phia)
  | UnaryProp _ _ f a =>
      @None _
      (* Some (PropRelUnaryProp phia f a (phia a)) *)
  | BinaryProp _ _ f a1 a2 =>
      @None _
  | AndProp _ _ p1 p2 =>
      @None _
  | OrProp _ _ p1 p2 =>
      @None _
  | TernaryProp _ _ f a1 a2 a3 =>
      @None _
  | NaryProp _ _ f args =>
      @None _
  end.

Definition Imp_Lang_lp_prop_rel_constructor (phia: aexp_Imp_Lang -> Prop) (phib: bexp_Imp_Lang -> Prop) (l: Imp_Lang_lp) : option (Imp_Lang_lp_prop_rel phia phib l) :=
  match l as l' return (option (Imp_Lang_lp_prop_rel phia phib l')) with
  | Imp_Lang_lp_arith l'' =>
      match ((prop_rel_arith_constructor phia l''))  with
      | Some P =>
          Some (Imp_LangLPPropArith phia phib l'' P)
      | None => None
      end
  | Imp_Lang_lp_bool l'' =>
      match ((prop_rel_bool_constructor phib l''))  with
      | Some P =>
          Some (Imp_LangLPPropBool phia phib l'' P)
      | None => None
      end
  end.

Fixpoint AbsEnv_prop_rel_constructor (phia: aexp_Imp_Lang -> Prop) (phib: bexp_Imp_Lang -> Prop) (ae: AbsEnv) : option (AbsEnv_prop_rel phia phib ae) :=
  match ae as ae' return (option (AbsEnv_prop_rel phia phib ae')) with
  | AbsEnvLP l =>
      match (Imp_Lang_lp_prop_rel_constructor phia phib l) with
      | Some P =>
          Some (Imp_LangLogPropRelLP phia phib l P)
      | _ =>
          None
      end
  | AbsEnvAnd l1 l2 =>
      match (AbsEnv_prop_rel_constructor phia phib l1) with
      | Some P1 =>
          match (AbsEnv_prop_rel_constructor phia phib l2) with
          | Some P2 =>
              Some (Imp_LangLogPropRelAnd phia phib l1 l2 P1 P2)
          | _ => None
          end
      | _ => None
      end
  | AbsEnvOr l1 l2 =>
      match (AbsEnv_prop_rel_constructor phia phib l1) with
      | Some P1 =>
          match (AbsEnv_prop_rel_constructor phia phib l2) with
          | Some P2 =>
              Some (Imp_LangLogPropRelOr phia phib l1 l2 P1 P2)
          | _ => None
          end
      | _ => None
      end
  end.

Ltac prove_AbsEnv_prop_wf :=
  match goal with
  | [ |- AbsEnv_prop_wf _ _ ] =>
      unfold AbsEnv_prop_wf; prove_AbsEnv_prop_wf
  | [ |- AbsEnv_prop_rel (var_map_wf_wrt_aexp ?idents) (var_map_wf_wrt_bexp ?idents) ?d ] =>
      exact (optionOut (AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d)
                       (AbsEnv_prop_rel_constructor (var_map_wf_wrt_aexp idents)
                                                    (var_map_wf_wrt_bexp idents) d))
  end.
    
