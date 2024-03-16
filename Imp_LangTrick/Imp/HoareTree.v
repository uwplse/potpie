From Coq Require Import String Arith List.
From Imp_LangTrick Require Import Base Imp_LangTrickLanguage.
From Imp_LangTrick.Imp Require Import Imp_LangLogProp Imp_LangLogHoare Imp_LangLogSubst.

Inductive imp_hoare_tree :=
| ImpHTSkip (P: AbsEnv)
| ImpHTAssign (P: AbsEnv) (x: ident) (a: aexp_Imp_Lang)
| ImpHTSeq (P Q R: AbsEnv) (i1 i2: imp_Imp_Lang) (H1 H2: imp_hoare_tree)
| ImpHTIf (P Q: AbsEnv) (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang) (H1 H2: imp_hoare_tree)
| ImpHTWhile (P: AbsEnv) (b: bexp_Imp_Lang) (i: imp_Imp_Lang) (H: imp_hoare_tree)
| ImpHTConLeft (Impl: AbsEnv * AbsEnv) (i: imp_Imp_Lang) (Q: AbsEnv) (n: nat) (H: imp_hoare_tree)
| ImpHTConRight (P: AbsEnv) (i: imp_Imp_Lang) (Impl: AbsEnv * AbsEnv) (n: nat) (H: imp_hoare_tree).

Definition get_precondition (ht: imp_hoare_tree): AbsEnv :=
  match ht with
  | ImpHTSkip P => P
  | ImpHTAssign P x a => subst_AbsEnv x a P
  | ImpHTSeq P _ _ _ _ _ _ => P
  | ImpHTIf P _ _ _ _ _ _ => P
  | ImpHTWhile P _ _ _ => P
  | ImpHTConLeft Impl _ _ _ _ =>
      match Impl with
      | (P, _) => P
      end
  | ImpHTConRight P _ _ _ _ => P
  end.

Definition get_postcondition (ht: imp_hoare_tree): AbsEnv :=
  match ht with
  | ImpHTSkip P => P
  | ImpHTAssign P _ _ => P
  | ImpHTSeq _ _ Q _ _ _ _ => Q
  | ImpHTIf _ Q _ _ _ _ _ => Q
  | ImpHTWhile P b _ _ => afalseImp_Lang b P
  | ImpHTConLeft _ _ Q _ _ => Q
  | ImpHTConRight _ _ Impl _ _ =>
      match Impl with
      | (_, Q) => Q
      end
  end.

Inductive valid_tree (P: AbsEnv) (i: imp_Imp_Lang) (Q: AbsEnv) (fenv: fun_env) (fact_env: implication_env) : imp_hoare_tree -> Type :=
| ValidHTSkip :
  P = Q ->
  i = SKIP_Imp_Lang ->
  valid_tree P i Q fenv fact_env (ImpHTSkip P)
| ValidHTAssign :
  forall x a,
    P = subst_AbsEnv x a Q ->
    i = ASSIGN_Imp_Lang x a ->
    valid_tree P i Q fenv fact_env (ImpHTAssign Q x a)
| ValidHTSeq :
  forall R i1 i2 H1 H2,
    i = SEQ_Imp_Lang i1 i2 ->
    valid_tree P i1 R fenv fact_env H1 ->
    valid_tree R i2 Q fenv fact_env H2 ->
    valid_tree P i Q fenv fact_env (ImpHTSeq P Q R i1 i2 H1 H2)
| ValidHTIf :
  forall b i1 i2 H1 H2,
    i = IF_Imp_Lang b i1 i2 ->
    valid_tree (atrueImp_Lang b P) i1 Q fenv fact_env H1 ->
    valid_tree (afalseImp_Lang b P) i2 Q fenv fact_env H2 ->
    valid_tree P i Q fenv fact_env (ImpHTIf P Q b i1 i2 H1 H2)
| ValidHTWhile :
  forall b i' H,
    i = WHILE_Imp_Lang b i' ->
    valid_tree (atrueImp_Lang b P) i' P fenv fact_env H ->
    Q = afalseImp_Lang b P ->
    valid_tree P i Q fenv fact_env (ImpHTWhile P b i' H)
| ValidHTConLeft :
  forall Impl P' H n,
    Impl = (P, P') ->
    nth_error fact_env n = Some Impl ->
    aimpImp_Lang P P' fenv ->
    valid_tree P' i Q fenv fact_env H ->
    valid_tree P i Q fenv fact_env (ImpHTConLeft Impl i Q n H)
| ValidHTConRight :
  forall Impl Q' H n,
    Impl = (Q', Q) ->
    nth_error fact_env n = Some Impl ->
    aimpImp_Lang Q' Q fenv ->
    valid_tree P i Q' fenv fact_env H ->
    valid_tree P i Q fenv fact_env (ImpHTConRight P i Impl n H).

Lemma valid_tree_implies_hl : 
  forall i P Q fenv fact_env tree, 
    valid_tree P i Q fenv fact_env tree ->
    hl_Imp_Lang P i Q fact_env fenv.
Proof.
    intros. induction X. 
    - subst. econstructor.
    - subst. econstructor.
    - subst. econstructor; eassumption.
    - subst. econstructor; eassumption.
    - subst. econstructor; eassumption.    
    - rewrite e in *. econstructor. apply IHX. eassumption. eassumption.
    - rewrite e in *. eapply hl_Imp_Lang_consequence_post. apply IHX. apply e0. eassumption.
Qed.   

Fixpoint imp_tree_constructor (P: AbsEnv) (i: imp_Imp_Lang) (Q: AbsEnv) (fenv: fun_env) (facts: implication_env) (tree: hl_Imp_Lang P i Q facts fenv): imp_hoare_tree :=
  match tree with
  | hl_Imp_Lang_skip Pre _ _ => ImpHTSkip Pre
  | hl_Imp_Lang_assign Post _ _ x a => ImpHTAssign Post x a
  | hl_Imp_Lang_seq P Q R f' f i1 i2 H1 H2 =>
      ImpHTSeq P Q R i1 i2
               (imp_tree_constructor P i1 R f f' H1)
               (imp_tree_constructor R i2 Q f f' H2)
  | hl_Imp_Lang_if P Q b i1 i2 f' f H1 H2 =>
      ImpHTIf P Q b i1 i2
              (imp_tree_constructor (atrueImp_Lang b P) i1 Q f f' H1)
              (imp_tree_constructor (afalseImp_Lang b P) i2 Q f f' H2)
  | hl_Imp_Lang_while P b i' f' f H =>
      ImpHTWhile P b i'
                 (imp_tree_constructor (atrueImp_Lang b P) i' P f f' H)
  | hl_Imp_Lang_consequence_pre P Q P' i' n f' f H _ _ =>
      ImpHTConLeft (P', P) i' Q n
                   (imp_tree_constructor P i' Q f f' H)
  | hl_Imp_Lang_consequence_post P Q Q' i' n f' f H _ _ =>
      ImpHTConRight P i' (Q, Q') n
                    (imp_tree_constructor P i' Q f f' H)
  end.

Lemma HTConstructor_valid : 
  forall P i Q fenv facts tree, 
    valid_tree P i Q fenv facts (imp_tree_constructor P i Q fenv facts tree).
Proof. 
induction tree.
  - econstructor; reflexivity.
  - econstructor; reflexivity.
  - pose proof ValidHTSeq P (SEQ_Imp_Lang i1 i2) Q fenv fact_env R i1 i2
    (imp_tree_constructor P i1 R fenv fact_env tree1)
    (imp_tree_constructor R i2 Q fenv fact_env tree2) 
    eq_refl IHtree1 IHtree2. simpl. apply X.
  - econstructor; try reflexivity.
    + apply IHtree1.
    + apply IHtree2.
  - econstructor; try reflexivity; try assumption.
  - eapply ValidHTConLeft; try reflexivity; try assumption.
  - eapply ValidHTConRight; try reflexivity; try assumption.
Qed.       
(* Running into the same problem with dependent types...and 
 * not being sure that H1 and H2 for example in ImpHTSeq are 
 * hoare trees with P, Q as the pre/post condition for H1 and 
 * Q, R as the pre/postcondition for H2 *)
(* Fixpoint imp_hoare_tree_valid (ht: imp_hoare_tree) (fenv: fun_env) (impl_env: implication_env) (v: fact_env_valid impl_env fenv): bool := *)
  (* match ht with *)
  (* | ImpHTSkip _ => true *)
  (* | ImpHTAssign _ _ _ => true *)
  (* | ImpHTSeq P Q R _ _ H1 H2 => false *)
  (* | _ => false *)
  (* end. *)

(*
From Imp_LangTrick Require Import LogicProp.
Definition true_absenv :=
  AbsEnvLP (Imp_Lang_lp_arith (TrueProp _ _)).

Definition false_absenv :=
  AbsEnvLP (Imp_Lang_lp_arith (FalseProp _ _ )).

Print True.
Print False.

Print eq_refl.

From Imp_LangTrick Require Import Imp.Imp_LangDec LogicProp.LogicPropDec.


Lemma abs_env_eq_dec :
  forall (a b: AbsEnv),
    { a = b } + { a <> b }.
Proof.
  decide equality.
  decide equality.
  decide equality; try eapply aexp_Imp_Lang_dec.
  
  
  

Example abs_env_equality_matching :
  forall (H: true_absenv = true_absenv),
    match H with
    | eq_refl _ => True
    end.
Proof.
  intros.
  unfold true_absenv in H.
  inversion H.


Compute (match (true_absenv  = false_absenv) with
         | eq_refl _ => true
         end).
Example abs_env_equality_matching :
    match true_absenv = false_absenv with
    | False => False
    end.

*)
