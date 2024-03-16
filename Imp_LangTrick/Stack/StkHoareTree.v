From Coq Require Import String Arith List.
(* Print LoadPath. *)
From Imp_LangTrick Require Import Base Stack.StackLanguage StackLogicGrammar Stack.StackLogicBase StackLogic.

Inductive stk_hoare_tree :=
| StkHTSkip (P: AbsState)
| StkHTAssign (P: AbsState) (k: stack_index) (a: aexp_stack)
| StkHTPush (P: AbsState)
| StkHTPop (P Q P': AbsState)
| StkHTSeq (P Q R: AbsState) (i1 i2: imp_stack) (H1 H2: stk_hoare_tree)
| StkHTIf (P Q: AbsState) (b: bexp_stack) (i1 i2: imp_stack) (H1 H2: stk_hoare_tree)
| StkHTWhile (P: AbsState) (b: bexp_stack) (i: imp_stack) (H: stk_hoare_tree)
| StkHTConLeft (Impl: AbsState * AbsState) (i: imp_stack) (Q: AbsState) (n: nat) (H: stk_hoare_tree)
| StkHTConRight (P: AbsState) (i: imp_stack) (Impl: AbsState * AbsState) (n: nat) (H: stk_hoare_tree)
| StkHTCon (Impl1 Impl2: AbsState * AbsState) (i: imp_stack) (H: stk_hoare_tree).

(* Definition get_command (ht: stk_hoare_tree) : imp_stack := *)
(*   match ht with *)
(*   | StkHTSkip _ => Skip_Stk *)
(*   | StkHTAssign _ k a => Assign_Stk k a *)
(*   | StkHTPush _ => Push_Stk *)
(*   | StkHTAssign  *)

Definition get_precondition (ht: stk_hoare_tree) : AbsState :=
  match ht with
  | StkHTSkip P => P
  | StkHTAssign P k a => state_update k a P
  | StkHTPush P => P
  | StkHTPop P Q P' => AbsAnd P Q
  | StkHTSeq P _ _ _ _ _ _ => P
  | StkHTIf P _ _ _ _ _ _ => P
  | StkHTWhile P _ _ _ => P
  | StkHTConLeft Impl _ _ _ _ =>
      match Impl with
      | (P, _) => P
      end
  | StkHTConRight P _ _ _ _ => P
  | StkHTCon Impl1 _ _ _ =>
      match Impl1 with
      | (P, _) => P
      end
  end.

Definition get_postcondition (ht: stk_hoare_tree) : AbsState :=
  match ht with
  | StkHTSkip P => P
  | StkHTAssign P _ _ => P
  | StkHTPush P => StackIncrease.absstate_stack_size_inc 1 P
  | StkHTPop _ _ P' => P'
  | StkHTSeq _ _ R _ _ _ _ => R
  | StkHTIf _ Q _ _ _ _ _ => Q
  | StkHTWhile P b _ _ => StackLogic.afalsestk b P
  | StkHTConLeft _ _ Q _ _ => Q
  | StkHTConRight _ _ Impl _ _ =>
      let (Q', Q) := Impl in Q
  | StkHTCon _ Impl2 _ _ =>
      let (Q', Q) := Impl2 in Q
  end.
              

Inductive stk_valid_tree (P: AbsState) (i: imp_stack) (Q: AbsState) (fenv: fun_env_stk) (fact_env: implication_env_stk): stk_hoare_tree -> Type :=
| StkValidHTSkip :
  P = Q ->
  i = Skip_Stk ->
  fact_env_valid fact_env fenv ->
  stk_valid_tree P i Q fenv fact_env (StkHTSkip P)
| StkValidHTAssign :
  forall k a,
    state_update_rel k a Q P ->
    (* P = state_update k a Q -> *)
    i = Assign_Stk k a ->
    fact_env_valid fact_env fenv ->
    StackPurestBase.aexp_stack_pure_rel a fenv ->
    stk_valid_tree P i Q fenv fact_env (StkHTAssign Q k a)
| StkValidHTPush :
  state_stk_size_inc 1 P Q ->
  i = Push_Stk ->
  fact_env_valid fact_env fenv ->
  stk_valid_tree P i Q fenv fact_env (StkHTPush P)
| StkValidHTPop :
  forall P1 P2,
    P = AbsAnd P1 P2 ->
    state_stk_size_inc 1 Q P1 ->
    i = Pop_Stk ->
    fact_env_valid fact_env fenv ->
    stk_valid_tree P i Q fenv fact_env (StkHTPop P1 P2 Q)
| StkValidHTSeq :
  forall R H1 H2 i1 i2,
    i = Seq_Stk i1 i2 ->
    fact_env_valid fact_env fenv ->
    stk_valid_tree P i1 R fenv fact_env H1 ->
    stk_valid_tree R i2 Q fenv fact_env H2 ->
    stk_valid_tree P i Q fenv fact_env (StkHTSeq P R Q i1 i2 H1 H2)
| StkValidHTIf :
  forall b i1 i2 H1 H2,
    i = If_Stk b i1 i2 ->
    fact_env_valid fact_env fenv ->
    StackPurestBase.bexp_stack_pure_rel b fenv ->
    stk_valid_tree (atruestk b P) i1 Q fenv fact_env H1 ->
    stk_valid_tree (afalsestk b P) i2 Q fenv fact_env H2 ->
    stk_valid_tree P i Q fenv fact_env (StkHTIf P Q b i1 i2 H1 H2)
| StkValidHTWhile :
  forall b i' H,
    i = While_Stk b i' ->
    Q = afalsestk b P ->
    fact_env_valid fact_env fenv ->
    StackPurestBase.bexp_stack_pure_rel b fenv ->
    stk_valid_tree (atruestk b P) i' P fenv fact_env H ->
    stk_valid_tree P i Q fenv fact_env (StkHTWhile P b i' H)
| StkValidHTCon :
  forall Impl1 Impl2 H P' Q',
    Impl1 = (P, P') ->
    Impl2 = (Q', Q) ->
    (* fact_env_valid fact_env fenv -> *)
    aimpstk P P' fenv ->
    aimpstk Q' Q fenv ->
    (* nth_error fact_env np = Some Impl1 -> *)
    (* nth_error fact_env nq = Some Impl2 -> *)
    stk_valid_tree P' i Q' fenv fact_env H ->
    stk_valid_tree P i Q fenv fact_env (StkHTCon Impl1 Impl2 i H)           | StkValidHTConLeft :
  forall Impl P' H n,
    Impl = (P, P') ->
    fact_env_valid fact_env fenv ->
    aimpstk P P' fenv ->
    nth_error fact_env n = Some Impl ->
    stk_valid_tree P' i Q fenv fact_env H ->
    stk_valid_tree P i Q fenv fact_env (StkHTConLeft Impl i Q n H)
| StkValidHTConRight :
  forall Impl Q' H n,
    Impl = (Q', Q) ->
    fact_env_valid fact_env fenv ->
    aimpstk Q' Q fenv ->
    nth_error fact_env n = Some Impl ->
    stk_valid_tree P i Q' fenv fact_env H ->
    stk_valid_tree P i Q fenv fact_env (StkHTConRight P i Impl n H).

Print stk_valid_tree.
Print StkValidHTSkip.

Create HintDb stk_trees.
#[export]
Hint Constructors stk_valid_tree : stk_trees.
    
Fixpoint stk_tree_constructor (P: AbsState) (i: imp_stack) (Q: AbsState) (fenv: fun_env_stk) (facts: implication_env_stk) (tree: hl_stk P i Q facts fenv): stk_hoare_tree :=
  match tree with
  | hl_stk_skip P _ _ _ => StkHTSkip P
  | hl_stk_assign P k a _ _ _ _ _ _ => StkHTAssign P k a
  | hl_stk_push P _ _ _ _ _ => StkHTPush P
  | hl_stk_pop P P' Q _ _ _ _ => StkHTPop P Q P'
  | hl_stk_seq P Q R i1 i2 facts' fenv' _ H1 H2 =>
      StkHTSeq P R Q i1 i2
               (stk_tree_constructor P i1 R fenv' facts' H1)
               (stk_tree_constructor R i2 Q fenv' facts' H2)
  | hl_stk_if P Q b i1 i2 facts' fenv' _ _ H1 H2 =>
      StkHTIf P Q b i1 i2
              (stk_tree_constructor (atruestk b P) i1 Q fenv' facts' H1)
              (stk_tree_constructor (afalsestk b P) i2 Q fenv' facts' H2)
  | hl_stk_while P b i facts' fenv' _ _ H =>
      StkHTWhile P b i
                 (stk_tree_constructor (atruestk b P) i P fenv' facts' H)
  | hl_stk_consequence_STKONLY P Q P' Q' i facts' fenv' H _ _ =>
      StkHTCon (P', P) (Q, Q') i
               (stk_tree_constructor P i Q fenv' facts' H)
  | hl_stk_consequence_pre P Q P' i n facts' fenv' _ H _ =>
      StkHTConLeft (P', P) i Q n
                   (stk_tree_constructor P i Q fenv' facts' H)
  | hl_stk_consequence_post P Q Q' i n facts' fenv' _ H _ =>
      StkHTConRight P i (Q, Q') n
                    (stk_tree_constructor P i Q fenv' facts' H)
  end.

Require Import StateUpdateAdequacy.

Lemma nth_error_nil_None :
  forall (A: Type) (n: nat),
    @nth_error A nil n = None.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. reflexivity.
Qed.

Lemma nth_error_facts_implies_aimpstk :
  forall (facts: implication_env_stk) (fenv: fun_env_stk) (n: nat) (P Q: AbsState),
    fact_env_valid facts fenv ->
    nth_error facts n = Some (P, Q) ->
    aimpstk P Q fenv.
Proof.
  induction facts; simpl; intros.
  - rewrite nth_error_nil_None in H0. invs H0.
  - destruct n.
    + simpl in H0. invs H0. unfold fact_env_valid in H.
      eapply H. econstructor. reflexivity.
    + simpl in H0. eapply IHfacts.
      unfold fact_env_valid in *.
      intros. eapply H.
      simpl. right. assumption.
      eassumption.
Qed.

Theorem stk_tree_constructs_valid_tree :
  forall (P: AbsState) (i: imp_stack) (Q: AbsState) (facts: implication_env_stk) (fenv: fun_env_stk),
  forall (H: hl_stk P i Q facts fenv),
  forall (T: stk_hoare_tree),
    T = stk_tree_constructor P i Q fenv facts H ->
    stk_valid_tree P i Q fenv facts T.
Proof.
  induction H; simpl; intros; subst; econstructor; eauto.
  (* [econstructor; eauto .. | | econstructor; eauto | econstructor; eauto]. *)
  (* - eapply state_update_adequacy_backwards in s. congruence. *)
  (* - eapply StkValidHTCon; eauto. *)
  - eapply nth_error_facts_implies_aimpstk; eauto.
  - eapply nth_error_facts_implies_aimpstk; eauto.
Defined.

From Imp_LangTrick Require Import StackUpdateAdequacy.

Theorem valid_tree_can_construct_hl_stk :
  forall (P: AbsState) (i: imp_stack) (Q: AbsState) (facts: implication_env_stk) (fenv: fun_env_stk),
  forall (T: stk_hoare_tree),
  forall (V: stk_valid_tree P i Q fenv facts T),
    hl_stk P i Q facts fenv.
Proof.
  intros. induction V; intros; subst; [ econstructor; eauto .. | | ].
  - eapply hl_stk_consequence_pre; eauto.
  - eapply hl_stk_consequence_post; eauto.
Defined.
