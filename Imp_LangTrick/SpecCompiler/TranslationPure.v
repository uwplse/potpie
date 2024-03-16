From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From Imp_LangTrick Require Import Imp.Imp_LangTrickLanguage Imp.Imp_LangLogProp Imp.Imp_LangLogicHelpers StackLanguage EnvToStack StackLogicGrammar LogicProp LogicTranslationBase StackPurest StackLangTheorems.
From Imp_LangTrick Require Import Imp.Imp_LangLogicHelpers Imp.Imp_LangTrickSemanticsMutInd StackFrame Imp.ImpVarMapTheorems RCompileMutInd.
From Imp_LangTrick Require Import FunctionWellFormed ParamsWellFormed Imp.Imp_LangDec.
Require Import Imp_LangTrick.CodeCompiler.Correctness.CompilerCorrectMoreHelpers.

                      
Local Open Scope string_scope.

Inductive no_pushes_or_pops_and_fxn_calls_fine : fun_env_stk -> imp_stack -> Prop :=
| NoPushPopSkip :
  forall fenv,
    no_pushes_or_pops_and_fxn_calls_fine fenv Skip_Stk
| NoPushPopAssign :
  forall fenv x a,
    (exists k,
        aexp_frame_rule a fenv k) ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (Assign_Stk x a)
| NoPushPopSeq :
  forall fenv i1 i2,
    no_pushes_or_pops_and_fxn_calls_fine fenv i1 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i2 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (Seq_Stk i1 i2)
| NoPushPopIf :
  forall fenv b i1 i2,
    (exists k,
        bexp_frame_rule b fenv k) ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i1 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i2 ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (If_Stk b i1 i2)
| NoPushPopWhile :
  forall fenv b i,
    (exists k,
        bexp_frame_rule b fenv k) ->
    no_pushes_or_pops_and_fxn_calls_fine fenv i ->
    no_pushes_or_pops_and_fxn_calls_fine fenv (While_Stk b i).

Section in_construct_trans_vs_in_free_vars_proof.
  Lemma in_construct_trans_implies_in_free_vars :
    forall (i: imp_Imp_Lang) (x: ident),
      In x (construct_trans i) ->
      In x (free_vars_imp_src i).
  Proof.
    unfold construct_trans.
    destruct i; intros; simpl in H; simpl.
    - eapply ListSet.set_union_iff.
      eapply fold_left_containment_helper_forward in H.
      eapply ListSet.set_union_iff in H.
      destruct H.
      + left. assumption.
      + right. eapply ListSet.set_union_iff in H.
        eapply ListSet.set_union_iff.
        destruct H; auto.
    - assumption.
    - eapply fold_left_containment_helper_forward in H.
      eapply ListSet.set_union_iff. eapply ListSet.set_union_iff in H.
      destruct H; auto.
    - eapply fold_left_containment_helper_forward in H.
      assumption.
    - eapply fold_left_containment_helper_forward in H.
      assumption.
  Qed.
End in_construct_trans_vs_in_free_vars_proof.

Lemma in_free_vars_implies_in_construct_trans :
  forall (i: imp_Imp_Lang) (x: ident),
    In x (free_vars_imp_src i) ->
    In x (construct_trans i).
Proof.
  intros. unfold construct_trans.
  eapply fold_left_containment_helper. assumption.
Qed.

Lemma in_construct_trans_vs_in_free_vars :
  forall (i: imp_Imp_Lang) (x: ident),
    In x (construct_trans i) <->
      In x (free_vars_imp_src i).
Proof.
  split; intros.
  - eapply in_construct_trans_implies_in_free_vars. assumption.
  - eapply in_free_vars_implies_in_construct_trans. assumption.
Qed.



Require Import Coq.Program.Equality.
Require Import Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems.
Require Import ZArith.

Lemma in_forall :
  forall (A: Type) (P: A -> Prop) (l: list A) (a: A),
    In a l ->
    Forall P l ->
    P a.
Proof.
  clear.
  induction l; intros.
  - invs H.
  - invs H.
    + invs H0. assumption.
    + invs H0. eapply IHl. assumption. assumption.
Qed.

Section CompiledImp_LangFrame.
  Print stack_frame_rule_mut_ind.

  Inductive no_pushes_pops : fun_env_stk -> imp_stack -> Prop :=
  | no_pushes_pops_skip :
    forall fenv,
      no_pushes_pops fenv Skip_Stk
  | no_pushes_pops_assign :
    forall (fenv: fun_env_stk) (k: nat) (a: aexp_stack),
      1 <= k ->
      (exists f,
         aexp_frame_rule a fenv f) ->
      no_pushes_pops fenv (Assign_Stk k a)
  | no_pushes_pops_seq :
    forall (fenv: fun_env_stk) (i1 i2: imp_stack),
      no_pushes_pops fenv i1 ->
      no_pushes_pops fenv i2 ->
      no_pushes_pops fenv (Seq_Stk i1 i2)
  | no_pushes_pops_if :
    forall (fenv: fun_env_stk) (b: bexp_stack) (i1 i2: imp_stack),
      (exists f,
          bexp_frame_rule b fenv f) ->
      no_pushes_pops fenv i1 ->
      no_pushes_pops fenv i2 ->
      no_pushes_pops fenv (If_Stk b i1 i2)
  | no_pushes_pops_while :
    forall (fenv: fun_env_stk) (b: bexp_stack) (i: imp_stack),
      (exists f,
          bexp_frame_rule b fenv f) ->
      no_pushes_pops fenv i ->
      no_pushes_pops fenv (While_Stk b i).

  Lemma no_pushes_pops_means_constant_frame :
    forall (i: imp_stack) (fenv: fun_env_stk),
      no_pushes_pops fenv i ->
      exists k,
        imp_frame_rule i fenv k k.
  Proof.
    induction 1; intros.
    - exists 0. constructor.
    - destruct H0 as (aframe & FRAME).
      exists (max k aframe).
      constructor.
      + assumption.
      + lia.
      + eapply aexp_frame_expansion. eassumption. lia.
    - destruct IHno_pushes_pops1 as (frame1 & FRAME1).
      destruct IHno_pushes_pops2 as (frame2 & FRAME2).
      exists (max frame1 frame2).
      econstructor.
      + eapply imp_frame_expansion. eassumption.
        lia.
      + rewrite Nat.add_sub. rewrite <- (Nat.add_sub _ frame2) at 2.
        eapply imp_frame_expansion. assumption. lia.
    - destruct H as (frameb & Fb).
      destruct IHno_pushes_pops1 as (frame1 & F1).
      destruct IHno_pushes_pops2 as (frame2 & F2).
      exists (max frameb (max frame1 frame2)).
      econstructor; [ | rewrite <- (Nat.add_sub _ frame1) at 2 | rewrite <- (Nat.add_sub _ frame2) at 2].
      + eapply bexp_frame_expansion. eassumption. lia.
      + eapply imp_frame_expansion. assumption. lia.
      + eapply imp_frame_expansion. assumption. lia.
    - destruct H as (frameb & FRAMEb).
      destruct IHno_pushes_pops as (framebody & FRAMEbody).
      exists (max frameb framebody).
      econstructor.
      + eapply bexp_frame_expansion. eassumption. lia.
      + rewrite <- (Nat.add_sub _ framebody) at 2. eapply imp_frame_expansion.
        assumption. lia.
  Qed.

  Require Import Imp_LangTrick.CodeCompiler.Correctness.CompilerCorrectHelpers.
  Lemma prepend_push_frame :
    forall (n: nat) (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
      imp_frame_rule i fenv (frame + n) frame' ->
      imp_frame_rule (prepend_push i n) fenv frame frame'.
  Proof using - no_pushes_pops_props.
    clear. induction n; intros.
    - unfold prepend_push. rewrite Nat.add_0_r in H. assumption.
    - simpl. rewrite prepend_push_commutes.
      econstructor.
      + econstructor.
      + eapply IHn.
        rewrite <- Nat.add_assoc. replace (1 + n) with (S n) by lia. assumption.
  Qed.

  Definition funcs_okay_too (funcs: list fun_Imp_Lang) (fenv: fun_env_stk) :=
    (Forall (fun func =>
              imp_frame_rule (StackLanguage.Body func)
                             fenv
                             (StackLanguage.Args func)
                             (StackLanguage.Return_pop func + StackLanguage.Args func) /\
                aexp_frame_rule (StackLanguage.Return_expr func)
                                fenv
                                (StackLanguage.Return_pop func + StackLanguage.Args func))
           (map fenv (map (Imp_LangTrick.Imp.Imp_LangTrickLanguage.Name) funcs))) 
    /\
      (forall func,
          (In func funcs -> 
           Imp_LangTrickLanguage.Name func = Name (fenv (Imp_LangTrickLanguage.Name (func)))))
    /\ (forall names, In names (map (Imp_LangTrick.Imp.Imp_LangTrickLanguage.Name) funcs) \/ fenv names = init_fenv_stk "id"). 

End CompiledImp_LangFrame.

Lemma frame_pure_of_return_expr :
  forall fenv_i f funcs fenv_s func,
    funcs_okay_too funcs fenv_s ->
    fenv_well_formed' funcs fenv_i ->
    func = fenv_i f ->
    In func funcs ->
    StackFrameBase.aexp_frame_rule
      (Return_expr (fenv_s f))
      fenv_s
      (Return_pop (fenv_s f) + Args (fenv_s f)).
Proof.
  intros fenv_i f funcs fenv_s func OKAY FENVWF EqFunc InFuncs. unfold fenv_well_formed' in FENVWF. destruct FENVWF as (NODUP & H & REST).
  unfold funcs_okay_too in OKAY. destruct OKAY as (FORALL & IN & RESTING).
  specialize (IN _ InFuncs).
  specialize (H _ _ EqFunc).

  pose proof (IN_MAP := in_map (Imp_LangTrickLanguage.Name) _ _ InFuncs).
  pose proof (IN_MAP_MAP := in_map fenv_s _ _ IN_MAP).
  pose proof (IN_FORALL := in_forall _ (fun func : fun_stk =>
            imp_frame_rule (Body func) fenv_s (Args func)
              (Return_pop func + Args func) /\
            aexp_frame_rule (Return_expr func) fenv_s
                            (Return_pop func + Args func)) (map fenv_s (map Imp_LangTrickLanguage.Name funcs)) _ IN_MAP_MAP).
  specialize (IN_FORALL FORALL). simpl in IN_FORALL.
  destruct REST as (A & F_EQ & C & D & E).
  specialize (E func f EqFunc InFuncs). invs E. destruct H0 as (F & G & J). 
  specialize (F_EQ _ InFuncs f). 
  pose proof @in_dec string string_dec f (map Imp_LangTrickLanguage.Name funcs). destruct H0.
  - specialize (F_EQ i eq_refl). rewrite <- F_EQ in *. eapply IN_FORALL.      
  - rewrite IN in *.  specialize (D f n). 
  (* unfold init_fenv in D.  *)
  (* rewrite D in *. *)
   unfold init_fenv in D.  unfold init_fenv in C. simpl in C.
  pose proof in_map_iff Imp_LangTrickLanguage.Name funcs f. destruct H0. 
  (* assert (exists x : fun_Imp_Lang, Imp_LangTrickLanguage.Name x = f /\ In x funcs). *)
  specialize (RESTING f). destruct RESTING. pose proof (n H2). contradiction. unfold init_fenv_stk in H2. simpl in H2. rewrite H2 in *. repeat constructor.    
Qed.

Local Definition rcomp_pure_P (funcs: list fun_Imp_Lang) (idents: list ident) (aimp_lang: aexp_Imp_Lang) (astk: aexp_stack): Prop :=
  forall fenv_i fenv_s dbenv nenv val,
    forall (OKfuncs: funcs_okay_too funcs fenv_s),
    fenv_well_formed' funcs fenv_i ->
    fun_app_well_formed fenv_i funcs aimp_lang ->
    var_map_wf_wrt_aexp idents aimp_lang ->
    (* fenv_s = compile_fenv fenv_i -> *)
    a_Imp_Lang aimp_lang dbenv fenv_i nenv val ->
    forall (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs),
      aexp_frame_rule astk fenv_s (Datatypes.length idents + Datatypes.length dbenv).

Lemma fun_imp_lang_equality :
  forall (func: fun_Imp_Lang),
    func = {|
             Imp_LangTrickLanguage.Name := Imp_LangTrickLanguage.Name func;
             Imp_LangTrickLanguage.Args := Imp_LangTrickLanguage.Args func;
             Ret := Ret func;
             Imp_LangTrickLanguage.Body := Imp_LangTrickLanguage.Body func |}.
Proof.
  destruct func. simpl. reflexivity.
Qed.

Lemma fun_Imp_Lang_name_must_be_the_same :
  forall (func: fun_Imp_Lang) (f: Base.ident) (fenv_i: fun_env)
    (funcs : list fun_Imp_Lang),
  forall
    (H4 : (forall (f : Base.ident) (func : fun_Imp_Lang),
              func = fenv_i f ->
              (In func funcs \/ func = init_fenv "id") /\
                fun_app_imp_well_formed fenv_i funcs (Imp_LangTrickLanguage.Body func) /\
                imp_has_variable (Ret func) (Imp_LangTrickLanguage.Body func)) /\
            NoDup (List.map Imp_LangTrickLanguage.Name funcs) /\
            (forall func : fun_Imp_Lang,
                In func funcs ->
                forall f : Base.ident,
                  func = fenv_i f -> f = Imp_LangTrickLanguage.Name func) /\
            In (init_fenv "id") funcs /\
            (forall f : Base.ident,
                ~ In f (List.map Imp_LangTrickLanguage.Name funcs) ->
                fenv_i f = init_fenv "id"))
    (Heqfunc : func = fenv_i f)
    (H11 : In func funcs),
    func =
      {|
        Imp_LangTrickLanguage.Name := f;
        Imp_LangTrickLanguage.Args := Imp_LangTrickLanguage.Args func;
        Ret := Imp_LangTrickLanguage.Ret func;
        Imp_LangTrickLanguage.Body := Imp_LangTrickLanguage.Body func
      |}.
Proof.
  intros.
  simpl.
  destruct H4 as (_ & _ & INFUNC & _). specialize (INFUNC _ H11 _ Heqfunc). rewrite INFUNC.

  eapply fun_imp_lang_equality.
Qed.

Lemma in_and_not_in_implies_not_equal :
  forall (A: Type) (x x': A) (xs: list A),
    In x xs ->
    ~ (In x' xs) ->
    x <> x'.
Proof.
  unfold not; intros.
  rewrite <- H1 in H0. apply H0 in H. assumption.
Qed.

Lemma in_implies_find_index_rel :
  forall idents x,
    In x idents ->
    NoDup idents ->
    exists n,
      find_index_rel idents x (Some n).
Proof.
  induction idents; intros.
  - invs H.
  - invs H.
    + exists 0. econstructor. reflexivity.
    + invs H0. apply in_and_not_in_implies_not_equal with (x := x) (x' := a) in H4; [ | assumption .. ]. apply IHidents in H1; [ | assumption ]. destruct H1. exists (S x0).
      constructor.
      * assumption.
      * assumption.
Qed.

Ltac eval_prop_rel_inversion num_repeats :=
  (do
    num_repeats (
         try match goal with
             | [ H : eval_prop_rel ?func ?prop |- _ ] =>
                 let n := numgoals in
                 invc H;
                 let n' := numgoals in
                 guard n = n'           
             end)).

Ltac bexp_inversion :=
  match goal with
  | [ H : bexp_stack_sem ?bexp _ _ _ |- _ ] =>
      match bexp with
      | True_Stk => fail
      | False_Stk => fail
      | _ => invc H
      end
  | [ H : b_Imp_Lang ?bexp _ _ _ _ |- _ ] =>
      match bexp with
      | TRUE_Imp_Lang => fail
      | FALSE_Imp_Lang => fail
      | _ => invc H
      end
  end.