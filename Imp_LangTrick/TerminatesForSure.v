From Coq Require Import List Arith String Psatz.

From Imp_LangTrick Require Import Imp_LangTrickLanguage ParamsWellFormed StackLangTheorems ParamsWellFormedMutInd ReflectionMachinery.

Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

(** Do not delete this file *)

(* really, imp_lang has no non-terminating functions *)
Inductive imp_lang_has_no_functions (fenv: fun_env) : aexp_Imp_Lang -> Prop :=
| const_has_no_functions :
  forall n,
    imp_lang_has_no_functions fenv (CONST_Imp_Lang n)
| var_has_no_functions :
  forall x,
    imp_lang_has_no_functions fenv (VAR_Imp_Lang x)
| param_has_no_functions :
  forall k,
    imp_lang_has_no_functions fenv (PARAM_Imp_Lang k)
| plus_has_no_functions :
  forall a1 a2,
    imp_lang_has_no_functions fenv a1 ->
    imp_lang_has_no_functions fenv a2 ->
    imp_lang_has_no_functions fenv (PLUS_Imp_Lang a1 a2)
| minus_has_no_functions :
  forall a1 a2,
    imp_lang_has_no_functions fenv a1 ->
    imp_lang_has_no_functions fenv a2 ->
    imp_lang_has_no_functions fenv (MINUS_Imp_Lang a1 a2)
| app_has_no_functions_always_terminating :
  forall f args,
    args_has_no_functions fenv args ->
    (forall nenv dbenv,
      exists nenv',
        a_Imp_Lang (APP_Imp_Lang f args) dbenv fenv nenv nenv') ->
    imp_lang_has_no_functions fenv (APP_Imp_Lang f args)
with args_has_no_functions (fenv: fun_env) : (list aexp_Imp_Lang) -> Prop :=
| nil_has_no_functions :
  args_has_no_functions fenv nil
| cons_has_no_functions :
  forall arg args,
    imp_lang_has_no_functions fenv arg ->
    args_has_no_functions fenv args ->
    args_has_no_functions fenv (arg :: args).

Scheme imp_lang_has_no_functions_mind := Induction for imp_lang_has_no_functions Sort Prop
    with args_has_no_functions_mind := Induction for args_has_no_functions Sort Prop.

Combined Scheme has_no_functions_mut_ind from imp_lang_has_no_functions_mind, args_has_no_functions_mind.

Inductive bexp_Imp_Langs_aexps (phi: aexp_Imp_Lang -> Prop): bexp_Imp_Lang -> Prop :=
| bDa_true :
  bexp_Imp_Langs_aexps phi TRUE_Imp_Lang
| bDa_false :
  bexp_Imp_Langs_aexps phi FALSE_Imp_Lang
| bDa_neg :
  forall b,
    bexp_Imp_Langs_aexps phi b ->
    bexp_Imp_Langs_aexps phi (NEG_Imp_Lang b)
| bDa_and :
  forall b1 b2,
    bexp_Imp_Langs_aexps phi b1 ->
    bexp_Imp_Langs_aexps phi b2 ->
    bexp_Imp_Langs_aexps phi (AND_Imp_Lang b1 b2)
| bDa_or :
  forall b1 b2,
    bexp_Imp_Langs_aexps phi b1 ->
    bexp_Imp_Langs_aexps phi b2 ->
    bexp_Imp_Langs_aexps phi (OR_Imp_Lang b1 b2)
| bDa_leq :
  forall a1 a2,
    phi a1 ->
    phi a2 ->
    bexp_Imp_Langs_aexps phi (LEQ_Imp_Lang a1 a2).

Inductive imp_Imp_Langs_aexps (phi: aexp_Imp_Lang -> Prop) : imp_Imp_Lang -> Prop :=
| iDa_skip :
  imp_Imp_Langs_aexps phi SKIP_Imp_Lang
| iDa_assign :
  forall x a,
    phi a ->
    imp_Imp_Langs_aexps phi (ASSIGN_Imp_Lang x a)
| iDa_seq :
  forall i1 i2,
    imp_Imp_Langs_aexps phi i1 ->
    imp_Imp_Langs_aexps phi i2 ->
    imp_Imp_Langs_aexps phi (SEQ_Imp_Lang i1 i2)
| iDa_if :
  forall b i1 i2,
    bexp_Imp_Langs_aexps phi b ->
    imp_Imp_Langs_aexps phi i1 ->
    imp_Imp_Langs_aexps phi i2 ->
    imp_Imp_Langs_aexps phi (IF_Imp_Lang b i1 i2)
| iDa_while :
  forall b i,
    bexp_Imp_Langs_aexps phi b ->
    imp_Imp_Langs_aexps phi i ->
    imp_Imp_Langs_aexps phi (WHILE_Imp_Lang b i).

Inductive imp_terminates (fenv: fun_env): imp_Imp_Lang -> Prop :=
| imp_terminates_skip :
  imp_terminates fenv SKIP_Imp_Lang
| imp_terminates_assign :
  forall x a,
    imp_lang_has_no_functions fenv a ->
    imp_terminates fenv (ASSIGN_Imp_Lang x a)
| imp_terminates_seq :
  forall i1 i2,
    imp_terminates fenv i1 ->
    imp_terminates fenv i2 ->
    imp_terminates fenv (SEQ_Imp_Lang i1 i2)
| imp_terminates_if :
  forall b i1 i2,
    bexp_Imp_Langs_aexps (imp_lang_has_no_functions fenv) b ->
    imp_terminates fenv i1 ->
    imp_terminates fenv i2 ->
    imp_terminates fenv (IF_Imp_Lang b i1 i2)
| imp_terminates_while :
  forall b i,
    (forall nenv dbenv,
        b_Imp_Lang b dbenv fenv nenv true ->
        exists nenv',
          i_Imp_Lang (WHILE_Imp_Lang b i) dbenv fenv nenv nenv') ->
    bexp_Imp_Langs_aexps (imp_lang_has_no_functions fenv) b ->
    imp_terminates fenv i ->
    imp_terminates fenv (WHILE_Imp_Lang b i).


Lemma nth_error_some_lt_length :
  forall (l: list nat) (k: nat),
    k < Datatypes.length l ->
    exists (x: nat),
      nth_error l k = Some x.
Proof.
  induction l; intros.
  - destruct k. invs H.
    invs H.
  - simpl in H. destruct k.
    + exists a. simpl. reflexivity.
    + eapply Arith_prebase.lt_S_n in H.
      eapply IHl in H. destruct H as (x & NTH).
      exists x. simpl. assumption.
Qed.
  
Lemma has_no_functions_always_terminates :
  forall fenv,
  (forall (a: aexp_Imp_Lang),
      imp_lang_has_no_functions fenv a ->
      forall nenv dbenv,
        all_params_ok_aexp (Datatypes.length dbenv) a ->
        exists n,
          a_Imp_Lang a dbenv fenv nenv n) /\
    (forall (args: list aexp_Imp_Lang),
        args_has_no_functions fenv args ->
        forall nenv dbenv,
          all_params_ok_args (Datatypes.length dbenv) args ->
          exists vals,
            args_Imp_Lang args dbenv fenv nenv vals).
Proof.
  intros fenv.
  pose (fun (a: aexp_Imp_Lang) =>
        fun (h: imp_lang_has_no_functions fenv a) =>
          forall nenv dbenv,
            all_params_ok_aexp (Datatypes.length dbenv) a ->
            exists n,
              a_Imp_Lang a dbenv fenv nenv n) as P.
  pose (fun (args: list aexp_Imp_Lang) =>
        fun (h: args_has_no_functions fenv args) =>
          forall nenv dbenv,
            all_params_ok_args (Datatypes.length dbenv) args ->
            exists vals,
              args_Imp_Lang args dbenv fenv nenv vals) as P0.

  apply (has_no_functions_mut_ind fenv P P0); unfold P, P0; intros.
  - exists n. constructor.
  - exists (nenv x). constructor. reflexivity.
  - invs H. eapply nth_error_some_lt_length in H2. destruct H2 as (x & NTH).
    exists x. econstructor.
    invs H. lia.
    assumption.
  - invs H1. eapply H in H5. eapply H0 in H6. destruct H5 as (n1 & A1). destruct H6 as (n2 & A2).
    exists (n1 + n2). econstructor. eassumption. eassumption.
  - invc H1. eapply H in H5. eapply H0 in H6. destruct H5 as (n1 & A1). destruct H6 as (n2 & A2). exists (n1 - n2). constructor.
    eassumption. eassumption.
  - invs H0.
    eapply H in H3.
    specialize (e nenv dbenv).
    destruct e as (n' & APP).
    exists n'.
    eassumption.
  - exists nil. constructor.
  - invc H1. eapply H in H5. eapply H0 in H6.
    destruct H5 as (n & ARG).
    destruct H6 as (vals & ARGS).
    exists (n :: vals). econstructor.
    eassumption. eassumption.
    Unshelve.
    + eassumption.
    (* + eassumption. *)
Defined.

Definition aexp_terminates (fenv: fun_env) (a: aexp_Imp_Lang) :=
  forall nenv dbenv,
    all_params_ok_aexp (Datatypes.length dbenv) a ->
    exists n,
      a_Imp_Lang a dbenv fenv nenv n.

Lemma aexp_has_no_functions_always_terminates :
  forall fenv,
  (forall a: aexp_Imp_Lang,
      imp_lang_has_no_functions fenv a ->
      forall nenv dbenv,
        all_params_ok_aexp (Datatypes.length dbenv) a ->
        exists n,
          a_Imp_Lang a dbenv fenv nenv n).
Proof.
  eapply has_no_functions_always_terminates.
Defined.

Lemma bexp_has_no_functions_always_terminates :
  forall fenv,
  forall (b: bexp_Imp_Lang),
    bexp_Imp_Langs_aexps (imp_lang_has_no_functions fenv) b ->
    forall nenv dbenv,
      all_params_ok_bexp (Datatypes.length dbenv) b ->
      exists v,
        b_Imp_Lang b dbenv fenv nenv v.
Proof.
  induction b; intros.
  - exists true. constructor.
  - exists false. constructor.
  - invc H0. invc H. eapply IHb in H3; [ | eassumption ].
    destruct H3 as (v & B). exists (negb v). econstructor. eassumption.
  - invc H. invc H0. eapply IHb1 in H3; [ | eassumption ]. eapply IHb2 in H4; [ | eassumption ].
    destruct H3 as (v1 & B1).
    destruct H4 as (v2 & B2).
    exists (andb v1 v2). constructor; eassumption.
  - invc H. invc H0. eapply IHb1 in H3; [ | eassumption ]. eapply IHb2 in H4; [ | eassumption ].
    destruct H3 as (v1 & B1).
    destruct H4 as (v2 & B2).
    exists (orb v1 v2).
    econstructor; eassumption.
  - invc H. invc H0. eapply aexp_has_no_functions_always_terminates in H3; [ | eassumption ]. eapply aexp_has_no_functions_always_terminates in H4; [ | eassumption ].
    destruct H3 as (n1 & A1). destruct H4 as (n2 & A2). exists (Nat.leb n1 n2).
    econstructor; eassumption.
Defined.

Definition imp_terminates_prop_def (fenv: fun_env) (i: imp_Imp_Lang) :=
  forall nenv dbenv,
    all_params_ok (Datatypes.length dbenv) i ->
    exists nenv',
      i_Imp_Lang i dbenv fenv nenv nenv'.

Lemma imp_has_no_functions_always_terminates :
  forall fenv,
  forall (i: imp_Imp_Lang),
    imp_terminates fenv i ->
    forall nenv dbenv,
      all_params_ok (Datatypes.length dbenv) i ->
      exists nenv',
        i_Imp_Lang i dbenv fenv nenv nenv'.
Proof.
  induction i; intros.
  - invc H. invc H0. eapply IHi1 in H5; [ | eassumption ]. eapply IHi2 in H6; [ | eassumption ]. eapply bexp_has_no_functions_always_terminates in H4; [ | eassumption ].
    destruct H4 as (v & B).
    destruct v eqn:V.
    + destruct H5 as (nenv' & I1).
      exists nenv'. eapply Imp_Lang_if_true. eassumption. eassumption.
    + destruct H6 as (nenv' & I2).
      exists nenv'. eapply Imp_Lang_if_false. eassumption. eassumption.
  - exists nenv. constructor.
  - invc H0. invc H.
    eapply IHi in H6; [ | eassumption ].
    eapply bexp_has_no_functions_always_terminates in H3; [ | eassumption ].
    destruct H3 as (v & B).
    destruct v eqn:V.
    + eapply H2. eassumption.
    + exists nenv. eapply Imp_Lang_while_done. eassumption.
  - invc H. invc H0. eapply aexp_has_no_functions_always_terminates in H2; [ | eassumption ]. destruct H2 as (n & A).
    exists (update x n nenv). econstructor. eassumption.
  - invc H. invc H0. eapply IHi1 in H3; [ | eassumption ].  destruct H3 as (nenv' & I1). eapply IHi2 in H4; [ | eassumption ]. destruct H4 as (nenv'' & I2).
    exists nenv''. econstructor.
    eassumption.
    eapply I2.
    Unshelve.
    + eassumption.
    (* + eassumption. *)
Defined.

Lemma terminating_args :
  forall (args: list aexp_Imp_Lang) (fenv: fun_env),
    Forall (fun arg : aexp_Imp_Lang => aexp_terminates fenv arg) args ->
    forall nenv dbenv,
    forall (PARAMS: all_params_ok_args (Datatypes.length dbenv) args),
    exists vals,
      args_Imp_Lang args dbenv fenv nenv vals.
Proof.
  induction args; intros.
  - exists nil. econstructor.
  - invs H.
    eapply IHargs in H3. destruct H3 as (vals' & ARGSargs).
    unfold aexp_terminates in H2.
    invs PARAMS. specialize (H2 nenv dbenv H4). destruct H2 as (v & A).
    exists (v :: vals'). econstructor.
    eassumption. eassumption.
    invs PARAMS. eassumption.
Qed.

Lemma args_Imp_Lang_same_length :
  forall (fenv: fun_env) dbenv nenv args vals,
    args_Imp_Lang args dbenv fenv nenv vals ->
    Datatypes.length args = Datatypes.length vals.
Proof.
Admitted.

Lemma terminating_functions :
  forall (args: list aexp_Imp_Lang) (i: imp_Imp_Lang) (fenv: fun_env) (f: ident),
    forall (LEN: Datatypes.length args = Imp_LangTrickLanguage.Args (fenv f)),
    forall (BODY: Imp_LangTrickLanguage.Body (fenv f) = i)
      (ARGS: Forall (fun arg => aexp_terminates fenv arg) args)
      (PARAMS: all_params_ok (Imp_LangTrickLanguage.Args (fenv f)) i)
      (ENOUGH: Imp_LangTrickLanguage.Args (fenv f) <= Datatypes.length args)
      (TERM: imp_terminates fenv i),
    aexp_terminates fenv (APP_Imp_Lang f args).
Proof.
  destruct args; intros; unfold aexp_terminates; intros nenv dbenv OK.
  - pose proof (ALWAYS:=imp_has_no_functions_always_terminates fenv i TERM).
    specialize (ALWAYS init_nenv nil).
    simpl in ENOUGH. invs ENOUGH.  rewrite H0 in PARAMS. simpl in ALWAYS. specialize (ALWAYS PARAMS).
    destruct ALWAYS as (nenv' & I).
    exists (nenv' (Imp_LangTrickLanguage.Ret (fenv f))).
    econstructor; try reflexivity.
    + simpl. assumption.
    + econstructor.
    + eassumption.
  - invs ARGS. unfold aexp_terminates in H1. invs OK.
    eapply terminating_args in ARGS; [ | invs H3; eassumption ].
    destruct ARGS as (vals & ARGS).
    pose proof (ALWAYS := imp_has_no_functions_always_terminates fenv _ TERM).
    specialize (ALWAYS init_nenv vals).
    pose proof (SAME := args_Imp_Lang_same_length _ _ _ _ _ ARGS).
    rewrite SAME in ENOUGH.
    pose proof (IMP_OK := imp_more_params_is_more_okay).
    specialize (IMP_OK _ _ PARAMS).
    specialize (IMP_OK _ ENOUGH).
    specialize (ALWAYS IMP_OK).
    destruct ALWAYS as (nenv' & IMP).
    exists (nenv' (Ret (fenv f))).
    econstructor; try reflexivity.
    + symmetry
      . eassumption.
    + eassumption.
    + eassumption.
Qed.    


Fixpoint aexp_has_no_functions_constructor (a: aexp_Imp_Lang) (fenv: fun_env): option (imp_lang_has_no_functions fenv a) :=
  match a as a' return (option (imp_lang_has_no_functions fenv a')) with
  | CONST_Imp_Lang n =>
      Some (const_has_no_functions fenv n)
  | VAR_Imp_Lang x =>
      Some (var_has_no_functions fenv x)
  | PARAM_Imp_Lang k =>
      Some (param_has_no_functions fenv k)
  | PLUS_Imp_Lang a1 a2 =>
      match (aexp_has_no_functions_constructor a1 fenv) with
      | Some a1pf =>
          match (aexp_has_no_functions_constructor a2 fenv) with
          | Some a2pf =>
              Some (plus_has_no_functions fenv a1 a2 a1pf a2pf)
          | None =>
              None
          end
      | None =>
          None
      end
  | MINUS_Imp_Lang a1 a2 =>
      match (aexp_has_no_functions_constructor a1 fenv) with
      | Some a1pf =>
          match (aexp_has_no_functions_constructor a2 fenv) with
          | Some a2pf =>
              Some (minus_has_no_functions fenv a1 a2 a1pf a2pf)
          | None =>
              None
          end
      | None =>
          None
      end
  | _ =>
      None
  end.

Fixpoint args_has_no_functions_constructor (fenv: fun_env) (args: list aexp_Imp_Lang): option (args_has_no_functions fenv args) :=
  match args as args' return (option (args_has_no_functions fenv args')) with
  | nil =>
      Some (nil_has_no_functions fenv)
  | (arg :: args') =>
      match (aexp_has_no_functions_constructor arg fenv) with
      | Some argpf =>
          match (args_has_no_functions_constructor fenv args') with
          | Some argspf =>
              Some (cons_has_no_functions fenv arg args' argpf argspf)
          | _ => None
          end
      | _ => None
      end
  end.

Ltac prove_args_terminates :=
  match goal with
  | [ |- exists vals, args_Imp_Lang ?args ?dbenv ?fenv ?nenv _ ] =>
      eapply has_no_functions_always_terminates; prove_args_terminates
  | [ |- args_has_no_functions ?fenv ?args ] =>
      exact (optionOut (args_has_no_functions fenv args) (args_has_no_functions_constructor fenv args))
  end.
                                          

Ltac prove_aexp_terminates :=
  repeat match goal with
         | [ |- imp_lang_has_no_functions ?fenv (APP_Imp_Lang ?f ?args) ] =>
             econstructor; try eassumption;
             try prove_args_terminates
         | [ |- imp_lang_has_no_functions ?fenv ?a] =>
             exact (optionOut (imp_lang_has_no_functions fenv a) (aexp_has_no_functions_constructor a fenv))
         | [ |- exists n, a_Imp_Lang ?a ?dbenv ?fenv ?nenv _ ] =>
             eapply aexp_has_no_functions_always_terminates
         end.

Fixpoint bexp_has_no_functions_constructor (b: bexp_Imp_Lang) (fenv: fun_env): option (bexp_Imp_Langs_aexps (imp_lang_has_no_functions fenv) b) :=
  match b as b' return (option (bexp_Imp_Langs_aexps (imp_lang_has_no_functions fenv) b'))
  with
  | TRUE_Imp_Lang =>
      Some (bDa_true (imp_lang_has_no_functions fenv))
  | FALSE_Imp_Lang =>
      Some (bDa_false (imp_lang_has_no_functions fenv))
  | NEG_Imp_Lang b =>
      match (bexp_has_no_functions_constructor b fenv) with
      | Some bpf =>
          Some (bDa_neg (imp_lang_has_no_functions fenv) b bpf)
      | None =>
          None
      end
  | AND_Imp_Lang b1 b2 =>
      match (bexp_has_no_functions_constructor b1 fenv) with
      | Some b1pf =>
          match (bexp_has_no_functions_constructor b2 fenv) with
          | Some b2pf =>
              Some (bDa_and (imp_lang_has_no_functions fenv) b1 b2 b1pf b2pf)
          | None =>
              None
          end
      | None =>
          None
      end
  | OR_Imp_Lang b1 b2 =>
      match (bexp_has_no_functions_constructor b1 fenv) with
      | Some b1pf =>
          match (bexp_has_no_functions_constructor b2 fenv) with
          | Some b2pf =>
              Some (bDa_or (imp_lang_has_no_functions fenv) b1 b2 b1pf b2pf)
          | None =>
              None
          end
      | None =>
          None
      end
  | LEQ_Imp_Lang a1 a2 =>
      match (aexp_has_no_functions_constructor a1 fenv) with
      | Some a1pf =>
          match (aexp_has_no_functions_constructor a2 fenv) with
          | Some a2pf =>
              Some (bDa_leq (imp_lang_has_no_functions fenv) a1 a2 a1pf a2pf)
          | None =>
              None
          end
      | None =>
          None
      end
  end.

Ltac prove_bexp_terminates :=
  repeat match goal with
         | [ |- bexp_Imp_Langs_aexps (imp_lang_has_no_functions ?fenv) ?b ] =>
             exact (optionOut (bexp_Imp_Langs_aexps (imp_lang_has_no_functions fenv) b) (bexp_has_no_functions_constructor b fenv))
         | [ |- exists v, b_Imp_Lang ?b ?dbenv ?fenv ?nenv _ ] =>
             eapply bexp_has_no_functions_always_terminates
         end.


Fixpoint imp_has_no_functions_constructor (fenv: fun_env) (i: imp_Imp_Lang) : option (imp_terminates fenv i) :=
  match i with
  | SKIP_Imp_Lang =>
      Some (imp_terminates_skip fenv)
  | ASSIGN_Imp_Lang x a =>
      match (aexp_has_no_functions_constructor a fenv) with
      | Some apf =>
          Some (imp_terminates_assign fenv x a apf)
      | None =>
          None
      end
  | SEQ_Imp_Lang i1 i2 =>
      match (imp_has_no_functions_constructor fenv i1) with
      | Some i1pf =>
          match (imp_has_no_functions_constructor fenv i2) with
          | Some i2pf =>
              Some (imp_terminates_seq fenv i1 i2 i1pf i2pf)
          | None =>
              None
          end
      | None =>
          None
      end
  | IF_Imp_Lang b i1 i2 =>
      match (bexp_has_no_functions_constructor b fenv) with
      | Some bpf =>
          match (imp_has_no_functions_constructor fenv i1) with
          | Some i1pf =>
              match (imp_has_no_functions_constructor fenv i2) with
              | Some i2pf =>
                  Some (imp_terminates_if fenv b i1 i2 bpf i1pf i2pf)
              | None =>
                  None
              end
          | None =>
              None
          end
      | None =>
          None
      end
  | WHILE_Imp_Lang b i =>
      None
  end.

Ltac prove_imp_terminates :=
  match goal with
  | [ |- imp_terminates ?fenv ?i ] =>
      exact (optionOut (imp_terminates fenv i) (imp_has_no_functions_constructor fenv i))
  | [ |- exists nenv', i_Imp_Lang ?i ?dbenv ?fenv ?nenv _ ] =>
      eapply imp_has_no_functions_always_terminates; try eassumption; try prove_imp_terminates
  end.

Definition always_terminates (fenv: fun_env) (i: imp_Imp_Lang) : option (forall nenv dbenv,
    all_params_ok (Datatypes.length dbenv) i ->
    exists nenv',
      i_Imp_Lang i dbenv fenv nenv nenv') :=
  match (imp_has_no_functions_constructor fenv i) with
  | Some ipf =>
      Some (imp_has_no_functions_always_terminates fenv _ ipf)
  | None =>
      None
  end.
