From Coq Require Import List String Arith Program.Equality.

From Imp_LangTrick Require Import Imp_LangTrickLanguage ImpVarMap ReflectionMachinery.

Lemma aexp_has_variable_app_inversion :
  forall x f args,
    aexp_has_variable x (APP_Imp_Lang f args) ->
    args_has_variable x args.
Proof.
  intros. inversion H. eassumption.
Qed.


Program Fixpoint construct_aexp_has_variable (x: ident) (a: aexp_Imp_Lang) : option (aexp_has_variable x a) :=
  match a with
  | _ => _
  end.
Next Obligation.
  
  eapply (aexp_Imp_Lang_rec2 (fun a =>
                                option (aexp_has_variable x a))); intros.
  - eapply None.
  - pose proof (xdec := Bool.bool_dec (String.eqb x x0) true). destruct xdec.
    + eapply (Some (AexpHasVarVar x x0 e)).
    + eapply None.
  - eapply None.
  - destruct H as [IHa1' | ]; [eapply (Some (AexpHasVarPlus__left _ _ _ IHa1')) | ]; destruct H0; match goal with
                         | [ H: aexp_has_variable _ _ |- _ ] =>
                             idtac
                         | [ |- _ ] => eapply None
                         end.
    eapply (Some (AexpHasVarPlus__right _ _ _ a0)).
  - destruct H as [IHa1' | ]; [eapply (Some (AexpHasVarMinus__left _ _ _ IHa1')) | ]; destruct H0; match goal with
                         | [ H: aexp_has_variable _ _ |- _ ] =>
                             idtac
                         | [ |- _ ] => eapply None
                         end.
    eapply (Some (AexpHasVarMinus__right _ _ _ a0)).
  - induction H; intros.
    + eapply None.
    + destruct p, IHSForall.
      * eapply (Some (AexpHasVarApp _ _ _ (ArgsHasVarFirst _ _ l a0))).
      * eapply (Some (AexpHasVarApp _ _ _ (ArgsHasVarFirst _ _ l a0))).
      * eapply aexp_has_variable_app_inversion in a0.
        eapply (Some (AexpHasVarApp _ _ _ (ArgsHasVarRest _ x0 _ a0))).
      * eapply None.
Defined.


                  
Program Fixpoint construct_bexp_has_variable (x: ident) (b: bexp_Imp_Lang) : option (bexp_has_variable x b) :=
  match b with
  | _ => _
  end.
Next Obligation.
  induction b; intros.
  - eapply None.
  - eapply None.
  - destruct IHb; [ | eapply None].
    eapply (Some (BexpHasVarNeg _ _ b0)).
  - destruct IHb1; [ | destruct IHb2 ];
      match goal with
      | [ H: bexp_has_variable _ b1 |- _ ] =>
          eapply (Some (BexpHasVarAnd__left _ _ _ H))
      | [ H: bexp_has_variable _ b2 |- _ ] =>
          eapply (Some (BexpHasVarAnd__right _ _ _ H))
      | [ |- _ ] =>
          eapply None
      end.
  - destruct IHb1; [ | destruct IHb2 ];
      match goal with
      | [ H: bexp_has_variable _ b1 |- _ ] =>
          eapply (Some (BexpHasVarOr__left _ _ _ H))
      | [ H: bexp_has_variable _ b2 |- _ ] =>
          eapply (Some (BexpHasVarOr__right _ _ _ H))
      | [ |- _ ] =>
          eapply None
      end.
  - pose proof (construct_aexp_has_variable x a1).
    pose proof (construct_aexp_has_variable x a2).
    destruct H; [ | destruct H0 ];
      match goal with
      | [ H: aexp_has_variable _ a1 |- _ ] =>
          eapply (Some (BexpHasVarLeq__left _ _ _ H))
      | [ H: aexp_has_variable _ a2 |- _ ] =>
          eapply (Some (BexpHasVarLeq__right _ _ _ H))
      | [ |- _ ] =>
          eapply None
      end.
Defined.

Program Fixpoint construct_imp_has_variable (x: ident) (i: imp_Imp_Lang) : option (imp_has_variable x i) :=
  match i with
  | _ => _
  end.
Next Obligation.
  induction i; intros.
  - pose proof (Hasb := construct_bexp_has_variable x b).
    destruct Hasb; [ | destruct IHi1; [ | destruct IHi2 ]];
      match goal with
      | [ H: bexp_has_variable _ b |- _ ] =>
          eapply (Some (ImpHasVarIf__cond _ _ _ _ H))
      | [ H: imp_has_variable _ i1 |- _ ] =>
          eapply (Some (ImpHasVarIf__then _ _ _ _ H))
      | [ H: imp_has_variable _ i2 |- _ ] =>
          eapply (Some (ImpHasVarIf__else _ _ _ _ H))
      | [ |- _ ] => eapply None
      end.
  - eapply None.
  - pose proof (Bhas := construct_bexp_has_variable x b).
    destruct Bhas; [ | destruct IHi ];
      match goal with
      | [ H: bexp_has_variable _ b |- _ ] =>
          eapply (Some (ImpHasVarWhile__cond _ _ _ H))
      | [ H: imp_has_variable _ i |- _ ] =>
          eapply (Some (ImpHasVarWhile__body _ _ _ H))
      | [ |- _ ] =>
          eapply None
      end.
  - pose proof (Ahas := construct_aexp_has_variable x a).
    pose proof (Eq := (Bool.bool_dec (String.eqb x x0) true)).
    destruct Eq; [ | destruct Ahas ];
      match goal with
      | [ H: _ = _ |- _ ] =>
          eapply (Some (ImpHasVarAssignee _ _ _ H))
      | [ H: aexp_has_variable _ a |- _ ] =>
          eapply (Some (ImpHasVarAssigned _ _ _ H))
      | |- _ =>
          eapply None
      end.
  - destruct IHi1; [ | destruct IHi2 ];
      match goal with
      | [ H: imp_has_variable _ i1 |- _ ] =>
          eapply (Some (ImpHasVarSeq__left _ _ _ H))
      | [ H: imp_has_variable _ i2 |- _ ] =>
          eapply (Some (ImpHasVarSeq__right _ _ _ H))
      | |- _ =>
          eapply None
      end.
Defined.

Ltac prove_aexp_has_variable :=
  match goal with
  | [ |- aexp_has_variable ?x ?a ] =>
      exact (optionOut (aexp_has_variable x a) (construct_aexp_has_variable x a))
  end.

Ltac prove_bexp_has_variable :=
  match goal with
  | [ |- bexp_has_variable ?x ?b ] =>
      exact (optionOut (bexp_has_variable x b) (construct_bexp_has_variable x b))
  end.

Ltac prove_imp_has_variable :=
  match goal with
  | [ |- imp_has_variable ?x ?i ] =>
      exact (optionOut (imp_has_variable x i) (construct_imp_has_variable x i))
  end.
