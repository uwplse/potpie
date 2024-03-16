From Imp_LangTrick Require Import Imp_LangTrickLanguage LogicPropDec StackLangTheorems Imp_LangLogicHelpers.
From Coq Require Import Eqdep_dec String.

(** NOTE: copied from ProofCompilerHelpers.v, duplicates in there should be deleted *)

Ltac not_eq := right; intros neq; invs neq.

Lemma imp_Imp_Lang_dec :
  forall (i1 i2: imp_Imp_Lang),
    {i1 = i2} + {i1 <> i2}.
Proof.
  induction i1; induction i2; try (left; reflexivity);
    match goal with
    | [ |- { ?l = ?r } + { _ } ] =>
        match l with
        | ?imp_lang_op _ _ _ =>
            match r with
            | imp_lang_op _ _ _ =>
                idtac
            | _ =>
                not_eq; try discrim_neq
            end
        | ?imp_lang_op _ _ =>
            match r with
            | imp_lang_op _ _ =>
                idtac
            | _ =>
                not_eq; try discrim_neq
            end
        | ?imp_lang_op =>
            not_eq; try discrim_neq
        end
    end.
  - pose proof (bexp_Imp_Lang_dec).
    specialize (H b b0).
    specialize (IHi1_1 i2_1).
    specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2, H; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (IHi1 i2).
    pose proof (bexp_Imp_Lang_dec).
    specialize (H b b0).
    destruct IHi1, H; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (string_dec x x0).
    specialize (aexp_Imp_Lang_dec a a0).
    intros.
    destruct H, H0; try (subst; left; reflexivity); not_eq; try discrim_neq.
  - specialize (IHi1_1 i2_1).
    specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2; try (subst; left; reflexivity); not_eq; try discrim_neq.
Qed.

Lemma UIP_refl_bexp :
  forall b: bexp_Imp_Lang,
  forall H: b = b,
    H = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ bexp_Imp_Lang_dec b b eq_refl H).
Qed.

Lemma UIP_imp_refl :
  forall (i: imp_Imp_Lang)
    (p: i = i),
    p = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ imp_Imp_Lang_dec i i eq_refl p).
Qed.

(** There is only ever one fenv that we are using. *)
Axiom UIP_fun_env_refl :
  forall (fenv: fun_env)
    (p: fenv = fenv),
    p = eq_refl.

Local Open Scope type_scope.

Lemma UIP_aexp_refl :
  forall (a: aexp_Imp_Lang)
    (p: a = a),
    p = eq_refl.
Proof.
  intros. symmetry. exact (@UIP_dec _ aexp_Imp_Lang_dec a a eq_refl p).
Qed.

Lemma fun_Imp_Lang_eq_dec :
  forall (f1 f2: fun_Imp_Lang),
    {f1 = f2} + {f1 <> f2}.
Proof.
  intros. destruct f1. destruct f2.
  pose proof (NAME := string_dec Name Name0).
  pose proof (IMP_LANG := imp_Imp_Lang_dec Body Body0).
  pose proof (ARGS := PeanoNat.Nat.eq_dec Args Args0).
  pose proof (RET := string_dec Ret Ret0).
  destruct NAME as [NAME | NAME], IMP_LANG as [IMP_LANG|IMP_LANG], ARGS as [ARGS|ARGS], RET as [RET|RET]; [subst | subst; not_eq; discrim_neq .. ].
  left. reflexivity.
Qed.
