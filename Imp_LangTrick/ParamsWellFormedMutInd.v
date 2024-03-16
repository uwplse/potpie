From Coq Require Import List String.

From Imp_LangTrick Require Import Imp_LangTrickLanguage ParamsWellFormed.

Local Open Scope string_scope.
Local Open Scope list_scope.

Scheme all_params_ok_imp_mut := Induction for all_params_ok Sort Prop
    with all_params_ok_aexp_mut := Induction for all_params_ok_aexp Sort Prop
                                  with all_params_ok_bexp_mut := Induction for all_params_ok_bexp Sort Prop
                                  with all_params_ok_args_mut := Induction for all_params_ok_args Sort Prop.

Combined Scheme all_params_ok_mut_ind from all_params_ok_imp_mut, all_params_ok_aexp_mut, all_params_ok_bexp_mut, all_params_ok_args_mut.

Check all_params_ok_mut_ind.

(* Section all_params_ok_mutual_induction_section. *)
  Local Definition all_params_ok_mut_ind_theorem
      (P: nat -> imp_Imp_Lang -> Prop)
      (P0: nat -> aexp_Imp_Lang -> Prop)
      (P1: nat -> bexp_Imp_Lang -> Prop)
      (P2: nat -> list aexp_Imp_Lang -> Prop) :=
        (forall (n : nat) (i : imp_Imp_Lang) (a : all_params_ok n i), P n i) /\
       (forall (n : nat) (a : aexp_Imp_Lang) (a0 : all_params_ok_aexp n a), P0 n a) /\
       (forall (n : nat) (b : bexp_Imp_Lang) (a : all_params_ok_bexp n b), P1 n b) /\
          (forall (n : nat) (l : list aexp_Imp_Lang) (a : all_params_ok_args n l), P2 n l).

  Local Definition all_params_ok_mut_ind_theorem_P
      (P: nat -> imp_Imp_Lang -> Prop) :=
        fun (n: nat) (i: imp_Imp_Lang) =>
        fun (_: all_params_ok n i) =>
          P n i.

  Local Definition all_params_ok_mut_ind_theorem_P0
      (P0: nat -> aexp_Imp_Lang -> Prop) :=
        fun (n: nat) (a: aexp_Imp_Lang) =>
        fun (_: all_params_ok_aexp n a) =>
          P0 n a.
  Local Definition all_params_ok_mut_ind_theorem_P1
      (P1: nat -> bexp_Imp_Lang -> Prop) :=
        fun (n: nat) (b: bexp_Imp_Lang) =>
        fun (_: all_params_ok_bexp n b) =>
          P1 n b.

  Local Definition all_params_ok_mut_ind_theorem_P2
      (P2: nat -> list aexp_Imp_Lang -> Prop) :=
        fun (n: nat) (args: list aexp_Imp_Lang) =>
        fun (_: all_params_ok_args n args) =>
          P2 n args.

  Ltac all_params_ok_mutual_induction P P0 P1 P2 :=
    let P' := fresh "P" in
    let P0' := fresh "P0" in
    let P1' := fresh "P1" in
    let P2' := fresh "P2" in
    pose (all_params_ok_mut_ind_theorem_P P) as P';
    pose (all_params_ok_mut_ind_theorem_P0 P0) as P0';
    pose (all_params_ok_mut_ind_theorem_P1 P1) as P1';
    pose (all_params_ok_mut_ind_theorem_P2 P2) as P2';
    apply (all_params_ok_mut_ind P' P0' P1' P2');
    try unfold all_params_ok_mut_ind_theorem;
    unfold P', P0', P1', P2';
    try unfold P, P0, P1, P2;
    try unfold all_params_ok_mut_ind_theorem_P, all_params_ok_mut_ind_theorem_P0, all_params_ok_mut_ind_theorem_P1, all_params_ok_mut_ind_theorem_P2.
(* End all_params_ok_mutual_induction_section. *)


Section more_params.
  Let more_params_P (n: nat) i :=
        forall n',
          n <= n' ->
          all_params_ok n' i.
  Let more_params_P0 (n: nat) a :=
        forall n',
          n <= n' ->
          all_params_ok_aexp n' a.
  Let more_params_P1 (n: nat) b :=
        forall n',
          n <= n' ->
          all_params_ok_bexp n' b.
  Let more_params_P2 (n: nat) args :=
        forall n',
          n <= n' ->
          all_params_ok_args n' args.

  Lemma more_params_is_more_okay :
    all_params_ok_mut_ind_theorem more_params_P more_params_P0 more_params_P1 more_params_P2.
  Proof using more_params_P more_params_P0 more_params_P1 more_params_P2.
    (* unfold all_params_ok_mut_ind_theorem. *)
    all_params_ok_mutual_induction more_params_P more_params_P0 more_params_P1 more_params_P2; intros.
    - econstructor.
    - specialize (H _ H0). econstructor.
      eassumption.
    - specialize (H _ H1). specialize (H0 _ H1).
      econstructor; eassumption.
    - specialize (H _ H2). specialize (H0 _ H2). specialize (H1 _ H2). econstructor; eassumption.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
    - econstructor.
    - econstructor. Psatz.lia.
    - econstructor.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
    - specialize (H _ H0). econstructor. eassumption.
    - econstructor.
    - econstructor.
    - specialize (H _ H0). econstructor; eassumption.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
    - econstructor.
    - specialize (H _ H1). specialize (H0 _ H1). econstructor; eassumption.
  Qed.

  Lemma imp_more_params_is_more_okay :
    (forall (n : nat) (i : imp_Imp_Lang), all_params_ok n i -> more_params_P n i).
  Proof.
    eapply more_params_is_more_okay.
  Qed.

  Lemma aexp_more_params_is_more_okay :
    (forall (n : nat) (a : aexp_Imp_Lang), all_params_ok_aexp n a -> more_params_P0 n a).
  Proof.
    eapply more_params_is_more_okay.
  Qed.

  Lemma bexp_more_params_is_more_okay :
    (forall (n : nat) (b : bexp_Imp_Lang), all_params_ok_bexp n b -> more_params_P1 n b).
  Proof.
    eapply more_params_is_more_okay.
  Qed.

  Lemma args_more_params_is_more_okay :
    (forall (n : nat) (l : list aexp_Imp_Lang), all_params_ok_args n l -> more_params_P2 n l).
  Proof.
    eapply more_params_is_more_okay.
  Qed.
End more_params.
            

