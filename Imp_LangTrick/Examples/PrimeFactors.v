From Coq Require Import List Arith String ZArith.


From Imp_LangTrick Require Import Base Imp_LangTrickLanguage StackLanguage.
(* rsa_impLang. *)


Definition div_and_mod (x y: nat) : nat * nat :=
  match y with
  | 0 => (y, x)
  | S y' => let (d, m') := Nat.divmod x y' 0 y' in
           (d, y' - m')
  end.

Lemma div_and_mod_fst_same_as_div :
  forall (x y d: nat),
    d = fst (div_and_mod x y) <->
      d = Nat.div x y.
Proof.
  intros x y. revert x. destruct y; intros.
  - split; intros.
    + simpl in *. eassumption.
    + simpl in *. eassumption.
  - split; intros.
    + simpl. simpl in H. destruct (Nat.divmod x y 0 y) eqn:dm.
      simpl. simpl in H. eassumption.
    + simpl. simpl in H. destruct (Nat.divmod x y 0 y) eqn:dm.
      simpl in *. eassumption.
Qed.

Lemma div_and_mod_snd_same_as_modulo :
  forall (x y m: nat),
    m = snd (div_and_mod x y) <->
      m = Nat.modulo x y.
Proof.
  intros x y. revert x. destruct y; intros; split; intros; simpl in *.
  - eassumption.
  - eassumption.
  - destruct (Nat.divmod x y 0 y) eqn:dm. simpl in *. eassumption.
  - destruct (Nat.divmod x y 0 y) eqn:dm. simpl in *. eassumption.
Qed.


