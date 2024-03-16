From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import Imp_LangTrickLanguage.

Ltac lots_of_rewrites Hrewrite_in REW1 REW2 REW3 REW4 REW5 REW6 :=
  try rewrite <- REW1 in Hrewrite_in;
  try rewrite <- REW2 in Hrewrite_in;
  try rewrite <- REW3 in Hrewrite_in;
  try rewrite <- REW4 in Hrewrite_in;
  try rewrite <- REW5 in Hrewrite_in;
  try rewrite <- REW6 in Hrewrite_in.

Ltac destruct_ands :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
             let H1 := fresh "A" in
             let H2 := fresh "B" in
             destruct H as (H1 & H2)
         end.

Ltac make_stack_big_enough :=
  match goal with
  | [ H: context C [Datatypes.length ?stk] |- _  ] =>
      destruct stk; simpl in H; try lia
  end.

Ltac string_dec_destruct :=
    match goal with
    | [ |- context STR_DEC [if string_dec ?a ?b then _ else _]] =>
        destruct (string_dec a b); try string_dec_destruct
    end.

Ltac get_contradiction :=
  match goal with
  | [ H: ~ (?a \/ ?b) |- _ ] =>
      enough (HNot : a \/ b);
      [ congruence | ]
  end.

Ltac simplify_In :=
  match goal with
  | [ |- In ?a ?b ] =>
      let a' := fresh "a'" in
      let Heqa' := fresh "Heqa'" in
      let b' := fresh "b'" in
      let Heqb' := fresh "Heqb'" in
      remember a as a' eqn:Heqa'; simpl in Heqa'; try unfold update in Heqa'; simpl in Heqa'; subst a';
      remember b as b' eqn:Heqb'; simpl in Heqb'; try unfold update in Heqb'; simpl in Heqb'; subst b'
  end.

Ltac unfold_constants a :=
  let a' := fresh "a'" in
  let Heqa' := fresh "Heqa'" in
  remember a as a' eqn:Heqa';
  let typeH := type of Heqa' in
  match a with
  | ?num_one _ => try unfold num_one in Heqa'; simpl in Heqa'
  | ?sth => try unfold sth in Heqa'
  end;
  subst a'.

Ltac unfold_In :=
  repeat match goal with
         | [ |- In ?a ?b ] =>
             try (progress unfold_constants a); try (progress unfold_constants b)
         end.

Ltac seassumption :=
  eassumption || (symmetry; eassumption).

Ltac string_dec_destruct_context :=
    match goal with
    | [ H: context STR_DEC [if string_dec ?a ?b then _ else _] |- _] =>
        destruct (string_dec a b); try string_dec_destruct_context
    end.
