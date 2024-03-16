From Coq Require Import Arith List String.
From Imp_LangTrick Require Import StackLanguage.

Inductive Forall_set {A: Type}: (A -> Set) -> (list A) -> Type :=
| Forall_set_nil :
  forall (P: A -> Set),
    Forall_set P nil
| Forall_set_cons :
  forall (P: A -> Set) (a: A) (l: list A),
    P a ->
    Forall_set P l ->
    Forall_set P (cons a l).

Print Forall_set_rec.

Section aexp_stack_rec2.
  Variable P: aexp_stack -> Set.
  Variable fconst : forall n: nat, P (Const_Stk n).
  Variable fvar : forall k: nat, P (Var_Stk k).
  Variable fplus : forall a1: aexp_stack, P a1 -> forall a2: aexp_stack, P a2 -> P (Plus_Stk a1 a2).
  Variable fminus : forall a1: aexp_stack, P a1 -> forall a2: aexp_stack, P a2 -> P (Minus_Stk a1 a2).
  Variable fapp : forall f (args: list aexp_stack), Forall_set  P args -> P (App_Stk f args).
  Print Forall.

  Fixpoint aexp_stack_rec2 (a: aexp_stack) : P a :=
    match a as a0 return (P a0) with
    | Const_Stk n => fconst n
    | Var_Stk k => fvar k
    | Plus_Stk a1 a2 => fplus a1 (aexp_stack_rec2 a1) a2 (aexp_stack_rec2 a2)
    | Minus_Stk a1 a2 => fminus a1 (aexp_stack_rec2 a1) a2 (aexp_stack_rec2 a2)
    | App_Stk f args =>
        fapp f args
             ((fix L args :=
                 match args return (Forall_set P args) with
                 | nil => Forall_set_nil _
                 | cons a args_tl => Forall_set_cons P a args_tl (aexp_stack_rec2 a) (L args_tl)
                 end) args)
    end.
End aexp_stack_rec2.
  (* Print aexp_stack_rec. *)
