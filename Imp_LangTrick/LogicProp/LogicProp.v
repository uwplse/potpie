From Coq Require Import List.

Local Open Scope list_scope.


Inductive LogicProp (V: Set) (A: Set): Type :=
| TrueProp
| FalseProp
| UnaryProp (f: V -> Prop) (a: A)
| BinaryProp (f: V -> V -> Prop) (a1 a2: A)
| AndProp (p1 p2: LogicProp V A)
| OrProp (p1 p2: LogicProp V A)
| TernaryProp (f: V -> V -> V -> Prop) (a1 a2 a3: A)
| NaryProp (f: list V -> Prop) (a_list: list A).

Fixpoint compile_prop {V A B: Set} (l: LogicProp V A) (phi: A -> B): LogicProp V B :=
  match l with
  | TrueProp _ _ => TrueProp V B
  | FalseProp _ _ => FalseProp V B
  | UnaryProp _ _ f a => UnaryProp V B f (phi a)
  | BinaryProp _ _ f a1 a2 => BinaryProp V B f (phi a1) (phi a2)
  | AndProp _ _ p1 p2 => AndProp V B (compile_prop p1 phi) (compile_prop p2 phi)
  | OrProp _ _ p1 p2 => OrProp V B (compile_prop p1 phi) (compile_prop p2 phi)
  | TernaryProp _ _ f a1 a2 a3 => TernaryProp V B f (phi a1) (phi a2) (phi a3)
  | NaryProp _ _ f a_list => NaryProp V B f (map phi a_list)
  end.


Inductive compile_prop_args_rel {A B: Set}: (A -> B) -> (list A) -> (list B) -> Prop :=
| CompileArgsNil :
  forall (phi: A -> B),
    compile_prop_args_rel phi nil nil
| CompileArgsCons :
  forall (phi: A -> B) (arg: A) (args: list A) (args': list B),
    compile_prop_args_rel phi args args' ->
    compile_prop_args_rel phi (arg :: args) ((phi arg) :: args').
    

Inductive compile_prop_rel {V A B: Set}: (A -> B) -> (LogicProp V A) -> (LogicProp V B) -> Prop :=
| CompileTrueProp :
  forall (phi: A -> B),
    compile_prop_rel phi (TrueProp V A) (TrueProp V B)
| CompileFalseProp :
  forall (phi: A -> B),
    compile_prop_rel phi (FalseProp V A) (FalseProp V B)
| CompileUnaryProp :
  forall (phi: A -> B) (f: V -> Prop) (a: A),
    compile_prop_rel phi (UnaryProp _ _ f a) (UnaryProp _ _ f (phi a))
| CompileBinaryProp :
  forall (phi: A -> B) (f: V -> V -> Prop) (a1 a2: A),
    compile_prop_rel phi (BinaryProp _ _ f a1 a2) (BinaryProp _ _ f (phi a1) (phi a2))
| CompileAndProp :
  forall (phi: A -> B) (p1 p2: LogicProp V A) (q1 q2: LogicProp V B),
    compile_prop_rel phi p1 q1 ->
    compile_prop_rel phi p2 q2 ->
    compile_prop_rel phi (AndProp _ _ p1 p2) (AndProp _ _ q1 q2)
| CompileOrProp :
  forall (phi: A -> B) (p1 p2: LogicProp V A) (q1 q2: LogicProp V B),
    compile_prop_rel phi p1 q1 ->
    compile_prop_rel phi p2 q2 ->
    compile_prop_rel phi (OrProp _ _ p1 p2) (OrProp _ _ q1 q2)
| CompileTernaryProp :
  forall (phi: A -> B) (f: V -> V -> V -> Prop) (a1 a2 a3: A),
    compile_prop_rel phi
                     (TernaryProp _ _ f a1 a2 a3)
                     (TernaryProp _ _ f (phi a1) (phi a2) (phi a3))
| CompileNaryProp :
  forall (phi: A -> B) (f: list V -> Prop) (alist: list A) (blist: list B),
    compile_prop_args_rel phi alist blist ->
    compile_prop_rel phi (NaryProp _ _ f alist) (NaryProp _ _ f blist).


Local Definition comp_rel (A B: Set) := A -> B -> Prop.

Inductive pcompile_args_rel {A B: Set}: (A -> B -> Prop) -> list A -> list B -> Prop :=
| PCompileArgsNil :
  forall (phi: comp_rel A B),
    pcompile_args_rel phi nil nil
| PCompileArgsCons :
  forall (phi: comp_rel A B) (a_arg : A) (a_list: list A) (b_arg: B) (b_list: list B),
    phi a_arg b_arg ->
    pcompile_args_rel phi a_list b_list ->
    pcompile_args_rel phi (a_arg :: a_list) (b_arg :: b_list).

Inductive pcompile_rel {V A B: Set}: (A -> B -> Prop) -> (LogicProp V A) -> (LogicProp V B) -> Prop :=
| PCompileTrueProp :
  forall (phi: comp_rel A B),
    pcompile_rel phi (TrueProp V A) (TrueProp V B)
| PCompileFalseProp :
  forall (phi: comp_rel A B),
    pcompile_rel phi (FalseProp V A) (FalseProp V B)
| PCompileUnaryProp :
  forall (phi: comp_rel A B) (f: V -> Prop) (a: A) (b: B),
    phi a b ->
    pcompile_rel phi (UnaryProp _ _ f a) (UnaryProp _ _ f b)
| PCompileBinaryProp :
  forall (phi: comp_rel A B) (f: V -> V -> Prop) (a1 a2: A) (b1 b2: B),
    phi a1 b1 ->
    phi a2 b2 ->
    pcompile_rel phi (BinaryProp _ _ f a1 a2) (BinaryProp _ _ f b1 b2)
| PCompileAndProp :
  forall (phi: comp_rel A B) (p1 p2: LogicProp V A) (q1 q2: LogicProp V B),
    pcompile_rel phi p1 q1 ->
    pcompile_rel phi p2 q2 ->
    pcompile_rel phi (AndProp _ _ p1 p2) (AndProp _ _ q1 q2)
| PCompileOrProp :
  forall (phi: comp_rel A B) (p1 p2: LogicProp V A) (q1 q2: LogicProp V B),
    pcompile_rel phi p1 q1 ->
    pcompile_rel phi p2 q2 ->
    pcompile_rel phi (OrProp _ _ p1 p2) (OrProp _ _ q1 q2)
| PCompileTernaryProp :
  forall (phi: comp_rel A B) (f: V -> V -> V -> Prop) (a1 a2 a3: A) (b1 b2 b3: B),
    phi a1 b1 ->
    phi a2 b2 ->
    phi a3 b3 ->
    pcompile_rel phi (TernaryProp _ _ f a1 a2 a3) (TernaryProp _ _ f b1 b2 b3)
| PCompileNaryProp :
  forall (phi: comp_rel A B) (f: list V -> Prop) (a_list: list A) (b_list: list B),
    pcompile_args_rel phi a_list b_list ->
    pcompile_rel phi (NaryProp _ _ f a_list) (NaryProp _ _ f b_list).


Fixpoint eval_prop {V A: Set} (l: LogicProp V A) (eval: A -> V): Prop :=
  match l with
  | TrueProp _ _ => True
  | FalseProp _ _ => False
  | UnaryProp _ _ f a => f (eval a)
  | BinaryProp _ _ f a1 a2 => f (eval a1) (eval a2)
  | AndProp _ _ p1 p2 => (eval_prop p1 eval) /\ (eval_prop p2 eval)
  | OrProp _ _ p1 p2 => (eval_prop p1 eval) \/ (eval_prop p2 eval)
  | TernaryProp _ _ f a1 a2 a3 => f (eval a1) (eval a2) (eval a3)
  | NaryProp _ _ f a_list => f (map eval a_list)
  end.

Inductive Hoare_Generic {V A V' A' I: Set}: Type :=
| HoareTriple (P: LogicProp V A) (i: I) (Q: LogicProp V' A').


Inductive eval_prop_rel {V A: Set}: (A -> V -> Prop) -> (LogicProp V A) -> Prop :=
| RelTrueProp :
  forall rel,
    eval_prop_rel rel (TrueProp V A)
| RelUnaryProp :
  forall (rel: A -> V -> Prop) (f: V -> Prop) (a: A) (v: V),
    rel a v ->
    f v ->
    eval_prop_rel rel (UnaryProp V A f a)
| RelBinaryProp :
  forall (rel: A -> V -> Prop) (f: V -> V -> Prop) a1 a2 v1 v2,
    rel a1 v1 ->
    rel a2 v2 ->
    f v1 v2 ->
    eval_prop_rel rel (BinaryProp V A f a1 a2)
| RelAndProp :
  forall (rel: A -> V -> Prop) p1 p2,
    eval_prop_rel rel p1 ->
    eval_prop_rel rel p2 ->
    eval_prop_rel rel (AndProp V A p1 p2)
| RelOrPropLeft :
  forall (rel: A -> V -> Prop) p1 p2,
    eval_prop_rel rel p1 ->
    eval_prop_rel rel (OrProp V A p1 p2)
| RelOrPropRight :
  forall (rel: A -> V -> Prop) p1 p2,
    eval_prop_rel rel p2 ->
    eval_prop_rel rel (OrProp V A p1 p2)
| RelTernaryProp :
  forall (rel: A -> V -> Prop) (f: V -> V -> V -> Prop) a1 a2 a3 v1 v2 v3,
    rel a1 v1 ->
    rel a2 v2 ->
    rel a3 v3 ->
    f v1 v2 v3 ->
    eval_prop_rel rel (TernaryProp V A f a1 a2 a3)
| RelNaryProp :
  forall (rel: A -> V -> Prop) (f: list V -> Prop) args vals,
    eval_prop_args_rel rel args vals ->
    f vals ->
    eval_prop_rel rel (NaryProp V A f args)
with eval_prop_args_rel {V A: Set}: (A -> V -> Prop) -> (list A) -> (list V) -> Prop :=
| RelArgsNil :
  forall (rel: A -> V -> Prop),
    eval_prop_args_rel rel nil nil
| RelArgsCons :
  forall (rel: A -> V -> Prop) arg val args vals,
    rel arg val ->
    eval_prop_args_rel rel args vals ->
    eval_prop_args_rel rel (arg :: args) (val :: vals).


Inductive prop_args_rel {V A: Set}: (A -> Prop) -> (list A) -> Prop :=
| PropRelArgsNil :
  forall (rel: A -> Prop),
    prop_args_rel rel nil
| PropRelArgsCons :
  forall (rel: A -> Prop) arg args,
    rel arg ->
    prop_args_rel rel args ->
    prop_args_rel rel (arg :: args).


Local Definition f_t (V A: Set) := A -> V.
Local Definition pred1 (V: Set) := (V -> Prop) -> Prop.
Local Definition pred2 (V: Set) := (V -> V -> Prop) -> Prop.
Local Definition pred3 (V: Set) := (V -> V -> V -> Prop) -> Prop.
Local Definition predl (V: Set) := (list V -> Prop) -> Prop.
Local Definition pred_a (A: Set) := A -> Prop.
Inductive char_prop_rel {V A: Set}: pred1 V -> pred2 V -> pred3 V -> predl V -> (A -> Prop) -> (LogicProp V A) -> Prop :=
| LPCharTrue :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A),
    char_prop_rel rel1 rel2 rel3 listrel rel__A (TrueProp _ _)
| LPCharFalse :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A),
    char_prop_rel rel1 rel2 rel3 listrel rel__A (FalseProp _ _)
| LPCharUnary :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A) (f: V -> Prop) (a: A),
    rel1 f ->
    rel__A a ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A (UnaryProp _ _ f a)
| LPCharBinary :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A) (f: V -> V -> Prop) (a1 a2: A),
    rel2 f ->
    rel__A a1 ->
    rel__A a2 ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A (BinaryProp _ _ f a1 a2)
| LPCharAnd :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A) (l1 l2: LogicProp V A),
    char_prop_rel rel1 rel2 rel3 listrel rel__A l1 ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A l2 ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A (AndProp _ _ l1 l2)
| LPCharOr :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A) (l1 l2: LogicProp V A),
    char_prop_rel rel1 rel2 rel3 listrel rel__A l1 ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A l2 ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A (OrProp _ _ l1 l2)
| LPCharTernary :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A) (f: V -> V -> V -> Prop) (a1 a2 a3: A),
    rel3 f ->
    rel__A a1 ->
    rel__A a2 ->
    rel__A a3 ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A (TernaryProp _ _ f a1 a2 a3)
| LPCharNary :
  forall (rel1: pred1 V) (rel2: pred2 V) (rel3: pred3 V) (listrel: predl V) (rel__A: pred_a A) (f: list V -> Prop) (alist: list A),
    prop_args_rel (V := V) rel__A alist ->
    listrel f ->
    char_prop_rel rel1 rel2 rel3 listrel rel__A (NaryProp _ _ f alist).

Local Definition bpred1 (V: Set) := (V -> Prop) -> (V -> Prop) -> Prop.
Local Definition bpred2 (V: Set) := (V -> V -> Prop) -> (V -> V -> Prop) -> Prop.
Local Definition bpred3 (V: Set) := (V -> V -> V -> Prop) -> (V -> V -> V -> Prop) -> Prop.
Local Definition bpredl (V: Set) := (list V -> Prop) -> (list V -> Prop) -> Prop.
Local Definition bpred_a (A: Set) := A -> A -> Prop.

Definition relA (A: Set) := A -> A -> Prop.

Inductive transformed_prop_exprs_args {V A: Set}: (relA A) -> (list A) -> (list A) -> Prop :=
| TrArgsNil :
  forall (rel: relA A),
    transformed_prop_exprs_args rel nil nil
| TrArgsCons :
  forall (rel: relA A) (arg: A) (args: list A) (arg': A) (args': list A),
    rel arg arg' ->
    transformed_prop_exprs_args rel args args' ->
    transformed_prop_exprs_args rel (arg :: args) (arg' :: args').

Inductive bin_prop_rel {V A: Set}: bpred1 V -> bpred2 V -> bpred3 V -> bpredl V -> bpred_a A -> (LogicProp V A) -> (LogicProp V A) -> Prop :=
| LPBinTrue :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A),
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (TrueProp _ _ ) (TrueProp _ _)
| LPBinFalse :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A),
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (FalseProp _ _ ) (FalseProp _ _)
| LPBinUnary :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A) (f f': V -> Prop) (a a': A),
    rel1 f f' ->
    rel__A a a' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (UnaryProp _ _ f a) (UnaryProp _ _ f' a')
| LPBinBinary :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A) (f f': V -> V -> Prop) (a1 a2 a1' a2': A),
    rel2 f f' ->
    rel__A a1 a1' ->
    rel__A a2 a2' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (BinaryProp _ _ f a1 a2) (BinaryProp _ _ f' a1' a2')
| LPBinAnd :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A) (l1 l2 l1' l2': LogicProp V A),
    bin_prop_rel rel1 rel2 rel3 listrel rel__A l1 l1' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A l2 l2' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (AndProp _ _ l1 l2) (AndProp _ _ l1' l2')
| LPBinOr :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A) (l1 l2 l1' l2': LogicProp V A),
    bin_prop_rel rel1 rel2 rel3 listrel rel__A l1 l1' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A l2 l2' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (OrProp _ _ l1 l2) (OrProp _ _ l1' l2')
| LPBinTernary :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A) (f f': V -> V -> V -> Prop) (a1 a2 a3 a1' a2' a3': A),
    rel3 f f' ->
    rel__A a1 a1' ->
    rel__A a2 a2' ->
    rel__A a3 a3' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (TernaryProp _ _ f a1 a2 a3) (TernaryProp _ _ f' a1' a2' a3')
| LPBinNary :
  forall (rel1: bpred1 V) (rel2: bpred2 V) (rel3: bpred3 V) (listrel: bpredl V) (rel__A: bpred_a A) (f f': list V -> Prop) (alist alist' : list A),
    listrel f f' ->
    transformed_prop_exprs_args (V := V) rel__A alist alist' ->
    bin_prop_rel rel1 rel2 rel3 listrel rel__A (NaryProp _ _ f alist) (NaryProp _ _ f' alist').
    
  

Inductive prop_rel {V A: Set}: (A -> Prop) -> (LogicProp V A) -> Prop :=
| PropRelTrueProp :
  forall rel,
    prop_rel rel (TrueProp V A)
| RelFalseProp :
  forall rel,
    prop_rel rel (FalseProp V A)
| PropRelUnaryProp :
  forall (rel: A -> Prop) (f: V -> Prop) (a: A),
    rel a ->
    prop_rel rel (UnaryProp V A f a)
| PropRelBinaryProp :
  forall (rel: A -> Prop) (f: V -> V -> Prop) a1 a2,
    rel a1 ->
    rel a2 ->
    prop_rel rel (BinaryProp V A f a1 a2)
| PropRelAndProp :
  forall (rel: A -> Prop) p1 p2,
    prop_rel rel p1 ->
    prop_rel rel p2 ->
    prop_rel rel (AndProp V A p1 p2)
| PropRelOrProp :
  forall (rel: A -> Prop) p1 p2,
    prop_rel rel p1 ->
    prop_rel rel p2 ->
    prop_rel rel (OrProp V A p1 p2)
| PropRelTernaryProp :
  forall (rel: A -> Prop) (f: V -> V -> V -> Prop) a1 a2 a3,
    rel a1 ->
    rel a2 ->
    rel a3 ->
    prop_rel rel (TernaryProp V A f a1 a2 a3)
| PropRelNaryProp :
  forall (rel: A -> Prop) (f: list V -> Prop) args,
    prop_args_rel (V := V) rel args ->
    prop_rel rel (NaryProp V A f args).

Fixpoint construct_prop_rel {V A: Set} (rel: A -> Prop) (lp: LogicProp V A) (show_rel: forall (a: A), option (rel a)) : option (prop_rel rel lp) :=
  match lp as lp' return option (prop_rel rel lp') with
  | TrueProp _ _ => Some (PropRelTrueProp rel)
  | FalseProp _ _ => Some (RelFalseProp rel)
  | UnaryProp _ _ f a =>
      match show_rel a with
      | Some Pa => Some (PropRelUnaryProp rel f a Pa)
      | None => None
      end
  | BinaryProp _ _ f a1 a2 =>
      match show_rel a1, show_rel a2 with
      | Some P1, Some P2 => Some (PropRelBinaryProp rel f a1 a2 P1 P2)
      | _, _ => None
      end
  | AndProp _ _ p1 p2 =>
      match construct_prop_rel rel p1 show_rel, construct_prop_rel rel p2 show_rel with
      | Some P1, Some P2 => Some (PropRelAndProp rel p1 p2 P1 P2)
      | _, _ => None
      end
  | OrProp _ _ p1 p2 =>
      match construct_prop_rel rel p1 show_rel, construct_prop_rel rel p2 show_rel with
      | Some P1, Some P2 => Some (PropRelOrProp rel p1 p2 P1 P2)
      | _, _ => None
      end
  | TernaryProp _ _ f a1 a2 a3 =>
      match show_rel a1, show_rel a2, show_rel a3 with
      | Some P1, Some P2, Some P3 => Some (PropRelTernaryProp rel f a1 a2 a3 P1 P2 P3)
      | _, _, _ => None
      end
  | NaryProp _ _ f args =>
      match (fix construct_prop_args_rel (args: list A): option (prop_args_rel (V := V) rel args) :=
               match args as args'' return option (prop_args_rel (V := V) rel args'') with
               | nil => Some (PropRelArgsNil rel)
               | arg :: args' =>
                   match show_rel arg, construct_prop_args_rel args' with
                   | Some Parg, Some Pargs' =>
                       Some (PropRelArgsCons rel arg args' Parg Pargs')
                   | _, _ => None
                   end
               end) args with
      | Some Pargs =>
          Some (PropRelNaryProp rel f args Pargs)
      | None => None
      end
  end.


Definition NatProp (A: Set): Type := LogicProp nat A.

Definition BoolProp (A: Set): Type := LogicProp bool A.

Fixpoint transform_prop_exprs {V A: Set} (l: LogicProp V A) (phi: A -> A): LogicProp V A :=
  match l with
  | UnaryProp _ _ f a => UnaryProp V A f (phi a)
  | BinaryProp _ _ f a1 a2 => BinaryProp V A f (phi a1) (phi a2)
  | AndProp _ _ p1 p2 => AndProp V A (transform_prop_exprs p1 phi) (transform_prop_exprs p2 phi)
  | OrProp _ _ p1 p2 => OrProp V A (transform_prop_exprs p1 phi) (transform_prop_exprs p2 phi)
  | TernaryProp _ _ f a1 a2 a3 => TernaryProp V A f (phi a1) (phi a2) (phi a3)
  | NaryProp _ _ f a_list => NaryProp V A f (map phi a_list)
  | _ => l
  end.



Inductive transformed_prop_exprs {V A: Set}: (A -> A -> Prop) -> (LogicProp V A) -> (LogicProp V A) -> Prop :=
| TrTrueProp :
  forall (rel: A -> A -> Prop),
    transformed_prop_exprs rel (TrueProp V A) (TrueProp V A)
| TrFalseProp :
  forall (rel: A -> A -> Prop),
    transformed_prop_exprs rel (FalseProp V A) (FalseProp V A)
| TrUnaryProp :
  forall (rel: relA A) f a a',
    rel a a' ->
    transformed_prop_exprs rel (UnaryProp _ _ f a) (UnaryProp _ _ f a')
| TrBinaryProp :
  forall (rel: relA A) (f: V -> V -> Prop) a1 a2 a1' a2',
    rel a1 a1' ->
    rel a2 a2' ->
    transformed_prop_exprs rel (BinaryProp _ _ f a1 a2) (BinaryProp _ _ f a1' a2')
| TrAndProp :
  forall (rel: relA A) (p1 p2 p1' p2': LogicProp V A),
    transformed_prop_exprs rel p1 p1' ->
    transformed_prop_exprs rel p2 p2' ->
    transformed_prop_exprs rel (AndProp _ _ p1 p2) (AndProp _ _ p1' p2')
| TrOrProp :
  forall (rel: relA A) (p1 p2 p1' p2': LogicProp V A),
    transformed_prop_exprs rel p1 p1' ->
    transformed_prop_exprs rel p2 p2' ->
    transformed_prop_exprs rel (OrProp _ _ p1 p2) (OrProp _ _ p1' p2')
| TrTernaryProp :
  forall (rel: relA A) (f: V -> V -> V -> Prop) a1 a2 a3 a1' a2' a3',
    rel a1 a1' ->
    rel a2 a2' ->
    rel a3 a3' ->
    transformed_prop_exprs rel (TernaryProp _ _ f a1 a2 a3) (TernaryProp _ _ f a1' a2' a3')
| TrNaryProp :
  forall (rel: relA A) (f: list V -> Prop) a_list a_list',
    transformed_prop_exprs_args (V := V) (A := A) rel a_list a_list' ->
    transformed_prop_exprs rel (NaryProp _ _ f a_list) (NaryProp _ _ f a_list').
