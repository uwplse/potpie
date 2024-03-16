From Coq Require Import Arith Psatz Bool String List Program.Equality Logic.Eqdep_dec Nat.
From Imp_LangTrick Require Export Base.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.


Definition store (T: Type): Type := ident -> T.


Definition update {T: Type} (x: ident) (v: T) (s: store T): store T :=
  fun y => if string_dec x y then v else s y.

Lemma update_same:
  forall (T: Type) (x: ident) (v: T) (s: store T), (update x v s) x = v.
Proof.
  unfold update; intros. destruct (string_dec x x); congruence.
Qed.

Lemma update_other:
  forall (T: Type) (x: ident) (v: T) (s: store T) (y: ident), x <> y -> (update x v s) y = s y.
Proof.
  unfold update; intros. destruct (string_dec x y); congruence.
Qed.

Section SEQUENCES.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation between states *)

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive transitive closure of [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; eauto using star. 
Qed.

End SEQUENCES.

(*default function if not defined is the identity function. *)



Definition nat_env := store nat. 

Definition init_nenv: nat_env := fun _ => 0.

Definition debruijn_env: Type := list nat.

Definition init_debruijn_env: debruijn_env := nil.


Inductive aexp_Imp_Lang :=
| CONST_Imp_Lang (n: nat)
| VAR_Imp_Lang (x: ident)
| PARAM_Imp_Lang (n: nat)
| PLUS_Imp_Lang (a1 a2: aexp_Imp_Lang)
| MINUS_Imp_Lang (a1 a2: aexp_Imp_Lang)
| APP_Imp_Lang (f: ident) (aexps : list aexp_Imp_Lang).

(*
 * Custom induction principle with stronger handling of containers,
 * based on this trick: https://pastebin.com/BAvg3Jdh
 *)
Section aexp_Imp_Lang_ind2.
  Variable P: aexp_Imp_Lang -> Prop. (* this is the property we want to prove *)
 
  (* For each constructor, we add a Variable *)
  Variable fconst : forall n : nat, P (CONST_Imp_Lang n).
  Variable fvar : forall x : ident, P (VAR_Imp_Lang x).
  Variable fparam : forall n : nat, P (PARAM_Imp_Lang n).
  Variable fplus :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P (PLUS_Imp_Lang a1 a2).
  Variable fminus :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P (MINUS_Imp_Lang a1 a2).
  Variable fapp :
    forall f (aexps : list aexp_Imp_Lang), List.Forall P aexps -> P (APP_Imp_Lang f aexps).

  Fixpoint aexp_Imp_Lang_ind2 (a : aexp_Imp_Lang) : P a :=
    match a as a0 return (P a0) with
    | CONST_Imp_Lang n => fconst n
    | VAR_Imp_Lang x => fvar x
    | PARAM_Imp_Lang n => fparam n
    | PLUS_Imp_Lang a1 a2 => fplus a1 (aexp_Imp_Lang_ind2 a1) a2 (aexp_Imp_Lang_ind2 a2)
    | MINUS_Imp_Lang a1 a2 => fminus a1 (aexp_Imp_Lang_ind2 a1) a2 (aexp_Imp_Lang_ind2 a2)
    | APP_Imp_Lang f aexps =>
        fapp f aexps
          ((fix L aexps := 
             match aexps return (Forall P aexps) with
             | nil => Forall_nil _
             | cons a aexps_tl => Forall_cons a (aexp_Imp_Lang_ind2 a) (L aexps_tl) end) aexps)
    end.
End aexp_Imp_Lang_ind2.

(* set version *)
Section aexp_Imp_Lang_rec2.
  Variable P: aexp_Imp_Lang -> Set. (* this is the property we want to prove *)
 
  (* For each constructor, we add a Variable *)
  Variable fconst : forall n : nat, P (CONST_Imp_Lang n).
  Variable fvar : forall x : ident, P (VAR_Imp_Lang x).
  Variable fparam : forall n : nat, P (PARAM_Imp_Lang n).
  Variable fplus :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P (PLUS_Imp_Lang a1 a2).
  Variable fminus :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P (MINUS_Imp_Lang a1 a2).

   Inductive SForall : list aexp_Imp_Lang -> Set :=
   | SForall_nil : SForall nil
   | SForall_cons : forall x l, P x -> SForall l -> SForall (x::l).

  Variable fapp :
    forall f (aexps : list aexp_Imp_Lang), SForall aexps -> P (APP_Imp_Lang f aexps).

  Fixpoint aexp_Imp_Lang_rec2 (a : aexp_Imp_Lang) : P a :=
    match a as a0 return (P a0) with
    | CONST_Imp_Lang n => fconst n
    | VAR_Imp_Lang x => fvar x
    | PARAM_Imp_Lang n => fparam n
    | PLUS_Imp_Lang a1 a2 => fplus a1 (aexp_Imp_Lang_rec2 a1) a2 (aexp_Imp_Lang_rec2 a2)
    | MINUS_Imp_Lang a1 a2 => fminus a1 (aexp_Imp_Lang_rec2 a1) a2 (aexp_Imp_Lang_rec2 a2)
    | APP_Imp_Lang f aexps =>
        fapp f aexps
          ((fix L aexps := 
             match aexps return (SForall aexps) with
             | nil => SForall_nil
             | cons a aexps_tl => SForall_cons a _ (aexp_Imp_Lang_rec2 a) (L aexps_tl) end) aexps)
    end.
End aexp_Imp_Lang_rec2.

(* Definition aexp_vector (n: nat): Type := VectorDef.t aexp_Imp_Lang n. *)

(* Definition nil_aexp_vector: aexp_vector 0 := nil aexp_Imp_Lang. *)

Declare Scope imp_langtrick_scope.

Infix "+d" := PLUS_Imp_Lang (at level 76) : imp_langtrick_scope.
Infix "-d" := MINUS_Imp_Lang (at level 76) : imp_langtrick_scope.
Infix "@d" := APP_Imp_Lang (at level 76) : imp_langtrick_scope.

Inductive bexp_Imp_Lang := 
| TRUE_Imp_Lang
| FALSE_Imp_Lang
| NEG_Imp_Lang (b: bexp_Imp_Lang)
| AND_Imp_Lang (b1 b2: bexp_Imp_Lang)
| OR_Imp_Lang  (b1 b2: bexp_Imp_Lang)
| LEQ_Imp_Lang (a1 a2: aexp_Imp_Lang).

Definition eq_Imp_Lang (a b : aexp_Imp_Lang) : bexp_Imp_Lang :=
  AND_Imp_Lang (LEQ_Imp_Lang a b) (LEQ_Imp_Lang b a).
Definition geq_Imp_Lang (a b : aexp_Imp_Lang) : bexp_Imp_Lang :=
  LEQ_Imp_Lang b a.
Definition neq_Imp_Lang (a b : aexp_Imp_Lang) : bexp_Imp_Lang :=
  NEG_Imp_Lang (eq_Imp_Lang a b).
Definition lt_Imp_Lang (a b : aexp_Imp_Lang) : bexp_Imp_Lang :=
  AND_Imp_Lang (LEQ_Imp_Lang a b) (neq_Imp_Lang a b).
Definition gt_Imp_Lang (a b : aexp_Imp_Lang) : bexp_Imp_Lang :=
  lt_Imp_Lang b a.

Notation "a '=d' b" := (eq_Imp_Lang a b) (at level 50) : imp_langtrick_scope.
Infix "&d" := AND_Imp_Lang (at level 50) : imp_langtrick_scope.
Infix "|d" := OR_Imp_Lang (at level 50) : imp_langtrick_scope.
Notation "'!d' a" := (NEG_Imp_Lang a) (at level 80) : imp_langtrick_scope.
Infix "<=d" := LEQ_Imp_Lang (at level 90) : imp_langtrick_scope.
Notation "a '>=d' b" := (geq_Imp_Lang a b) (at level 90) : imp_langtrick_scope.
Notation "a '!=d' b" := (neq_Imp_Lang a b) (at level 90) : imp_langtrick_scope.
Notation "a '<d' b" := (lt_Imp_Lang a b) (at level 90) : imp_langtrick_scope.
Notation "a '>d' b" := (gt_Imp_Lang a b) (at level 90) : imp_langtrick_scope.

Inductive imp_Imp_Lang :=
  |IF_Imp_Lang (b: bexp_Imp_Lang) (i1 i2: imp_Imp_Lang)
  |SKIP_Imp_Lang
  |WHILE_Imp_Lang (b: bexp_Imp_Lang) (i: imp_Imp_Lang)
  |ASSIGN_Imp_Lang (x: ident) (a: aexp_Imp_Lang)
|SEQ_Imp_Lang (i1 i2: imp_Imp_Lang).

Section imp_Imp_Lang_ind2.
  Variable P: aexp_Imp_Lang -> Prop. (* this is the property we want to prove *)
  Variable P0: bexp_Imp_Lang -> Prop.
  Variable P1: imp_Imp_Lang -> Prop.
 
  (* For each constructor, we add a Variable *)
  Variable fconst : forall n : nat, P (CONST_Imp_Lang n).
  Variable fvar : forall x : ident, P (VAR_Imp_Lang x).
  Variable fparam : forall n : nat, P (PARAM_Imp_Lang n).
  Variable fplus :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P (PLUS_Imp_Lang a1 a2).
  Variable fminus :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P (MINUS_Imp_Lang a1 a2).
  Variable fapp :
    forall f (aexps : list aexp_Imp_Lang), List.Forall P aexps -> P (APP_Imp_Lang f aexps).
  Variable ftrue : P0 (TRUE_Imp_Lang).
  Variable ffalse : P0 (FALSE_Imp_Lang).
  Variable fneg : forall b: bexp_Imp_Lang, P0 b -> P0 (NEG_Imp_Lang b).
  Variable fand : forall b1: bexp_Imp_Lang, P0 b1 -> forall b2: bexp_Imp_Lang, P0 b2 -> P0 (AND_Imp_Lang b1 b2).
  Variable f_or : forall b1: bexp_Imp_Lang, P0 b1 -> forall b2: bexp_Imp_Lang, P0 b2 -> P0 (OR_Imp_Lang b1 b2).
  Variable fleq :
    forall a1 : aexp_Imp_Lang, P a1 -> forall a2 : aexp_Imp_Lang, P a2 -> P0 (LEQ_Imp_Lang a1 a2).
  Variable fskip : P1 SKIP_Imp_Lang.
  Variable fassign : forall x: ident, forall a: aexp_Imp_Lang, P a -> P1 (ASSIGN_Imp_Lang x a).
  Variable fseq : forall i1: imp_Imp_Lang, P1 i1 -> forall i2: imp_Imp_Lang, P1 i2 -> P1 (SEQ_Imp_Lang i1 i2).
  Variable fif : forall b: bexp_Imp_Lang, P0 b -> forall i1: imp_Imp_Lang, P1 i1 -> forall i2: imp_Imp_Lang, P1 i2 -> P1 (IF_Imp_Lang b i1 i2).
  Variable fwhile : forall b: bexp_Imp_Lang, P0 b -> forall i: imp_Imp_Lang, P1 i -> P1 (WHILE_Imp_Lang b i).

  Fixpoint imp_aexp_Imp_Lang_ind2 (a : aexp_Imp_Lang) : P a :=
    match a as a0 return (P a0) with
    | CONST_Imp_Lang n => fconst n
    | VAR_Imp_Lang x => fvar x
    | PARAM_Imp_Lang n => fparam n
    | PLUS_Imp_Lang a1 a2 => fplus a1 (imp_aexp_Imp_Lang_ind2 a1) a2 (imp_aexp_Imp_Lang_ind2 a2)
    | MINUS_Imp_Lang a1 a2 => fminus a1 (imp_aexp_Imp_Lang_ind2 a1) a2 (imp_aexp_Imp_Lang_ind2 a2)
    | APP_Imp_Lang f aexps =>
        fapp f aexps
          ((fix L aexps := 
             match aexps return (Forall P aexps) with
             | nil => Forall_nil _
             | cons a aexps_tl => Forall_cons a (imp_aexp_Imp_Lang_ind2 a) (L aexps_tl) end) aexps)
    end.
  Fixpoint imp_Imp_Lang_ind2 (i: imp_Imp_Lang): P1 i :=
           match i as i0 return (P1 i0) with
           | SKIP_Imp_Lang => fskip
           | ASSIGN_Imp_Lang x a => fassign x a (imp_aexp_Imp_Lang_ind2 a)
           | SEQ_Imp_Lang i1 i2 => fseq i1 (imp_Imp_Lang_ind2 i1) i2 (imp_Imp_Lang_ind2 i2)
           | IF_Imp_Lang b i1 i2 =>
               fif b ((fix imp_bexp_Imp_Lang_ind2 (b: bexp_Imp_Lang) : P0 b :=
                         match b as b0 return (P0 b0) with
                         | TRUE_Imp_Lang => ftrue
                         | FALSE_Imp_Lang => ffalse
                         | NEG_Imp_Lang b => fneg b (imp_bexp_Imp_Lang_ind2 b)
                         | AND_Imp_Lang b1 b2 => fand b1 (imp_bexp_Imp_Lang_ind2 b1) b2 (imp_bexp_Imp_Lang_ind2 b2)
                         | OR_Imp_Lang b1 b2 => f_or b1 (imp_bexp_Imp_Lang_ind2 b1) b2 (imp_bexp_Imp_Lang_ind2 b2)
                         | LEQ_Imp_Lang a1 a2 => fleq a1 (imp_aexp_Imp_Lang_ind2 a1) a2 (imp_aexp_Imp_Lang_ind2 a2)
                         end) b)
                   i1 (imp_Imp_Lang_ind2 i1) i2 (imp_Imp_Lang_ind2 i2)
           | WHILE_Imp_Lang b i =>
               fwhile b ((fix imp_bexp_Imp_Lang_ind2 (b: bexp_Imp_Lang) : P0 b :=
                            match b as b0 return (P0 b0) with
                            | TRUE_Imp_Lang => ftrue
                            | FALSE_Imp_Lang => ffalse
                            | NEG_Imp_Lang b => fneg b (imp_bexp_Imp_Lang_ind2 b)
                            | AND_Imp_Lang b1 b2 => fand b1 (imp_bexp_Imp_Lang_ind2 b1) b2 (imp_bexp_Imp_Lang_ind2 b2)
                            | OR_Imp_Lang b1 b2 => f_or b1 (imp_bexp_Imp_Lang_ind2 b1) b2 (imp_bexp_Imp_Lang_ind2 b2)
                            | LEQ_Imp_Lang a1 a2 => fleq a1 (imp_aexp_Imp_Lang_ind2 a1) a2 (imp_aexp_Imp_Lang_ind2 a2)
                            end) b)
                      i (imp_Imp_Lang_ind2 i)
           end.
End imp_Imp_Lang_ind2.

Notation "x <- e" := (ASSIGN_Imp_Lang x e) (at level 75) : imp_langtrick_scope.
Infix ";;" := SEQ_Imp_Lang (at level 76) : imp_langtrick_scope.
Notation "'when' b 'then' t 'else' e 'done'" :=
  (IF_Imp_Lang b t e) (at level 75, b at level 0) : imp_langtrick_scope.
Notation "'while' b 'loop' body 'done'" :=
  (WHILE_Imp_Lang b body) (at level 75) : imp_langtrick_scope.

Local Open Scope imp_langtrick_scope.

Record fun_Imp_Lang :=
  { Name: ident
  ; Args : nat
  ; Ret: ident
  ; Body: imp_Imp_Lang }.

Definition fun_env := store fun_Imp_Lang. 

Definition init_fenv: fun_env := fun _ => {| Name := "id"
                                          ; Args := 1
                                          ; Ret := "x"
                                          ; Body := "x" <- (PARAM_Imp_Lang 0) |}.

Inductive prog_Imp_Lang :=
| PROF_Imp_Lang (l: list fun_Imp_Lang) (i: imp_Imp_Lang).


Local Open Scope vector_scope.

Inductive a_Imp_Lang : aexp_Imp_Lang -> list nat -> fun_env -> nat_env -> nat -> Prop :=
| Imp_Lang_const : 
  forall dbenv fenv nenv n,
    a_Imp_Lang (CONST_Imp_Lang n) dbenv fenv nenv n
| Imp_Lang_var :
  forall dbenv fenv nenv x n,
    (nenv x = n) ->
    a_Imp_Lang (VAR_Imp_Lang x) dbenv fenv nenv n
| Imp_Lang_param :
  forall dbenv fenv nenv n m,
    0 <= n < List.length dbenv ->
    nth_error dbenv n = Some m ->
    a_Imp_Lang (PARAM_Imp_Lang n) dbenv fenv nenv m
| Imp_Lang_plus : 
  forall dbenv fenv nenv a1 a2 n1 n2, 
    a_Imp_Lang a1 dbenv fenv nenv n1 ->
    a_Imp_Lang a2 dbenv fenv nenv n2 -> 
    a_Imp_Lang (PLUS_Imp_Lang a1 a2) dbenv fenv nenv (n1 + n2)
| Imp_Lang_minus : 
  forall dbenv fenv nenv a1 a2 n1 n2, 
    a_Imp_Lang a1 dbenv fenv nenv n1 ->
    a_Imp_Lang a2 dbenv fenv nenv n2 -> 
    a_Imp_Lang (MINUS_Imp_Lang a1 a2) dbenv fenv nenv (n1 - n2)
| Imp_Lang_app : 
  forall dbenv fenv nenv nenv'' func aexps ns ret f, 
    (fenv f = func) ->
    (Args func) = Datatypes.length aexps ->
    args_Imp_Lang aexps dbenv fenv nenv ns ->
    (i_Imp_Lang (func).(Body) ns fenv init_nenv nenv'') ->
    (nenv'' ((func).(Ret)) = ret) ->
    a_Imp_Lang (APP_Imp_Lang f aexps) dbenv fenv nenv ret
with args_Imp_Lang: list aexp_Imp_Lang -> list nat -> fun_env -> nat_env -> list nat -> Prop :=
| args_nil :
  forall dbenv fenv nenv,
    args_Imp_Lang nil dbenv fenv nenv nil%list
| args_cons :
  forall aexp aexps dbenv fenv nenv v vals,
    a_Imp_Lang aexp dbenv fenv nenv v -> 
    args_Imp_Lang aexps dbenv fenv nenv vals ->
    args_Imp_Lang (aexp :: aexps) dbenv fenv nenv (v :: vals)
with b_Imp_Lang: bexp_Imp_Lang -> list nat -> fun_env -> nat_env -> bool -> Prop :=
|Imp_Lang_true : 
  forall dbenv fenv nenv,
    b_Imp_Lang TRUE_Imp_Lang dbenv fenv nenv true
|Imp_Lang_false : 
  forall dbenv fenv nenv,
    b_Imp_Lang FALSE_Imp_Lang dbenv fenv nenv false
|Imp_Lang_neg : 
  forall dbenv fenv nenv bexp b,
    b_Imp_Lang bexp dbenv fenv nenv b ->
    b_Imp_Lang (NEG_Imp_Lang bexp) dbenv fenv nenv (negb b)
|Imp_Lang_and : 
  forall dbenv fenv nenv bexp1 bexp2 b1 b2, 
    b_Imp_Lang bexp1 dbenv fenv nenv b1 ->
    b_Imp_Lang bexp2 dbenv fenv nenv b2 ->
    b_Imp_Lang (AND_Imp_Lang bexp1 bexp2) dbenv fenv nenv (andb b1 b2)
|Imp_Lang_or : 
  forall dbenv fenv nenv bexp1 bexp2 b1 b2, 
    b_Imp_Lang bexp1 dbenv fenv nenv b1 ->
    b_Imp_Lang bexp2 dbenv fenv nenv b2 ->
    b_Imp_Lang (OR_Imp_Lang bexp1 bexp2) dbenv fenv nenv (orb b1 b2)
|Imp_Lang_leq : 
  forall dbenv fenv nenv a1 a2 n1 n2, 
      a_Imp_Lang a1 dbenv fenv nenv n1 ->
      a_Imp_Lang a2 dbenv fenv nenv n2 -> 
      b_Imp_Lang (LEQ_Imp_Lang a1 a2) dbenv fenv nenv (Nat.leb n1 n2)
with i_Imp_Lang : imp_Imp_Lang -> list nat -> fun_env -> nat_env -> nat_env -> Prop := 
| Imp_Lang_skip : 
  forall dbenv fenv nenv,
    i_Imp_Lang SKIP_Imp_Lang dbenv fenv nenv nenv
| Imp_Lang_if_true :
  forall dbenv fenv nenv nenv' bexp i1 i2, 
    b_Imp_Lang bexp dbenv fenv nenv true ->
    i_Imp_Lang i1 dbenv fenv nenv nenv' ->
    i_Imp_Lang (IF_Imp_Lang bexp i1 i2) dbenv fenv nenv nenv'
| Imp_Lang_if_false :
  forall dbenv fenv nenv nenv' bexp i1 i2, 
    b_Imp_Lang bexp dbenv fenv nenv false ->
    i_Imp_Lang i2 dbenv fenv nenv nenv' ->
    i_Imp_Lang (IF_Imp_Lang bexp i1 i2) dbenv fenv nenv nenv'
| Imp_Lang_assign :
  forall dbenv fenv nenv x a n, 
    a_Imp_Lang a dbenv fenv nenv n ->
    i_Imp_Lang (ASSIGN_Imp_Lang x a) dbenv fenv nenv (update x n nenv)
| Imp_Lang_while_done :
  forall dbenv fenv nenv bexp i, 
    b_Imp_Lang bexp dbenv fenv nenv false ->
    i_Imp_Lang (WHILE_Imp_Lang bexp i) dbenv fenv nenv nenv
| Imp_Lang_while_step :
  forall dbenv fenv nenv nenv' nenv'' bexp i, 
    b_Imp_Lang bexp dbenv fenv nenv true ->
    i_Imp_Lang i dbenv fenv nenv nenv' ->
    i_Imp_Lang (WHILE_Imp_Lang bexp i) dbenv fenv nenv' nenv'' ->
    i_Imp_Lang (WHILE_Imp_Lang bexp i) dbenv fenv nenv nenv''
| Imp_Lang_seq : forall dbenv fenv nenv nenv' nenv'' i1 i2,
    i_Imp_Lang i1 dbenv fenv nenv nenv' ->
    i_Imp_Lang i2 dbenv fenv nenv' nenv'' -> 
    i_Imp_Lang (SEQ_Imp_Lang i1 i2) dbenv fenv nenv nenv''
.


Scheme i_Imp_Lang_mut := Induction for i_Imp_Lang Sort Prop
    with a_Imp_Lang_mut := Induction for a_Imp_Lang Sort Prop
                      with b_Imp_Lang_mut := Induction for b_Imp_Lang Sort Prop
                      with args_Imp_Lang_mut := Induction for args_Imp_Lang Sort Prop.


Combined Scheme i_Imp_Lang_mutind from i_Imp_Lang_mut,a_Imp_Lang_mut,b_Imp_Lang_mut,args_Imp_Lang_mut.


Ltac inv H :=
  inversion H; subst; try (reflexivity || assumption).

Ltac smart_inversion_helper :=
  multimatch goal with
  | [ IH : (forall x, ?imp_lang ?imp_lang_syntax _ _ ?nenv x -> _ = x),
        H: ?imp_lang ?imp_lang_syntax _ _ ?nenv _ |- _ ] => apply IH in H; try (assumption || reflexivity)
  | [ IH: forall n1, ?blah_Imp_Lang ?imp_lang_syntax ?dbenv ?fenv ?nenv n1 -> ?nenv'' = n1, Heq: ?nenv = ?nenv''', Hblah_Imp_Lang: ?blah_Imp_Lang ?imp_lang_syntax ?dbenv ?fenv ?nenv''' ?nenv' |- ?nenv'' = ?nenv' ] =>
      rewrite <- Heq in Hblah_Imp_Lang; apply IH in Hblah_Imp_Lang; assumption
  end.

Ltac smart_rewriter :=
  match goal with
  | [ a : ?T, b : ?T |- _ ] =>
      match goal with
      | [ H: a = b |- _ ] => rewrite H; try reflexivity
      end
  end.


                      
Ltac det_smart_inversion :=
  match goal with
  | [ H': ?imp_lang _ _ _ _ ?res' |- ?res = ?res' ] => inv H'; repeat smart_inversion_helper; repeat smart_rewriter
  end.

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).


Theorem big_step_deterministic :
    (forall i dbenv fenv nenv nenv',
        i_Imp_Lang i dbenv fenv nenv nenv' ->
        forall nenv'',
        i_Imp_Lang i dbenv fenv nenv nenv'' ->
        nenv' = nenv'') /\
      (forall a dbenv fenv nenv n,
          a_Imp_Lang a dbenv fenv nenv n ->
          forall n',
          a_Imp_Lang a dbenv fenv nenv n' ->
          n = n')
    /\
      (forall b dbenv fenv nenv v,
          b_Imp_Lang b dbenv fenv nenv v ->
          forall v',
          b_Imp_Lang b dbenv fenv nenv v' ->
          v = v')
    /\
      (forall args dbenv fenv nenv vals,
          args_Imp_Lang args dbenv fenv nenv vals ->
          forall vals',
          args_Imp_Lang args dbenv fenv nenv vals' ->
          vals = vals').
Proof.
  pose (fun i db f n n0 => fun H: i_Imp_Lang i db f n n0 => forall n1, i_Imp_Lang i db f n n1 -> n0 = n1) as P.
  pose (fun a db f n n0 => fun Ha: a_Imp_Lang a db f n n0 => forall n1, a_Imp_Lang a db f n n1 -> n0 = n1) as P0.
  pose (fun b db f n n0 => fun Hb: b_Imp_Lang b db f n n0 => forall n1, b_Imp_Lang b db f n n1 -> n0 = n1) as P1.
  pose (fun args db f n n0 => fun Hargs: args_Imp_Lang args db f n n0 => forall n1, args_Imp_Lang args db f n n1 -> n0 = n1) as P2.
  apply (i_Imp_Lang_mutind P P0 P1 P2); unfold P, P0, P1, P2 in *; intros; try det_smart_inversion; try discriminate; try (substs; reflexivity).
  - (* The function application case is the one case I couldn't get the automation to work on lol *)
    rewrite H2 in e.
    inversion e.
    reflexivity.
  - rewrite <- H6 in H7.
    apply H0 in H7.
    smart_rewriter.
Qed.

Ltac destruct_imp_lang H :=
  destruct H as [Hi_Imp_Lang [Ha_Imp_Lang [Hb_Imp_Lang Hargs_Imp_Lang]]].

Theorem big_step_deterministic_human_version :
  forall dbenv fenv nenv,
    (forall i nenv' nenv'',
        i_Imp_Lang i dbenv fenv nenv nenv' ->
        i_Imp_Lang i dbenv fenv nenv nenv'' ->
        nenv' = nenv'')
    /\
      (forall a n n',
          a_Imp_Lang a dbenv fenv nenv n ->
          a_Imp_Lang a dbenv fenv nenv n' ->
          n = n')
    /\
      (forall b v v',
          b_Imp_Lang b dbenv fenv nenv v ->
          b_Imp_Lang b dbenv fenv nenv v' ->
          v = v')
    /\
      (forall args vals vals',
          args_Imp_Lang args dbenv fenv nenv vals ->
          args_Imp_Lang args dbenv fenv nenv vals' ->
          vals = vals').
Proof.
  intros dbenv fenv nenv.
  split; [ | split; [ | split ]]; intros; pose proof big_step_deterministic; destruct_imp_lang H1.
  - eapply Hi_Imp_Lang; eassumption.
  - eapply Ha_Imp_Lang; eassumption.
  - eapply Hb_Imp_Lang; eassumption.
  - eapply Hargs_Imp_Lang; eassumption.
Qed.


(* Helper theorems that just show that each relation is deterministic without
 * having to do all the splitting nonsense. *)

Theorem i_Imp_Lang_deterministic :
  forall dbenv fenv nenv i nenv' nenv'',
    i_Imp_Lang i dbenv fenv nenv nenv' ->
    i_Imp_Lang i dbenv fenv nenv nenv'' ->
    nenv' = nenv''.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as DET.
  destruct_imp_lang DET. eapply Hi_Imp_Lang; eassumption.
Qed.

Theorem a_Imp_Lang_deterministic :
  forall dbenv fenv nenv a n n',
    a_Imp_Lang a dbenv fenv nenv n ->
    a_Imp_Lang a dbenv fenv nenv n' ->
    n = n'.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as Hdet.
  destruct_imp_lang Hdet. eapply Ha_Imp_Lang; eassumption.
Qed.

Theorem b_Imp_Lang_deterministic :
  forall dbenv fenv nenv b v v',
    b_Imp_Lang b dbenv fenv nenv v ->
    b_Imp_Lang b dbenv fenv nenv v' ->
    v = v'.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as Hdet.
  destruct_imp_lang Hdet. eapply Hb_Imp_Lang; eassumption.
Qed.

Theorem args_Imp_Lang_deterministic :
  forall dbenv fenv nenv args vals vals',
    args_Imp_Lang args dbenv fenv nenv vals ->
    args_Imp_Lang args dbenv fenv nenv vals' ->
    vals = vals'.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as DET.
  destruct_imp_lang DET. eapply Hargs_Imp_Lang; eassumption.
Qed.




 

Definition options_to_prod_option {A B: Type} (a: option A) (b: option B) : option (A * B) :=
  match (a, b) with
  | (Some a', Some b') => Some (a', b')
  | _ => None
  end.

Definition prod_add (n: nat * nat): nat :=
  match n with
  | (n', n'') => n' + n''
  end.

Definition prod_minus (n: nat * nat) : nat :=
  match n with
  | (n', n'') => n' - n''
  end.
               
Definition option_bind {A B: Type} (a: option A) (f: A -> option B): option B :=
  match a with
  | Some x => f x
  | None => None
  end.

Definition option_map_map {A B C: Type} (f: A -> B -> C) (a: option A) (b: option B): option C :=
  match a with
  | Some a' => option_map (f a') b
  | _ => None
  end.

Definition nat_option_map_2 (f: nat -> nat -> nat) (a b : option nat): option nat :=
  option_map_map f a b.

Definition option_apply {A B : Type} (f: option (A -> B)) (a: A): option B :=
  match f with
  | Some f' => Some (f' a)
  | _ => None
  end.



Print option_map.

Print Nat.add.
Print Nat.sub.
Print Nat.leb.

Print Implicit option_map_map.


(* Temporarily disable printing, without having to remove prints *)
Definition print {T: Type} (x: T) := x.

Definition print_id {T: Type}  (x: T) := x.


Fixpoint eval_aImp_Lang (a: aexp_Imp_Lang) (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option nat :=
  let blah := print "[eval_aImp_Lang" in
  let blah2 := print a in
  let blah3 := print nenv in
  match (print_id fuel) with
    | 0 =>
        let big_res :=
          (match a with
           | CONST_Imp_Lang n => Some n
           | VAR_Imp_Lang x => Some (nenv x)
           | PARAM_Imp_Lang n => nth_error dbenv n                               
           | _ => None
           end) in
        let blah4 := print "eval_aImp_Lang]" in
        big_res
    | S fuel' =>
        let big_res :=
          (
            match a with
            | CONST_Imp_Lang n => Some n
            | VAR_Imp_Lang x => Some (nenv x)
            | PARAM_Imp_Lang n => nth_error dbenv n
            | PLUS_Imp_Lang a1 a2 =>
                option_map_map
                  Nat.add
                  (eval_aImp_Lang a1 fuel' dbenv fenv nenv)
                  (eval_aImp_Lang a2 fuel' dbenv fenv nenv)
            | MINUS_Imp_Lang a1 a2 =>
                option_map_map
                  Nat.sub
                  (eval_aImp_Lang a1 fuel' dbenv fenv nenv)
                  (eval_aImp_Lang a2 fuel' dbenv fenv nenv)
            | APP_Imp_Lang f a =>
                let blah_app := print "[app " in
                let eval_dbenv :=
                  eval_args_Imp_Lang a
                                fuel'
                                dbenv
                                fenv
                                nenv in
                let return_nenv :=
                  (option_bind
                     eval_dbenv
                     (fun dbenv' =>
                        eval_fuel_Imp_Lang ((fenv f).(Body)) fuel' dbenv' fenv init_nenv)) in
                let res :=
                  option_map
                    (fun return_nenv => return_nenv ((fenv f).(Ret)))
                    return_nenv in
                let blah_app_1 := print "app]" in
                res
            end) in
        let blah4' := print big_res in
        let blah4 := print "eval_aImp_Lang]" in
        big_res
  end
with eval_args_Imp_Lang (arg_exprs: list aexp_Imp_Lang)  (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option (list nat) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match arg_exprs with
           | e :: exprs =>
               let result_e := eval_aImp_Lang e fuel' dbenv fenv nenv in
               match result_e with
               | Some v =>
                   match (eval_args_Imp_Lang exprs fuel' dbenv fenv nenv) with
                   | None =>
                       None
                   | Some dbenv' =>
                       Some (cons v dbenv')
                       end
               | None =>
                   None
               end
           | nil =>
               Some nil
           end
       end                                         
with eval_bImp_Lang (b: bexp_Imp_Lang) (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option bool :=
       let blah := print "[eval_bImp_Lang" in
       let blah' := print b in
       match fuel with
       | 0 => let blah2 := print "eval_bImp_Lang]" in
              None
       | S fuel' =>
           let big_res := (match b with
           | TRUE_Imp_Lang => Some true
           | FALSE_Imp_Lang => Some false
           | NEG_Imp_Lang b' =>
               option_map
                 negb
                 (eval_bImp_Lang b' fuel' dbenv fenv nenv)
           | AND_Imp_Lang b1 b2 =>
               option_map_map
                 andb
                 (eval_bImp_Lang b1 fuel' dbenv fenv nenv)
                 (eval_bImp_Lang b2 fuel' dbenv fenv nenv)
           | OR_Imp_Lang  b1 b2 =>
               option_map_map
                 orb
                 (eval_bImp_Lang b1 fuel' dbenv fenv nenv)
                 (eval_bImp_Lang b2 fuel' dbenv fenv nenv)
           | LEQ_Imp_Lang a1 a2 =>
               option_map_map
                 Nat.leb
                 (eval_aImp_Lang a1 fuel' dbenv fenv nenv)
                 (eval_aImp_Lang a2 fuel' dbenv fenv nenv)
                           end) in
           let blah2' := print big_res in
           let blah2 := print "eval_bImp_Lang]" in
           big_res
       end
with eval_fuel_Imp_Lang (i: imp_Imp_Lang) (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option nat_env :=
       let blah := print "[eval_fuel_Imp_Lang" in
       let blah1 := print i in
       let blah2 := print fuel in
       let blah3 := print nenv in
       match fuel with
       | 0 => 
           match i with
           | SKIP_Imp_Lang =>
              Some nenv
           | _ =>
              let blah0 := print "]" in None
           end
       | S fuel' =>
           match (print_id i) with
           | SKIP_Imp_Lang =>
               let blahskip1 := print "]" in
               Some nenv
           | ASSIGN_Imp_Lang x a =>
               let res := eval_aImp_Lang a fuel' dbenv fenv nenv in
               let res' := option_map (fun res => update (print_id x) (print_id res) nenv) res in
               let blahassign1 := print "]" in
               res'
                 
           | IF_Imp_Lang b i1 i2 =>
               let bres := eval_bImp_Lang b fuel' dbenv fenv nenv in
               let next_instruction := option_map (fun (bres': bool) => if bres' then i1 else i2) bres in
               let res: option nat_env := option_bind next_instruction (fun (i: imp_Imp_Lang) => eval_fuel_Imp_Lang i fuel' dbenv fenv nenv) in
               let blahif1 := print "]" in
               res
           | WHILE_Imp_Lang b i' =>
               let bres := eval_bImp_Lang b fuel' dbenv fenv nenv in
               option_bind bres (fun bres' =>
                                   if bres' then
                                     let new_nenv: option nat_env := eval_fuel_Imp_Lang i' fuel' dbenv fenv nenv in
                                     let res: option nat_env := option_bind new_nenv (eval_fuel_Imp_Lang i fuel' dbenv fenv) in
                                     let blahwhile1 := print "]" in
                                     res
                                   else
                                     Some nenv)
           | SEQ_Imp_Lang i1 i2 =>
               let new_nenv: option nat_env := eval_fuel_Imp_Lang i1 fuel' dbenv fenv nenv in
               let res: option nat_env := option_bind new_nenv (eval_fuel_Imp_Lang i2 fuel' dbenv fenv) in
               let blahseq1 := print "]" in
               res
           end
       end.

Definition default_fuel := 1000.

Ltac invc H :=
  inversion H; subst; clear H.

Ltac duplicate_proof H H' :=
  pose proof H as H'.

Tactic Notation "dupe" ident(H) "as" ident(H') := (duplicate_proof H H').

Fixpoint construct_fenv lst (f: fun_env) : fun_env :=
  match lst with
  | nil => f
  | foo::foos => construct_fenv foos (update ((foo).(Name)) foo f)
  end.

Definition eval_fuel_pImp_Lang (p: prog_Imp_Lang) (fuel: nat) (nenv: nat_env): option nat_env :=
  match p with
  | PROF_Imp_Lang lst imp =>
      let new_fenv := construct_fenv lst init_fenv in
      eval_fuel_Imp_Lang imp fuel nil new_fenv init_nenv
  end.
