From Coq Require Import Arith Psatz Bool String List Program.Equality Logic.Eqdep_dec Nat.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Definition ident := string.

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


Inductive aexp_Dan :=
| CONST_Dan (n: nat)
| VAR_Dan (x: ident)
| PARAM_Dan (n: nat)
| PLUS_Dan (a1 a2: aexp_Dan)
| MINUS_Dan (a1 a2: aexp_Dan)
| APP_Dan (f: ident) (aexps : list aexp_Dan).

(*
 * Custom induction principle with stronger handling of containers,
 * based on this trick: https://pastebin.com/BAvg3Jdh
 *)
Section aexp_Dan_ind2.
  Variable P: aexp_Dan -> Prop. (* this is the property we want to prove *)
 
  (* For each constructor, we add a Variable *)
  Variable fconst : forall n : nat, P (CONST_Dan n).
  Variable fvar : forall x : ident, P (VAR_Dan x).
  Variable fparam : forall n : nat, P (PARAM_Dan n).
  Variable fplus :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P (PLUS_Dan a1 a2).
  Variable fminus :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P (MINUS_Dan a1 a2).
  Variable fapp :
    forall f (aexps : list aexp_Dan), List.Forall P aexps -> P (APP_Dan f aexps).

  Fixpoint aexp_Dan_ind2 (a : aexp_Dan) : P a :=
    match a as a0 return (P a0) with
    | CONST_Dan n => fconst n
    | VAR_Dan x => fvar x
    | PARAM_Dan n => fparam n
    | PLUS_Dan a1 a2 => fplus a1 (aexp_Dan_ind2 a1) a2 (aexp_Dan_ind2 a2)
    | MINUS_Dan a1 a2 => fminus a1 (aexp_Dan_ind2 a1) a2 (aexp_Dan_ind2 a2)
    | APP_Dan f aexps =>
        fapp f aexps
          ((fix L aexps := 
             match aexps return (Forall P aexps) with
             | nil => Forall_nil _
             | cons a aexps_tl => Forall_cons a (aexp_Dan_ind2 a) (L aexps_tl) end) aexps)
    end.
End aexp_Dan_ind2.

(* set version *)
Section aexp_Dan_rec2.
  Variable P: aexp_Dan -> Set. (* this is the property we want to prove *)
 
  (* For each constructor, we add a Variable *)
  Variable fconst : forall n : nat, P (CONST_Dan n).
  Variable fvar : forall x : ident, P (VAR_Dan x).
  Variable fparam : forall n : nat, P (PARAM_Dan n).
  Variable fplus :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P (PLUS_Dan a1 a2).
  Variable fminus :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P (MINUS_Dan a1 a2).

   Inductive SForall : list aexp_Dan -> Set :=
   | SForall_nil : SForall nil
   | SForall_cons : forall x l, P x -> SForall l -> SForall (x::l).

  Variable fapp :
    forall f (aexps : list aexp_Dan), SForall aexps -> P (APP_Dan f aexps).

  Fixpoint aexp_Dan_rec2 (a : aexp_Dan) : P a :=
    match a as a0 return (P a0) with
    | CONST_Dan n => fconst n
    | VAR_Dan x => fvar x
    | PARAM_Dan n => fparam n
    | PLUS_Dan a1 a2 => fplus a1 (aexp_Dan_rec2 a1) a2 (aexp_Dan_rec2 a2)
    | MINUS_Dan a1 a2 => fminus a1 (aexp_Dan_rec2 a1) a2 (aexp_Dan_rec2 a2)
    | APP_Dan f aexps =>
        fapp f aexps
          ((fix L aexps := 
             match aexps return (SForall aexps) with
             | nil => SForall_nil
             | cons a aexps_tl => SForall_cons a _ (aexp_Dan_rec2 a) (L aexps_tl) end) aexps)
    end.
End aexp_Dan_rec2.

(* Definition aexp_vector (n: nat): Type := VectorDef.t aexp_Dan n. *)

(* Definition nil_aexp_vector: aexp_vector 0 := nil aexp_Dan. *)

Declare Scope dantrick_scope.

Infix "+d" := PLUS_Dan (at level 76) : dantrick_scope.
Infix "-d" := MINUS_Dan (at level 76) : dantrick_scope.
Infix "@d" := APP_Dan (at level 76) : dantrick_scope.

Inductive bexp_Dan := 
| TRUE_Dan
| FALSE_Dan
| NEG_Dan (b: bexp_Dan)
| AND_Dan (b1 b2: bexp_Dan)
| OR_Dan  (b1 b2: bexp_Dan)
| LEQ_Dan (a1 a2: aexp_Dan).

Definition eq_Dan (a b : aexp_Dan) : bexp_Dan :=
  AND_Dan (LEQ_Dan a b) (LEQ_Dan b a).
Definition geq_Dan (a b : aexp_Dan) : bexp_Dan :=
  LEQ_Dan b a.
Definition neq_Dan (a b : aexp_Dan) : bexp_Dan :=
  NEG_Dan (eq_Dan a b).
Definition lt_Dan (a b : aexp_Dan) : bexp_Dan :=
  AND_Dan (LEQ_Dan a b) (neq_Dan a b).
Definition gt_Dan (a b : aexp_Dan) : bexp_Dan :=
  lt_Dan b a.

Notation "a '=d' b" := (eq_Dan a b) (at level 50) : dantrick_scope.
Infix "&d" := AND_Dan (at level 50) : dantrick_scope.
Infix "|d" := OR_Dan (at level 50) : dantrick_scope.
Notation "'!d' a" := (NEG_Dan a) (at level 80) : dantrick_scope.
Infix "<=d" := LEQ_Dan (at level 90) : dantrick_scope.
Notation "a '>=d' b" := (geq_Dan a b) (at level 90) : dantrick_scope.
Notation "a '!=d' b" := (neq_Dan a b) (at level 90) : dantrick_scope.
Notation "a '<d' b" := (lt_Dan a b) (at level 90) : dantrick_scope.
Notation "a '>d' b" := (gt_Dan a b) (at level 90) : dantrick_scope.

Inductive imp_Dan :=
  |IF_Dan (b: bexp_Dan) (i1 i2: imp_Dan)
  |SKIP_Dan
  |WHILE_Dan (b: bexp_Dan) (i: imp_Dan)
  |ASSIGN_Dan (x: ident) (a: aexp_Dan)
|SEQ_Dan (i1 i2: imp_Dan).

Section imp_Dan_ind2.
  Variable P: aexp_Dan -> Prop. (* this is the property we want to prove *)
  Variable P0: bexp_Dan -> Prop.
  Variable P1: imp_Dan -> Prop.
 
  (* For each constructor, we add a Variable *)
  Variable fconst : forall n : nat, P (CONST_Dan n).
  Variable fvar : forall x : ident, P (VAR_Dan x).
  Variable fparam : forall n : nat, P (PARAM_Dan n).
  Variable fplus :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P (PLUS_Dan a1 a2).
  Variable fminus :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P (MINUS_Dan a1 a2).
  Variable fapp :
    forall f (aexps : list aexp_Dan), List.Forall P aexps -> P (APP_Dan f aexps).
  Variable ftrue : P0 (TRUE_Dan).
  Variable ffalse : P0 (FALSE_Dan).
  Variable fneg : forall b: bexp_Dan, P0 b -> P0 (NEG_Dan b).
  Variable fand : forall b1: bexp_Dan, P0 b1 -> forall b2: bexp_Dan, P0 b2 -> P0 (AND_Dan b1 b2).
  Variable f_or : forall b1: bexp_Dan, P0 b1 -> forall b2: bexp_Dan, P0 b2 -> P0 (OR_Dan b1 b2).
  Variable fleq :
    forall a1 : aexp_Dan, P a1 -> forall a2 : aexp_Dan, P a2 -> P0 (LEQ_Dan a1 a2).
  Variable fskip : P1 SKIP_Dan.
  Variable fassign : forall x: ident, forall a: aexp_Dan, P a -> P1 (ASSIGN_Dan x a).
  Variable fseq : forall i1: imp_Dan, P1 i1 -> forall i2: imp_Dan, P1 i2 -> P1 (SEQ_Dan i1 i2).
  Variable fif : forall b: bexp_Dan, P0 b -> forall i1: imp_Dan, P1 i1 -> forall i2: imp_Dan, P1 i2 -> P1 (IF_Dan b i1 i2).
  Variable fwhile : forall b: bexp_Dan, P0 b -> forall i: imp_Dan, P1 i -> P1 (WHILE_Dan b i).

  Fixpoint imp_aexp_Dan_ind2 (a : aexp_Dan) : P a :=
    match a as a0 return (P a0) with
    | CONST_Dan n => fconst n
    | VAR_Dan x => fvar x
    | PARAM_Dan n => fparam n
    | PLUS_Dan a1 a2 => fplus a1 (imp_aexp_Dan_ind2 a1) a2 (imp_aexp_Dan_ind2 a2)
    | MINUS_Dan a1 a2 => fminus a1 (imp_aexp_Dan_ind2 a1) a2 (imp_aexp_Dan_ind2 a2)
    | APP_Dan f aexps =>
        fapp f aexps
          ((fix L aexps := 
             match aexps return (Forall P aexps) with
             | nil => Forall_nil _
             | cons a aexps_tl => Forall_cons a (imp_aexp_Dan_ind2 a) (L aexps_tl) end) aexps)
    end.
  Fixpoint imp_Dan_ind2 (i: imp_Dan): P1 i :=
           match i as i0 return (P1 i0) with
           | SKIP_Dan => fskip
           | ASSIGN_Dan x a => fassign x a (imp_aexp_Dan_ind2 a)
           | SEQ_Dan i1 i2 => fseq i1 (imp_Dan_ind2 i1) i2 (imp_Dan_ind2 i2)
           | IF_Dan b i1 i2 =>
               fif b ((fix imp_bexp_Dan_ind2 (b: bexp_Dan) : P0 b :=
                         match b as b0 return (P0 b0) with
                         | TRUE_Dan => ftrue
                         | FALSE_Dan => ffalse
                         | NEG_Dan b => fneg b (imp_bexp_Dan_ind2 b)
                         | AND_Dan b1 b2 => fand b1 (imp_bexp_Dan_ind2 b1) b2 (imp_bexp_Dan_ind2 b2)
                         | OR_Dan b1 b2 => f_or b1 (imp_bexp_Dan_ind2 b1) b2 (imp_bexp_Dan_ind2 b2)
                         | LEQ_Dan a1 a2 => fleq a1 (imp_aexp_Dan_ind2 a1) a2 (imp_aexp_Dan_ind2 a2)
                         end) b)
                   i1 (imp_Dan_ind2 i1) i2 (imp_Dan_ind2 i2)
           | WHILE_Dan b i =>
               fwhile b ((fix imp_bexp_Dan_ind2 (b: bexp_Dan) : P0 b :=
                            match b as b0 return (P0 b0) with
                            | TRUE_Dan => ftrue
                            | FALSE_Dan => ffalse
                            | NEG_Dan b => fneg b (imp_bexp_Dan_ind2 b)
                            | AND_Dan b1 b2 => fand b1 (imp_bexp_Dan_ind2 b1) b2 (imp_bexp_Dan_ind2 b2)
                            | OR_Dan b1 b2 => f_or b1 (imp_bexp_Dan_ind2 b1) b2 (imp_bexp_Dan_ind2 b2)
                            | LEQ_Dan a1 a2 => fleq a1 (imp_aexp_Dan_ind2 a1) a2 (imp_aexp_Dan_ind2 a2)
                            end) b)
                      i (imp_Dan_ind2 i)
           end.
End imp_Dan_ind2.

Notation "x <- e" := (ASSIGN_Dan x e) (at level 75) : dantrick_scope.
Infix ";;" := SEQ_Dan (at level 76) : dantrick_scope.
Notation "'when' b 'then' t 'else' e 'done'" :=
  (IF_Dan b t e) (at level 75, b at level 0) : dantrick_scope.
Notation "'while' b 'loop' body 'done'" :=
  (WHILE_Dan b body) (at level 75) : dantrick_scope.

Local Open Scope dantrick_scope.

Record fun_Dan :=
  { Name: ident
  ; Args : nat
  ; Ret: ident
  ; Body: imp_Dan }.

Definition fun_env := store fun_Dan. 

Definition init_fenv: fun_env := fun _ => {| Name := "id"
                                          ; Args := 1
                                          ; Ret := "x"
                                          ; Body := "x" <- (PARAM_Dan 0) |}.

Inductive prog_Dan :=
| PROF_Dan (l: list fun_Dan) (i: imp_Dan).


Local Open Scope vector_scope.

Inductive a_Dan : aexp_Dan -> list nat -> fun_env -> nat_env -> nat -> Prop :=
| Dan_const : 
  forall dbenv fenv nenv n,
    a_Dan (CONST_Dan n) dbenv fenv nenv n
| Dan_var :
  forall dbenv fenv nenv x n,
    (nenv x = n) ->
    a_Dan (VAR_Dan x) dbenv fenv nenv n
| Dan_param :
  forall dbenv fenv nenv n m,
    0 <= n < List.length dbenv ->
    nth_error dbenv n = Some m ->
    a_Dan (PARAM_Dan n) dbenv fenv nenv m
| Dan_plus : 
  forall dbenv fenv nenv a1 a2 n1 n2, 
    a_Dan a1 dbenv fenv nenv n1 ->
    a_Dan a2 dbenv fenv nenv n2 -> 
    a_Dan (PLUS_Dan a1 a2) dbenv fenv nenv (n1 + n2)
| Dan_minus : 
  forall dbenv fenv nenv a1 a2 n1 n2, 
    a_Dan a1 dbenv fenv nenv n1 ->
    a_Dan a2 dbenv fenv nenv n2 -> 
    a_Dan (MINUS_Dan a1 a2) dbenv fenv nenv (n1 - n2)
| Dan_app : 
  forall dbenv fenv nenv nenv'' func aexps ns ret f, 
    (fenv f = func) ->
    (Args func) = Datatypes.length aexps ->
    args_Dan aexps dbenv fenv nenv ns ->
    (i_Dan (func).(Body) ns fenv init_nenv nenv'') ->
    (nenv'' ((func).(Ret)) = ret) ->
    a_Dan (APP_Dan f aexps) dbenv fenv nenv ret
with args_Dan: list aexp_Dan -> list nat -> fun_env -> nat_env -> list nat -> Prop :=
| args_nil :
  forall dbenv fenv nenv,
    args_Dan nil dbenv fenv nenv nil%list
| args_cons :
  forall aexp aexps dbenv fenv nenv v vals,
    a_Dan aexp dbenv fenv nenv v -> 
    args_Dan aexps dbenv fenv nenv vals ->
    args_Dan (aexp :: aexps) dbenv fenv nenv (v :: vals)
with b_Dan: bexp_Dan -> list nat -> fun_env -> nat_env -> bool -> Prop :=
|Dan_true : 
  forall dbenv fenv nenv,
    b_Dan TRUE_Dan dbenv fenv nenv true
|Dan_false : 
  forall dbenv fenv nenv,
    b_Dan FALSE_Dan dbenv fenv nenv false
|Dan_neg : 
  forall dbenv fenv nenv bexp b,
    b_Dan bexp dbenv fenv nenv b ->
    b_Dan (NEG_Dan bexp) dbenv fenv nenv (negb b)
|Dan_and : 
  forall dbenv fenv nenv bexp1 bexp2 b1 b2, 
    b_Dan bexp1 dbenv fenv nenv b1 ->
    b_Dan bexp2 dbenv fenv nenv b2 ->
    b_Dan (AND_Dan bexp1 bexp2) dbenv fenv nenv (andb b1 b2)
|Dan_or : 
  forall dbenv fenv nenv bexp1 bexp2 b1 b2, 
    b_Dan bexp1 dbenv fenv nenv b1 ->
    b_Dan bexp2 dbenv fenv nenv b2 ->
    b_Dan (OR_Dan bexp1 bexp2) dbenv fenv nenv (orb b1 b2)
|Dan_leq : 
  forall dbenv fenv nenv a1 a2 n1 n2, 
      a_Dan a1 dbenv fenv nenv n1 ->
      a_Dan a2 dbenv fenv nenv n2 -> 
      b_Dan (LEQ_Dan a1 a2) dbenv fenv nenv (Nat.leb n1 n2)
with i_Dan : imp_Dan -> list nat -> fun_env -> nat_env -> nat_env -> Prop := 
| Dan_skip : 
  forall dbenv fenv nenv,
    i_Dan SKIP_Dan dbenv fenv nenv nenv
| Dan_if_true :
  forall dbenv fenv nenv nenv' bexp i1 i2, 
    b_Dan bexp dbenv fenv nenv true ->
    i_Dan i1 dbenv fenv nenv nenv' ->
    i_Dan (IF_Dan bexp i1 i2) dbenv fenv nenv nenv'
| Dan_if_false :
  forall dbenv fenv nenv nenv' bexp i1 i2, 
    b_Dan bexp dbenv fenv nenv false ->
    i_Dan i2 dbenv fenv nenv nenv' ->
    i_Dan (IF_Dan bexp i1 i2) dbenv fenv nenv nenv'
| Dan_assign :
  forall dbenv fenv nenv x a n, 
    a_Dan a dbenv fenv nenv n ->
    i_Dan (ASSIGN_Dan x a) dbenv fenv nenv (update x n nenv)
| Dan_while_done :
  forall dbenv fenv nenv bexp i, 
    b_Dan bexp dbenv fenv nenv false ->
    i_Dan (WHILE_Dan bexp i) dbenv fenv nenv nenv
| Dan_while_step :
  forall dbenv fenv nenv nenv' nenv'' bexp i, 
    b_Dan bexp dbenv fenv nenv true ->
    i_Dan i dbenv fenv nenv nenv' ->
    i_Dan (WHILE_Dan bexp i) dbenv fenv nenv' nenv'' ->
    i_Dan (WHILE_Dan bexp i) dbenv fenv nenv nenv''
| Dan_seq : forall dbenv fenv nenv nenv' nenv'' i1 i2,
    i_Dan i1 dbenv fenv nenv nenv' ->
    i_Dan i2 dbenv fenv nenv' nenv'' -> 
    i_Dan (SEQ_Dan i1 i2) dbenv fenv nenv nenv''
.


Scheme i_Dan_mut := Induction for i_Dan Sort Prop
    with a_Dan_mut := Induction for a_Dan Sort Prop
                      with b_Dan_mut := Induction for b_Dan Sort Prop
                      with args_Dan_mut := Induction for args_Dan Sort Prop.


Combined Scheme i_Dan_mutind from i_Dan_mut,a_Dan_mut,b_Dan_mut,args_Dan_mut.


Ltac inv H :=
  inversion H; subst; try (reflexivity || assumption).

Ltac smart_inversion_helper :=
  multimatch goal with
  | [ IH : (forall x, ?dan ?dan_syntax _ _ ?nenv x -> _ = x),
        H: ?dan ?dan_syntax _ _ ?nenv _ |- _ ] => apply IH in H; try (assumption || reflexivity)
  | [ IH: forall n1, ?blah_Dan ?dan_syntax ?dbenv ?fenv ?nenv n1 -> ?nenv'' = n1, Heq: ?nenv = ?nenv''', Hblah_Dan: ?blah_Dan ?dan_syntax ?dbenv ?fenv ?nenv''' ?nenv' |- ?nenv'' = ?nenv' ] =>
      rewrite <- Heq in Hblah_Dan; apply IH in Hblah_Dan; assumption
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
  | [ H': ?dan _ _ _ _ ?res' |- ?res = ?res' ] => inv H'; repeat smart_inversion_helper; repeat smart_rewriter
  end.

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).


Theorem big_step_deterministic :
    (forall i dbenv fenv nenv nenv',
        i_Dan i dbenv fenv nenv nenv' ->
        forall nenv'',
        i_Dan i dbenv fenv nenv nenv'' ->
        nenv' = nenv'') /\
      (forall a dbenv fenv nenv n,
          a_Dan a dbenv fenv nenv n ->
          forall n',
          a_Dan a dbenv fenv nenv n' ->
          n = n')
    /\
      (forall b dbenv fenv nenv v,
          b_Dan b dbenv fenv nenv v ->
          forall v',
          b_Dan b dbenv fenv nenv v' ->
          v = v')
    /\
      (forall args dbenv fenv nenv vals,
          args_Dan args dbenv fenv nenv vals ->
          forall vals',
          args_Dan args dbenv fenv nenv vals' ->
          vals = vals').
Proof.
  pose (fun i db f n n0 => fun H: i_Dan i db f n n0 => forall n1, i_Dan i db f n n1 -> n0 = n1) as P.
  pose (fun a db f n n0 => fun Ha: a_Dan a db f n n0 => forall n1, a_Dan a db f n n1 -> n0 = n1) as P0.
  pose (fun b db f n n0 => fun Hb: b_Dan b db f n n0 => forall n1, b_Dan b db f n n1 -> n0 = n1) as P1.
  pose (fun args db f n n0 => fun Hargs: args_Dan args db f n n0 => forall n1, args_Dan args db f n n1 -> n0 = n1) as P2.
  apply (i_Dan_mutind P P0 P1 P2); unfold P, P0, P1, P2 in *; intros; try det_smart_inversion; try discriminate; try (substs; reflexivity).
  - (* The function application case is the one case I couldn't get the automation to work on lol *)
    rewrite H2 in e.
    inversion e.
    reflexivity.
  - rewrite <- H6 in H7.
    apply H0 in H7.
    smart_rewriter.
Qed.

Ltac destruct_dan H :=
  destruct H as [Hi_Dan [Ha_Dan [Hb_Dan Hargs_Dan]]].

Theorem big_step_deterministic_human_version :
  forall dbenv fenv nenv,
    (forall i nenv' nenv'',
        i_Dan i dbenv fenv nenv nenv' ->
        i_Dan i dbenv fenv nenv nenv'' ->
        nenv' = nenv'')
    /\
      (forall a n n',
          a_Dan a dbenv fenv nenv n ->
          a_Dan a dbenv fenv nenv n' ->
          n = n')
    /\
      (forall b v v',
          b_Dan b dbenv fenv nenv v ->
          b_Dan b dbenv fenv nenv v' ->
          v = v')
    /\
      (forall args vals vals',
          args_Dan args dbenv fenv nenv vals ->
          args_Dan args dbenv fenv nenv vals' ->
          vals = vals').
Proof.
  intros dbenv fenv nenv.
  split; [ | split; [ | split ]]; intros; pose proof big_step_deterministic; destruct_dan H1.
  - eapply Hi_Dan; eassumption.
  - eapply Ha_Dan; eassumption.
  - eapply Hb_Dan; eassumption.
  - eapply Hargs_Dan; eassumption.
Qed.


(* Helper theorems that just show that each relation is deterministic without
 * having to do all the splitting nonsense. *)

Theorem i_Dan_deterministic :
  forall dbenv fenv nenv i nenv' nenv'',
    i_Dan i dbenv fenv nenv nenv' ->
    i_Dan i dbenv fenv nenv nenv'' ->
    nenv' = nenv''.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as DET.
  destruct_dan DET. eapply Hi_Dan; eassumption.
Qed.

Theorem a_Dan_deterministic :
  forall dbenv fenv nenv a n n',
    a_Dan a dbenv fenv nenv n ->
    a_Dan a dbenv fenv nenv n' ->
    n = n'.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as Hdet.
  destruct_dan Hdet. eapply Ha_Dan; eassumption.
Qed.

Theorem b_Dan_deterministic :
  forall dbenv fenv nenv b v v',
    b_Dan b dbenv fenv nenv v ->
    b_Dan b dbenv fenv nenv v' ->
    v = v'.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as Hdet.
  destruct_dan Hdet. eapply Hb_Dan; eassumption.
Qed.

Theorem args_Dan_deterministic :
  forall dbenv fenv nenv args vals vals',
    args_Dan args dbenv fenv nenv vals ->
    args_Dan args dbenv fenv nenv vals' ->
    vals = vals'.
Proof.
  intros. pose proof (big_step_deterministic_human_version dbenv fenv nenv) as DET.
  destruct_dan DET. eapply Hargs_Dan; eassumption.
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


Fixpoint eval_aDan (a: aexp_Dan) (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option nat :=
  let blah := print "[eval_aDan" in
  let blah2 := print a in
  let blah3 := print nenv in
  match (print_id fuel) with
    | 0 =>
        let big_res :=
          (match a with
           | CONST_Dan n => Some n
           | VAR_Dan x => Some (nenv x)
           | PARAM_Dan n => nth_error dbenv n                               
           | _ => None
           end) in
        let blah4 := print "eval_aDan]" in
        big_res
    | S fuel' =>
        let big_res :=
          (
            match a with
            | CONST_Dan n => Some n
            | VAR_Dan x => Some (nenv x)
            | PARAM_Dan n => nth_error dbenv n
            | PLUS_Dan a1 a2 =>
                option_map_map
                  Nat.add
                  (eval_aDan a1 fuel' dbenv fenv nenv)
                  (eval_aDan a2 fuel' dbenv fenv nenv)
            | MINUS_Dan a1 a2 =>
                option_map_map
                  Nat.sub
                  (eval_aDan a1 fuel' dbenv fenv nenv)
                  (eval_aDan a2 fuel' dbenv fenv nenv)
            | APP_Dan f a =>
                let blah_app := print "[app " in
                let eval_dbenv :=
                  eval_args_Dan a
                                fuel'
                                dbenv
                                fenv
                                nenv in
                let return_nenv :=
                  (option_bind
                     eval_dbenv
                     (fun dbenv' =>
                        eval_fuel_Dan ((fenv f).(Body)) fuel' dbenv' fenv init_nenv)) in
                let res :=
                  option_map
                    (fun return_nenv => return_nenv ((fenv f).(Ret)))
                    return_nenv in
                let blah_app_1 := print "app]" in
                res
            end) in
        let blah4' := print big_res in
        let blah4 := print "eval_aDan]" in
        big_res
  end
with eval_args_Dan (arg_exprs: list aexp_Dan)  (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option (list nat) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match arg_exprs with
           | e :: exprs =>
               let result_e := eval_aDan e fuel' dbenv fenv nenv in
               match result_e with
               | Some v =>
                   match (eval_args_Dan exprs fuel' dbenv fenv nenv) with
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
with eval_bDan (b: bexp_Dan) (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option bool :=
       let blah := print "[eval_bDan" in
       let blah' := print b in
       match fuel with
       | 0 => let blah2 := print "eval_bDan]" in
              None
       | S fuel' =>
           let big_res := (match b with
           | TRUE_Dan => Some true
           | FALSE_Dan => Some false
           | NEG_Dan b' =>
               option_map
                 negb
                 (eval_bDan b' fuel' dbenv fenv nenv)
           | AND_Dan b1 b2 =>
               option_map_map
                 andb
                 (eval_bDan b1 fuel' dbenv fenv nenv)
                 (eval_bDan b2 fuel' dbenv fenv nenv)
           | OR_Dan  b1 b2 =>
               option_map_map
                 orb
                 (eval_bDan b1 fuel' dbenv fenv nenv)
                 (eval_bDan b2 fuel' dbenv fenv nenv)
           | LEQ_Dan a1 a2 =>
               option_map_map
                 Nat.leb
                 (eval_aDan a1 fuel' dbenv fenv nenv)
                 (eval_aDan a2 fuel' dbenv fenv nenv)
                           end) in
           let blah2' := print big_res in
           let blah2 := print "eval_bDan]" in
           big_res
       end
with eval_fuel_Dan (i: imp_Dan) (fuel: nat) (dbenv: list nat) (fenv: fun_env) (nenv: nat_env) : option nat_env :=
       let blah := print "[eval_fuel_Dan" in
       let blah1 := print i in
       let blah2 := print fuel in
       let blah3 := print nenv in
       match fuel with
       | 0 => 
           match i with
           | SKIP_Dan =>
              Some nenv
           | _ =>
              let blah0 := print "]" in None
           end
       | S fuel' =>
           match (print_id i) with
           | SKIP_Dan =>
               let blahskip1 := print "]" in
               Some nenv
           | ASSIGN_Dan x a =>
               let res := eval_aDan a fuel' dbenv fenv nenv in
               let res' := option_map (fun res => update (print_id x) (print_id res) nenv) res in
               let blahassign1 := print "]" in
               res'
                 
           | IF_Dan b i1 i2 =>
               let bres := eval_bDan b fuel' dbenv fenv nenv in
               let next_instruction := option_map (fun (bres': bool) => if bres' then i1 else i2) bres in
               let res: option nat_env := option_bind next_instruction (fun (i: imp_Dan) => eval_fuel_Dan i fuel' dbenv fenv nenv) in
               let blahif1 := print "]" in
               res
           | WHILE_Dan b i' =>
               let bres := eval_bDan b fuel' dbenv fenv nenv in
               option_bind bres (fun bres' =>
                                   if bres' then
                                     let new_nenv: option nat_env := eval_fuel_Dan i' fuel' dbenv fenv nenv in
                                     let res: option nat_env := option_bind new_nenv (eval_fuel_Dan i fuel' dbenv fenv) in
                                     let blahwhile1 := print "]" in
                                     res
                                   else
                                     Some nenv)
           | SEQ_Dan i1 i2 =>
               let new_nenv: option nat_env := eval_fuel_Dan i1 fuel' dbenv fenv nenv in
               let res: option nat_env := option_bind new_nenv (eval_fuel_Dan i2 fuel' dbenv fenv) in
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

Definition eval_fuel_pDan (p: prog_Dan) (fuel: nat) (nenv: nat_env): option nat_env :=
  match p with
  | PROF_Dan lst imp =>
      let new_fenv := construct_fenv lst init_fenv in
      eval_fuel_Dan imp fuel nil new_fenv init_nenv
  end.
