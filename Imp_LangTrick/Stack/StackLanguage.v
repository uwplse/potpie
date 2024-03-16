From Coq Require Import Arith Psatz Bool String List Program.Equality Nat.
From Imp_LangTrick Require Export Base.
Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Definition stack := list nat.
(* Definition ident := string. *)
Definition stack_index := nat.
Definition store (T: Type) : Type := ident -> T.

Fixpoint update_stack_helper (stk: stack) (acc: stack) (index: stack_index) (value: nat): option stack :=
  match index with
  | 0 => None
  | 1 =>
      match stk with
      | v :: stk' => Some (rev_append acc (value :: stk'))
      | _ => None
      end
  | S index' =>
      match stk with
      | v :: stk' => update_stack_helper stk' (v :: acc) index' value
      | _ => None
      end
  end.

Definition update_stack (stk: stack) (index: stack_index) (value: nat): option stack :=
  if Nat.leb 1 index then
    (if (Nat.leb index (List.length stk)) then
       (update_stack_helper stk nil index value)
     else None)
  else None.


Declare Scope stack_scope.
Declare Scope stack_arith_scope.

Inductive aexp_stack :=
| Const_Stk (n: nat)
| Var_Stk (n: stack_index)
| Plus_Stk (a1 a2: aexp_stack)
| Minus_Stk (a1 a2: aexp_stack)
| App_Stk (f: ident) (aexps: list aexp_stack).

Section aexp_stack_ind2.
  Variable P: aexp_stack -> Prop.

  Variable fconst : forall n: nat, P (Const_Stk n).
  Variable fvar: forall n: nat, P (Var_Stk n).
  Variable fplus : forall a1: aexp_stack, P a1 -> forall a2: aexp_stack, P a2 -> P (Plus_Stk a1 a2).
  Variable fminus : forall a1: aexp_stack, P a1 -> forall a2: aexp_stack, P a2 -> P (Minus_Stk a1 a2).
  Variable fapp:
    forall f (aexps: list aexp_stack), List.Forall P aexps -> P (App_Stk f aexps).

  Fixpoint aexp_stack_ind2 (a: aexp_stack): P a :=
    match a as a0 return (P a0) with
    | Const_Stk n => fconst n
    | Var_Stk k => fvar k
    | Plus_Stk a1 a2 => fplus a1 (aexp_stack_ind2 a1) a2 (aexp_stack_ind2 a2)
    | Minus_Stk a1 a2 => fminus a1 (aexp_stack_ind2 a1) a2 (aexp_stack_ind2 a2)
    | App_Stk f aexps =>
        fapp f aexps
             ((fix L aexps :=
                 match aexps return (Forall P aexps) with
                 | nil => Forall_nil _
                 | cons a aexps_tl => Forall_cons a (aexp_stack_ind2 a) (L aexps_tl) end) aexps)
    end.
End aexp_stack_ind2.

Coercion Const_Stk : nat >-> aexp_stack.
Notation "# n" := (Var_Stk n) (at level 0, format "'#' n") : stack_arith_scope.
Infix "+s" := Plus_Stk (at level 76) : stack_arith_scope.
Infix "-s" := Minus_Stk (at level 76) : stack_arith_scope.
Infix "@s" := App_Stk (at level 76) : stack_arith_scope.

Inductive bexp_stack :=
| True_Stk
| False_Stk
| Neg_Stk (b: bexp_stack)
| And_Stk (b1 b2: bexp_stack)
| Or_Stk (b1 b2: bexp_stack)
| Leq_Stk (a1 a2: aexp_stack)
| Eq_Stk (a1 a2: aexp_stack).

Check bexp_stack.

Delimit Scope stack_arith_scope with aexp_stack.
Bind Scope stack_arith_scope with aexp_stack.

Declare Scope stack_bool_scope.
Delimit Scope stack_bool_scope with bexp_stack.
Bind Scope stack_bool_scope with bexp_stack.

Notation "'Trues'" := True_Stk (at level 50) : stack_bool_scope.
Notation "'Falses'" := False_Stk (at level 50) : stack_bool_scope.
Notation "'!s' b" := (Neg_Stk b) (at level 80) : stack_bool_scope.
Infix "&s" := And_Stk (at level 50) : stack_bool_scope.
Infix "|s" := Or_Stk (at level 50) : stack_bool_scope.
Notation "a '<=s' b" := (Leq_Stk a%aexp_stack b%aexp_stack) (at level 90) : stack_bool_scope.

Inductive imp_stack :=
| Skip_Stk
| Assign_Stk (k: nat) (a: aexp_stack)
| Push_Stk
| Pop_Stk
| Seq_Stk (i1 i2: imp_stack)
| If_Stk (b: bexp_stack) (i1 i2: imp_stack)
| While_Stk (b: bexp_stack) (i: imp_stack).


Notation "'skips'" := Skip_Stk : stack_scope.
Notation "# k <- a" :=
  (Assign_Stk k a%aexp_stack)
    (at level 75,
      format "'#' k  '<-'  '[   ' a ']'") : stack_scope.
Notation "'push'" := Push_Stk : stack_scope.
Notation "'pop'" := Pop_Stk : stack_scope.
Notation "i1 ;;; i2" := (Seq_Stk i1 i2) (at level 76, format "i1 ';;;' '//' i2", no associativity) : stack_scope.
Notation "'ifs' b 'thens' t 'elses' e 'dones'" :=
  (If_Stk b%bexp_stack t e)
    (at level 75,
      b at level 0,
    format "'ifs'  b  'thens' '//'   '[' t ']' '//' 'elses' '//'   '[' e ']' '//' 'dones'") : stack_scope.
Notation "'whiles' b 'loops' body 'dones'" :=
  (While_Stk b%bexp_stack body)
    (at level 75,
      format "'whiles'  b  'loops' '//'   '[' body ']' '//' 'dones'") : stack_scope.

Local Open Scope stack_scope.

Compute (#3 <- 5).
Check (whiles 3 <=s 5 loops skips dones).
Check (ifs #3 <=s 5 thens skips ;;; #5 <- 5 elses skips ;;; skips ;;; skips dones).
Check (ifs (5 <=s 3) &s Falses thens skips elses skips dones).

Inductive stack_mutated_at_index: stack -> stack_index -> nat -> stack -> Prop :=
| stk_mut_first :
  forall (stk stk': stack) (n0 new: nat),
    stk = stk' ->
    stack_mutated_at_index (new :: stk) 1 new (n0 :: stk')
| stk_mut_rest :
  forall (stk stk': stack) (n n' new: nat) (k: stack_index),
    k > 1 ->
    k <= S (List.length stk) ->
    List.length stk = List.length stk' ->
    stack_mutated_at_index stk (k - 1) new stk' ->
    n = n' ->
    stack_mutated_at_index (n :: stk) k new (n' :: stk').


Record fun_stk :=
  { Name: ident
  ; Args : nat
  ; Body : imp_stack
  ; Return_expr : aexp_stack
  ; Return_pop : nat }.

Definition fun_env_stk := store fun_stk.

Definition init_fenv_stk : fun_env_stk :=
  fun _ => 
  {|
    Name := "id";
    Args := 1;
    Body := Seq_Stk Push_Stk (Assign_Stk 1 #(2));
    Return_expr := Var_Stk 1;
    Return_pop := 1
  |}. 
        (* ({| Name := "id"
        ; Args := 1
        ; Body := Skip_Stk
        ; Return_expr := (Var_Stk 1)
        ; Return_pop := 0 |}). *)

Compute (init_fenv_stk "").

Inductive prog_stack :=
| Prog_Stk (l: list fun_stk) (i: imp_stack).

Inductive same_after_popping : stack -> stack -> nat -> Prop :=
| Same_nil :
  forall stk1 stk2,
    stk1 = stk2 ->
    same_after_popping stk1 stk2 0
| Same_cons :
  forall stk1 stk2 val n,
    same_after_popping stk1 stk2 n ->
    same_after_popping stk1 (val :: stk2) (S n).

Lemma same_after_popping_implies_geq_popped_length :
  forall stk1 stk2 n,
    same_after_popping stk1 stk2 n ->
    n <= Datatypes.length stk2.
Proof.
  intros stk1 stk2 n. revert stk1 stk2.
  induction n; intros.
  - induction stk2; simpl; auto.
    lia.
  - destruct stk2.
    + inversion H.
    + simpl.
      inversion H.
      apply IHn in H2. lia.
Qed.


Inductive aexp_stack_sem : aexp_stack -> fun_env_stk -> stack -> stack * nat -> Prop :=
| Stack_const :
  forall fenv stk n,
    aexp_stack_sem (Const_Stk n) fenv stk (stk, n)
| Stack_var :
  forall i fenv stk n,
    1 <= i ->
    i <= (List.length stk) ->
    List.nth_error stk (i - 1) = Some n ->
    aexp_stack_sem (Var_Stk i) fenv stk (stk, n)
| Stack_plus :
  forall fenv stk a1 a2 stk1 stk2 n1 n2,
    aexp_stack_sem a1 fenv stk (stk1, n1) ->
    aexp_stack_sem a2 fenv stk1 (stk2, n2) ->
    aexp_stack_sem (Plus_Stk a1 a2) fenv stk (stk2, n1 + n2)
| Stack_minus :
  forall fenv stk a1 a2 stk1 stk2 n1 n2,
    aexp_stack_sem a1 fenv stk (stk1, n1) ->
    aexp_stack_sem a2 fenv stk1 (stk2, n2) ->
    aexp_stack_sem (Minus_Stk a1 a2) fenv stk (stk2, n1 - n2)
| Stack_app :
  forall fenv stk stk1 stk2 stk3 stk4 func num_args args vals ret_expr ret_pop fname n,
    (fenv fname = func) ->
    (Args func) = num_args ->
    (Return_expr func) = ret_expr ->
    (Return_pop func) = ret_pop ->
    num_args = List.length args ->
    args_stack_sem args fenv stk (stk1, vals) ->
    imp_stack_sem (Body func) fenv (List.app vals stk1) stk2 ->
    aexp_stack_sem ret_expr fenv stk2 (stk3, n) ->
    same_after_popping stk4 stk3 (num_args + ret_pop) ->
    aexp_stack_sem (App_Stk fname args) fenv stk (stk4, n)
with args_stack_sem : list aexp_stack -> fun_env_stk -> stack -> stack * (list nat) -> Prop :=
| args_stack_nil :
  forall fenv stk,
    args_stack_sem nil fenv stk (stk, nil)
| args_stack_cons :
  forall aexp aexps fenv stk val vals stk' stk'',
    aexp_stack_sem aexp fenv stk (stk', val) ->
    args_stack_sem aexps fenv stk' (stk'', vals) ->
    args_stack_sem (aexp :: aexps) fenv stk (stk'', val :: vals)
with bexp_stack_sem : bexp_stack -> fun_env_stk -> stack -> stack * bool -> Prop :=
| Stack_true :
  forall fenv stk,
    bexp_stack_sem True_Stk fenv stk (stk, true)
| Stack_false :
  forall fenv stk,
    bexp_stack_sem False_Stk fenv stk (stk, false)
| Stack_neg :
  forall fenv stk stk' bexp b b',
    bexp_stack_sem bexp fenv stk (stk', b') ->
    b = negb b' ->
    bexp_stack_sem (Neg_Stk bexp) fenv stk (stk', b)
| Stack_and :
  forall fenv stk stk' stk'' bexp1 bexp2 b1 b2 b,
    bexp_stack_sem bexp1 fenv stk (stk', b1) ->
    bexp_stack_sem bexp2 fenv stk' (stk'', b2) ->
    b = andb b1 b2 ->
    bexp_stack_sem (And_Stk bexp1 bexp2) fenv stk (stk'', b)
| Stack_or :
  forall fenv stk stk' stk'' bexp1 bexp2 b1 b2 b,
    bexp_stack_sem bexp1 fenv stk (stk', b1) ->
    bexp_stack_sem bexp2 fenv stk' (stk'', b2) ->
    b = orb b1 b2 ->
    bexp_stack_sem (Or_Stk bexp1 bexp2) fenv stk (stk'', b)
| Stack_leq :
  forall fenv stk stk' stk'' a1 a2 n1 n2 b,
    aexp_stack_sem a1 fenv stk (stk', n1) ->
    aexp_stack_sem a2 fenv stk' (stk'', n2) ->
    b = Nat.leb n1 n2 ->
    bexp_stack_sem (Leq_Stk a1 a2) fenv stk (stk'', b)
| Stack_eq :
  forall fenv stk stk' stk'' a1 a2 n1 n2 b,
    aexp_stack_sem a1 fenv stk (stk', n1) ->
    aexp_stack_sem a2 fenv stk' (stk'', n2) ->
    b = Nat.eqb n1 n2 ->
    bexp_stack_sem (Eq_Stk a1 a2) fenv stk (stk'', b)
with imp_stack_sem : imp_stack -> fun_env_stk -> stack -> stack -> Prop :=
| Stack_skip :
  forall fenv stk,
    imp_stack_sem Skip_Stk fenv stk stk
| Stack_assign :
  forall fenv stk stk' stk'' k aexp c,
    1 <= k ->
    k <= (List.length stk) ->
    aexp_stack_sem aexp fenv stk (stk', c) ->
    stack_mutated_at_index stk'' k c stk' ->
    imp_stack_sem (Assign_Stk k aexp) fenv stk stk''
| Stack_push :
  forall fenv stk stk',
    stk' = 0 :: stk ->
    imp_stack_sem Push_Stk fenv stk stk'
| Stack_pop :
  forall fenv stk stk' v,
    stk = v :: stk' ->
    imp_stack_sem Pop_Stk fenv stk stk'
| Stack_seq :
  forall fenv stk stk' stk'' i1 i2,
    imp_stack_sem i1 fenv stk stk' ->
    imp_stack_sem i2 fenv stk' stk'' ->
    imp_stack_sem (Seq_Stk i1 i2) fenv stk stk''
| Stack_if_true :
  forall fenv stk stk' stk'' b i1 i2,
    bexp_stack_sem b fenv stk (stk', true) ->
    imp_stack_sem i1 fenv stk' stk'' ->
    imp_stack_sem (If_Stk b i1 i2) fenv stk stk''
| Stack_if_false :
  forall fenv stk stk' stk'' b i1 i2,
    bexp_stack_sem b fenv stk (stk', false) ->
    imp_stack_sem i2 fenv stk' stk'' ->
    imp_stack_sem (If_Stk b i1 i2) fenv stk stk''
| Stack_while_done :
  forall fenv stk stk' b i,
    bexp_stack_sem b fenv stk (stk', false) ->
    imp_stack_sem (While_Stk b i) fenv stk stk'
| Stack_while_step :
  forall fenv stk stk1 stk2 stk3 b i,
    bexp_stack_sem b fenv stk (stk1, true) ->
    imp_stack_sem i fenv stk1 stk2 ->
    imp_stack_sem (While_Stk b i) fenv stk2 stk3 ->
    imp_stack_sem (While_Stk b i) fenv stk stk3
.

Check imp_stack_sem_ind.

Scheme imp_stack_sem_mut := Induction for imp_stack_sem Sort Prop
    with aexp_stack_sem_mut := Induction for aexp_stack_sem Sort Prop
                              with bexp_stack_sem_mut := Induction for bexp_stack_sem Sort Prop
                              with args_stack_sem_mut := Induction for args_stack_sem Sort Prop.

Combined Scheme imp_stack_mutind from imp_stack_sem_mut, aexp_stack_sem_mut, bexp_stack_sem_mut, args_stack_sem_mut.
Check imp_stack_mutind.

Lemma same_after_popping_means_same :
  forall a b c n,
    same_after_popping a c n ->
    same_after_popping b c n ->
    a = b.
Proof.
  intros. revert H0. revert b. induction H; intros.
  - subst. inversion H0. subst. reflexivity.
  - inversion H0. subst. apply IHsame_after_popping. apply H3. 
Qed.

Lemma stack_mutated_at_index_deterministic :
  forall stk k n stk' stk'',
    stack_mutated_at_index stk' k n stk ->
    stack_mutated_at_index stk'' k n stk ->
    stk' = stk''.
Proof.
  intros. revert H0. revert stk''. induction H; intros; subst.
  - inversion H0; subst; auto. inversion H2. inversion H1. 
  - inversion H4; subst.
    + inversion H. inversion H5.
    + f_equal. apply IHstack_mutated_at_index. apply H12.
Qed.

Ltac invc H := inversion H; subst; clear H.

Theorem big_step_deterministic :
  (forall i fenv stk stk',
      imp_stack_sem i fenv stk stk' ->
      forall stk'',
        imp_stack_sem i fenv stk stk'' ->
        stk' = stk'') /\
    (forall a fenv stk stk'n,
        aexp_stack_sem a fenv stk (stk'n) ->
        forall stk'' n',
          aexp_stack_sem a fenv stk (stk'', n') ->
          stk'n = (stk'', n')) /\
    (forall b fenv stk stk'v,
        bexp_stack_sem b fenv stk (stk'v) ->
        forall stk'' v',
          bexp_stack_sem b fenv stk (stk'', v') ->
          stk'v = (stk'', v')) /\
    (forall args fenv stk stk'vals,
        args_stack_sem args fenv stk (stk'vals) ->
        forall stk'' vals',
          args_stack_sem args fenv stk (stk'', vals') ->
          stk'vals = (stk'', vals')).
Proof.
  pose (fun i f s s0 => fun H: imp_stack_sem i f s s0 => forall s1, imp_stack_sem i f s s1 -> s0 = s1) as P.
  pose (fun a f s p => fun Ha: aexp_stack_sem a f s p => forall s1 n1, aexp_stack_sem a f s (s1, n1) -> p = (s1, n1)) as P0.
  pose (fun b f s p =>
        fun Hb: bexp_stack_sem b f s p =>
          forall s1 v1,
            bexp_stack_sem b f s (s1, v1) ->
            p = (s1, v1)) as P1.
  pose (fun l f s p =>
        fun Harg : args_stack_sem l f s p =>
          forall s1 vals1,
            args_stack_sem l f s (s1, vals1) ->
            p = (s1, vals1)) as P2.
  
  apply (imp_stack_mutind P P0 P1 P2); unfold P, P0, P1, P2 in *; intros.
  - invc H. reflexivity.
  - inversion H0; subst.
    apply H in H5.
    inversion H5; subst.
    eapply stack_mutated_at_index_deterministic in H9.
    eassumption.
    assumption.
  - inversion H.
    subst. reflexivity.
  - invc H. invc H0. reflexivity.
  - inversion H1. apply H in H4. subst. apply H0 in H8. assumption.
  - inversion H1. subst. apply H in H8. invc H8. apply H0 in H9. assumption.
    apply H in H8. inversion H8.
  - invc H1; apply H in H8; invc H8.
    apply H0 in H9. assumption.
  - inversion H0.
    + apply H in H6. subst. inversion H6. reflexivity.
    + apply H in H3. subst. inversion H3.
  - inversion H2.
    + apply H in H8. inversion H8.
    + apply H in H5. invc H5. apply H0 in H6. subst. apply H1 in H10. assumption.
  - inversion H. reflexivity.
  - inversion H. subst. rewrite H7 in e. inversion e. reflexivity.
  - invc H1. apply H in H7. invc H7. apply H0 in H9. invc H9. reflexivity.
  - invc H1. apply H in H7. invc H7. apply H0 in H9. invc H9. reflexivity.
  - invc H2. apply H in H12. invc H12. apply H0 in H15. subst. apply H1 in H16. invc H16. pose proof (same_after_popping_means_same) as Same.
    apply (Same stk4 s1 stk7 (Args (fenv fname) + Return_pop (fenv fname))) in s.
    subst. reflexivity.
    assumption.
  - invc H. reflexivity.
  - invc H. reflexivity.
  - invc H0. apply H in H6. invc H6. reflexivity.
  - invc H1. apply H in H8. invc H8. apply H0 in H9. invc H9. reflexivity.
  - invc H1. apply H in H8. invc H8. apply H0 in H9. invc H9. reflexivity.
  - invc H1. apply H in H8. invc H8. apply H0 in H9. invc H9. reflexivity.
  - invc H1. apply H in H8. invc H8. apply H0 in H9. invc H9. reflexivity.
  - invc H. reflexivity.
  - invc H1. apply H in H7. invc H7. apply H0 in H9. invc H9. reflexivity.
Qed.

Corollary stack_sem_deterministic_human :
  forall fenv stk,
    (forall i stk' stk'',
        imp_stack_sem i fenv stk stk' ->
        imp_stack_sem i fenv stk stk'' ->
        stk' = stk'')
    /\
      (forall a stk'n stk''n,
          aexp_stack_sem a fenv stk stk'n ->
          aexp_stack_sem a fenv stk stk''n ->
          stk'n = stk''n)
    /\
      (forall b stk'v stk''v,
          bexp_stack_sem b fenv stk stk'v ->
          bexp_stack_sem b fenv stk stk''v ->
          stk'v = stk''v)
    /\
      (forall args stk'vals stk''vals,
          args_stack_sem args fenv stk stk'vals ->
          args_stack_sem args fenv stk stk''vals ->
          stk'vals = stk''vals).
Proof.
  intros fenv stk.
  split; [ | split; [ | split ]]; intros; pose proof big_step_deterministic as DET; destruct DET as (IMP & AEXP & BEXP & ARGS).
  - eapply IMP; eassumption.
  - inversion H; subst; inversion H0; subst; eapply AEXP; eassumption.
  - destruct stk'v as [stk' v'] eqn:STK' in H.
    destruct stk''v as [stk'' v''] eqn:STK'' in H0.
    subst. eapply BEXP; eassumption.
  - destruct stk'vals as [stk' vals'] eqn:STK' in H.
    destruct stk''vals as [stk'' vals''] eqn:STK'' in H0.
    subst.
    eapply ARGS; eassumption.
Qed.

Ltac destruct_det DET := destruct DET as (IMP & AEXP & BEXP & ARGS).

Corollary imp_stack_sem_det :
  forall fenv stk i stk' stk'',
    imp_stack_sem i fenv stk stk' ->
    imp_stack_sem i fenv stk stk'' ->
    stk' = stk''.
Proof.
  intros. pose proof (stack_sem_deterministic_human fenv stk) as DET.
  destruct_det DET. eapply IMP; eassumption.
Qed.

Corollary aexp_stack_sem_det :
  forall fenv stk a stk'n stk''n,
    aexp_stack_sem a fenv stk stk'n ->
    aexp_stack_sem a fenv stk stk''n ->
    stk'n = stk''n.
Proof.
  intros. pose proof (stack_sem_deterministic_human fenv stk) as DET.
  destruct_det DET. eapply AEXP; eassumption.
Qed.

Corollary bexp_stack_sem_det :
  forall fenv stk b stk'v stk''v,
    bexp_stack_sem b fenv stk stk'v ->
    bexp_stack_sem b fenv stk stk''v ->
    stk'v = stk''v.
Proof.
  intros. pose proof (stack_sem_deterministic_human fenv stk) as DET.
  destruct_det DET. eapply BEXP; eassumption.
Qed.

Corollary args_stack_sem_det :
  forall fenv stk args stk'vals stk''vals,
      args_stack_sem args fenv stk stk'vals ->
      args_stack_sem args fenv stk stk''vals ->
      stk'vals = stk''vals.
Proof.
  intros. pose proof (stack_sem_deterministic_human fenv stk) as DET.
  destruct_det DET. eapply ARGS; eassumption.
Qed.
