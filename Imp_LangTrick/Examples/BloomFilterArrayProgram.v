From Coq Require Import String List Psatz.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage rsa_impLang EnvToStack.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition bloom_fun_body :=
  Seq_Stk Push_Stk (Seq_Stk (Assign_Stk 1 (Var_Stk 2)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 0)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 1)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 2)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 3)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 4)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 5)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 6)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 7)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 8)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 9)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 10)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 11)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 12)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 13)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 14)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 15)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 16)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 17)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 18)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 19)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 20)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 21)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 22)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 23)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 24)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 25)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 26)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 27)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 28)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 29)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 30)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 31)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 32)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 33)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 34)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 35)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 36)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 37)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 38)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 39)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 40)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 41)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 42)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 43)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 44)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 45)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 46)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 47)) (Assign_Stk 1 (Const_Stk 1)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 48)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 49)) (Assign_Stk 1 (Const_Stk 0)) (If_Stk (Eq_Stk (Var_Stk 1) (Const_Stk 50)) (Assign_Stk 1 (Const_Stk 0)) (Skip_Stk))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition imp_is_prime_body :=
  
  (IF_Imp_Lang (lt_Imp_Lang (PARAM_Imp_Lang 0) (CONST_Imp_Lang 2))
               (ASSIGN_Imp_Lang "isPrime" (CONST_Imp_Lang 0))
               (IF_Imp_Lang (eq_Imp_Lang (PARAM_Imp_Lang 0) (CONST_Imp_Lang 2))
                            (ASSIGN_Imp_Lang "isPrime" (CONST_Imp_Lang 1))
                            (SEQ_Imp_Lang
                               (ASSIGN_Imp_Lang "isPrime" (CONST_Imp_Lang 0))
                               (SEQ_Imp_Lang
                                  (ASSIGN_Imp_Lang "i" (CONST_Imp_Lang 2))
                                  (WHILE_Imp_Lang (lt_Imp_Lang (VAR_Imp_Lang "i") (PARAM_Imp_Lang 0))
                                                  (SEQ_Imp_Lang
                                                     (ASSIGN_Imp_Lang "res" (APP_Imp_Lang "euc_div" ((PARAM_Imp_Lang 0) :: (VAR_Imp_Lang "i") :: nil)))
                                                     (IF_Imp_Lang (eq_Imp_Lang (VAR_Imp_Lang "res") (CONST_Imp_Lang 0))
                                                                  (SEQ_Imp_Lang
                                                                     (ASSIGN_Imp_Lang "isPrime" (CONST_Imp_Lang 1))
                                                                     (ASSIGN_Imp_Lang "i" (PARAM_Imp_Lang 0)))
                                                                  (ASSIGN_Imp_Lang "i" (PLUS_Imp_Lang (VAR_Imp_Lang "i") (CONST_Imp_Lang 1)))))))))).

Definition construct_eq_imp (n1 n2: nat) :=
  andb (Nat.leb n1 n2) (Nat.leb n2 n1).

Definition construct_neq_imp (n1 n2: nat) :=
  negb (construct_eq_imp n1 n2).

Definition construct_lt_imp (n1 n2: nat) :=
  andb (Nat.leb n1 n2) (construct_neq_imp n1 n2).

Definition imp_is_prime_fun : fun_Imp_Lang :=
  {| Imp_LangTrickLanguage.Name := "is_prime"
  ; Imp_LangTrickLanguage.Args := 1
  ; Ret := "isPrime"
  ; Imp_LangTrickLanguage.Body := imp_is_prime_body |}.

Definition imp_euc_div_fun : fun_Imp_Lang :=
  {| Imp_LangTrickLanguage.Name := "euc_div"
  ; Imp_LangTrickLanguage.Args := 2
  ; Ret := "x"
  ; Imp_LangTrickLanguage.Body := euc_div_body |}.

Definition is_prime_fenv := update "euc_div" imp_euc_div_fun (update "is_prime" imp_is_prime_fun init_fenv).

(* Example mod_3_2 : *)
(*   a_Imp_Lang (APP_Imp_Lang "euc_div" ((CONST_Imp_Lang 3) :: (CONST_Imp_Lang 2) :: nil)) nil is_prime_fenv init_nenv 1. *)
(* Proof. *)
(*   econstructor. *)
(*   - reflexivity. *)
(*   - reflexivity. *)
(*   - repeat econstructor. *)
(*   - simpl. unfold euc_div_body. unfold euc_div_loop. econstructor. *)
(*     + repeat econstructor. *)
(*     + eapply Imp_Lang_while_step. *)
(*       * replace true with (Nat.leb 2 3) at 9; [ | reflexivity ]. *)
(*         repeat econstructor. *)
(*       * repeat econstructor. *)
(*       * simpl. eapply Imp_Lang_while_step. *)
(*         -- replace true with (Nat.leb 1 1) at 13; [ | reflexivity ]. *)
(*            repeat  *)

Example is_prime_3 :
  a_Imp_Lang (APP_Imp_Lang "is_prime" ((CONST_Imp_Lang 3) :: nil)) nil is_prime_fenv init_nenv 0.
Proof.
  econstructor.
  - reflexivity.
  - simpl. reflexivity.
  - repeat econstructor.
  - simpl. unfold imp_is_prime_body.
    eapply Imp_Lang_if_false.
    + assert (false = (andb (Nat.leb 3 2) (negb (andb (Nat.leb 3 2) (Nat.leb 2 3))))) by (reflexivity).
      rewrite H. econstructor.
      * econstructor; econstructor.
        -- simpl. lia.
        -- reflexivity.
      * econstructor; econstructor; econstructor; econstructor; simpl; try lia; try reflexivity.
    + eapply Imp_Lang_if_false.
      * assert (false = (andb (Nat.leb 3 2) (Nat.leb 2 3))) by reflexivity.
        rewrite H.
        repeat econstructor.
      * econstructor.
        -- repeat econstructor.
        -- econstructor.
           ++ repeat econstructor.
           ++ eapply Imp_Lang_while_step.
              ** assert (true = construct_lt_imp 2 3) by reflexivity.
                 rewrite H at 37. unfold construct_lt_imp. econstructor.
                 --- repeat econstructor.
                 --- unfold construct_neq_imp. econstructor.
                     unfold construct_eq_imp. repeat econstructor.
              ** econstructor.
                 --- econstructor. econstructor.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ repeat econstructor.
                     +++ simpl. unfold euc_div_body. unfold euc_div_loop.
                         unfold update. simpl.
                         econstructor.
                         *** repeat econstructor.
                         *** eapply Imp_Lang_while_step.
                             ---- assert (true = Nat.leb 2 3) by reflexivity. rewrite H at 9. repeat econstructor.
                             ---- repeat econstructor.
                             ---- simpl. eapply Imp_Lang_while_done.
                                  replace false with (Nat.leb 2 1) at 13; [ | reflexivity ].
                                  repeat econstructor.
                     +++ reflexivity.
                 --- simpl. remember (update "x" 1 (update "x" 3 init_nenv) "x") as UP.
                     unfold update in HeqUP. simpl in HeqUP. subst UP.
                     eapply Imp_Lang_if_false.
                     +++ replace false with (construct_eq_imp 1 0) at 55 by reflexivity. repeat econstructor.
                     +++ repeat econstructor.
              ** simpl. eapply Imp_Lang_while_done.
                 replace false with (construct_lt_imp 3 3) at 52 by reflexivity. repeat econstructor.
  - reflexivity.
Qed.


Definition stack_euc_div := compile_function imp_euc_div_fun.

Eval compute in stack_euc_div.

Definition stack_hash1 :=
  Seq_Stk
    Push_Stk
    (Assign_Stk 1 (App_Stk "euc_div" ((Var_Stk 2) :: (Const_Stk 51) :: nil))).

Definition stack_hash2 :=
  Seq_Stk
    Push_Stk
    (Seq_Stk
       (Assign_Stk 1 (App_Stk "euc_div" ((Var_Stk 2) :: (Const_Stk 89) :: nil)))
       (Assign_Stk 1 (App_Stk "hash1" ((Var_Stk 1) :: nil)))).


Definition stack_hash3 :=
  Seq_Stk
    Push_Stk
    (Seq_Stk
       (Assign_Stk 1 (App_Stk "euc_div" ((Var_Stk 2) :: (Const_Stk 97) :: nil)))
       (Assign_Stk 1 (App_Stk "hash1" ((Var_Stk 1) :: nil)))).

Definition hash1_fun : fun_stk :=
  {| Name := "hash1"
  ; Args := 1
  ; Body := stack_hash1
  ; Return_expr := Var_Stk 1
  ; Return_pop := 1 |}.

Definition hash2_fun : fun_stk :=
  {| Name := "hash2"
  ; Args := 1
  ; Body := stack_hash2
  ; Return_expr := Var_Stk 1
  ; Return_pop := 1 |}.

Definition hash3_fun : fun_stk :=
  {| Name := "hash3"
  ; Args := 1
  ; Body := stack_hash3
  ; Return_expr := Var_Stk 1
  ; Return_pop := 1 |}.

Definition bloom_array : fun_stk :=
  {| Name := "bloom_array"
  ; Args := 1
  ; Body := bloom_fun_body
  ; Return_expr := Var_Stk 1
  ; Return_pop := 1 |}.

Definition apply_unary_fun (funName : ident) (n: nat): aexp_stack :=
  App_Stk funName ((Var_Stk n) :: nil).

Fixpoint seq_stk_ify (cmds: list imp_stack) : imp_stack :=
  match cmds with
  | nil => Skip_Stk
  | cmd :: cmds' =>
      match (seq_stk_ify cmds') with
      | Skip_Stk =>
          cmd
      | c => Seq_Stk cmd c
      end
  end.




Definition stack_is_prime_body :=
  let eq1 := (fun n => Eq_Stk (Var_Stk n) (Const_Stk 1)) in
  let assign0 := (fun n => Assign_Stk n (Const_Stk 0)) in
  seq_stk_ify
    (Push_Stk
       :: Push_Stk
       :: Push_Stk
       :: Push_Stk
       :: Push_Stk
       :: Push_Stk
       :: Push_Stk
       :: (Assign_Stk 1 (apply_unary_fun "hash1" 8))
       :: (Assign_Stk 2 (apply_unary_fun "hash2" 8))
       :: (Assign_Stk 3 (apply_unary_fun "hash3" 8))
       :: (Assign_Stk 4 (apply_unary_fun "bloom_array" 1))
       :: (If_Stk
            (eq1 4)
            (seq_stk_ify
               ((Assign_Stk 5 (apply_unary_fun "bloom_array" 2))
                  :: (If_Stk
                       (eq1 5)
                       (seq_stk_ify
                          ((Assign_Stk 6 (apply_unary_fun "bloom_array" 3))
                             :: (If_Stk
                                  (eq1 6)
                                  (Assign_Stk 7 (Const_Stk 1))
                                  (Assign_Stk 7 (Const_Stk 0)))
                             :: nil))
                       (assign0 7))
                  :: nil))
            (assign0 7))
       :: nil).
Eval compute in stack_is_prime_body.

Definition stack_is_prime_fun :=
  {| Name := "isPrime"
  ; Args := 1
  ; Body := stack_is_prime_body
  ; Return_expr := (Var_Stk 7)
  ; Return_pop := 7 |}.

Fixpoint stk_fenv_ify (funs : list fun_stk) : fun_env_stk :=
  match funs with
  | nil => init_fenv_stk
  | f :: funs' =>
      update (Name f) f (stk_fenv_ify funs')
  end.

Definition stack_funs := hash1_fun :: hash2_fun :: bloom_array :: stack_is_prime_fun :: stack_euc_div :: nil.

Definition is_prime_fenv_stk := stk_fenv_ify stack_funs.
From Imp_LangTrick Require Import ProofCompAutoAnother.
(* Example stk_is_prime_3 : *)
(*   aexp_stack_sem (App_Stk "isPrime" ((Const_Stk 3) :: nil)) is_prime_fenv_stk nil (nil, 1). *)
(* Proof. *)
(*   econstructor; auto. *)
(*   - repeat econstructor. *)
(*   - simpl. unfold stack_is_prime_body. simpl. *)
(*     repeat match goal with *)
(*            | [ |- imp_stack_sem (Seq_Stk Push_Stk _) _ _ _ ] => *)
(*                econstructor *)
(*            | [ |- _ ] => *)
(*                fail *)
(*            end. *)
(*     all: try econstructor; eauto. *)
(*     + repeat econstructor. *)
(*     + econstructor. *)
(*       * econstructor. *)
(*         -- lia. *)
(*         -- simpl. lia. *)
(*         --  *)
(*         unfold apply_unary_fun. *)
(*         econstructor; eauto. *)
(*         ++  *)
(*           repeat econstructor. *)
(*         ++  *)
(*         simpl. unfold stack_hash2. *)
(*         econstructor. *)
(*         ** econstructor. reflexivity. *)
(*         **  *)
(*           econstructor. *)
(*           ---  *)
(*             econstructor; try (simpl; lia). *)
(*             +++ econstructor; eauto. *)
(*                 *** repeat econstructor. *)
(*                 *** simpl. unfold stack_mapping. simpl. *)
(*                     repeat econstructor. *)
(*                 *** simpl. unfold stack_mapping. simpl. repeat econstructor. *)
(*                 *** simpl. repeat econstructor. *)
(*             +++ repeat econstructor. *)
(*           --- repeat econstructor. *)
(*         ++ simpl. repeat econstructor. *)
(*         ++ simpl. repeat econstructor. *)
(*         -- smash_stack_mutated_at_index. *)
(*       * simpl. meta_smash. *)
(*         smash_stack_mutated_at_index. *)
(*         simpl. lia. *)
(*         simpl. reflexivity. *)
(*         repeat econstructor. *)
(*         smash_stack_mutated_at_index. *)
(*         simpl. lia. simpl. lia. *)
(*         simpl. reflexivity. *)
(*         unfold bloom_fun_body. simpl. *)
(*         meta_smash. smash_stack_mutated_at_index. *)
        
        
