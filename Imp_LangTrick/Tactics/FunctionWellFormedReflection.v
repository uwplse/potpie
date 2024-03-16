From Coq Require Import List Program.Equality.

From Imp_LangTrick Require Import Imp_LangTrickLanguage FunctionWellFormed StackLangTheorems ImpHasVariableReflection.

Local Open Scope list_scope.

Program Fixpoint construct_in {A: Type} (Aeq_dec: forall (x y: A), {x = y} + {x <> y}) (elt: A) (lst: list A): option (In elt lst) :=
  match lst with
  | nil => None
  | head :: rest =>
      if (Aeq_dec elt head) then
        _
      else
        match (construct_in Aeq_dec elt rest) with
        | Some P => _
        | None => None
        end
  end.
Next Obligation.
  assert (head = head \/ In head rest) by (left; reflexivity).
  eapply (Some H).
Defined.
Next Obligation.
  assert (head = elt \/ In elt rest) by (right; eassumption).
  eapply (Some H).
Defined.

From Coq Require Import String.

Local Open Scope string_scope.


Fixpoint aexp_Imp_Lang_eqb (a1 a2: aexp_Imp_Lang) : bool :=
  match a1, a2 with
  | CONST_Imp_Lang n, CONST_Imp_Lang n' =>
      Nat.eqb n n'
  | VAR_Imp_Lang x, VAR_Imp_Lang x' =>
      String.eqb x x'
  | PARAM_Imp_Lang k, PARAM_Imp_Lang k' =>
      Nat.eqb k k'
  | PLUS_Imp_Lang a1' a1'', PLUS_Imp_Lang a2' a2'' =>
      andb (aexp_Imp_Lang_eqb a1' a2') (aexp_Imp_Lang_eqb a1'' a2'')
  | MINUS_Imp_Lang a1' a1'', MINUS_Imp_Lang a2' a2'' =>
      andb (aexp_Imp_Lang_eqb a1' a2') (aexp_Imp_Lang_eqb a1'' a2'')
  | APP_Imp_Lang f args, APP_Imp_Lang f' args' =>
      andb (String.eqb f f')
           ((fix args_Imp_Lang_eqb (args1 args2: list aexp_Imp_Lang) : bool :=
               match args1, args2 with
               | nil, nil => true
               | hd1 :: tl1, hd2 :: tl2 =>
                   andb (aexp_Imp_Lang_eqb hd1 hd2) (args_Imp_Lang_eqb tl1 tl2)
               | _, _ => false
               end)
              args args')
  | _, _ => false
  end.

Fixpoint bexp_Imp_Lang_eqb (b1 b2: bexp_Imp_Lang) : bool :=
  match b1, b2 with
  | TRUE_Imp_Lang, TRUE_Imp_Lang => true
  | FALSE_Imp_Lang, FALSE_Imp_Lang => true
  | NEG_Imp_Lang b, NEG_Imp_Lang b' =>
      bexp_Imp_Lang_eqb b b'
  | AND_Imp_Lang b3 b4, AND_Imp_Lang b5 b6 =>
      andb (bexp_Imp_Lang_eqb b3 b5)
           (bexp_Imp_Lang_eqb b4 b6)
  | OR_Imp_Lang b3 b4, OR_Imp_Lang b5 b6 =>
      andb (bexp_Imp_Lang_eqb b3 b5)
           (bexp_Imp_Lang_eqb b4 b6)
  | LEQ_Imp_Lang a1 a2, LEQ_Imp_Lang a1' a2' =>
      andb (aexp_Imp_Lang_eqb a1 a1')
           (aexp_Imp_Lang_eqb a2 a2')
  | _, _ => false
  end.

Fixpoint imp_Imp_Lang_eqb (i1 i2: imp_Imp_Lang) : bool :=
  match i1, i2 with
  | SKIP_Imp_Lang, SKIP_Imp_Lang => true
  | ASSIGN_Imp_Lang x a, ASSIGN_Imp_Lang x' a' =>
      andb (String.eqb x x')
           (aexp_Imp_Lang_eqb a a')
  | SEQ_Imp_Lang i3 i4, SEQ_Imp_Lang i5 i6 =>
      andb (imp_Imp_Lang_eqb i3 i5)
           (imp_Imp_Lang_eqb i4 i6)
  | IF_Imp_Lang b1 i3 i4, IF_Imp_Lang b2 i5 i6 =>
      andb (bexp_Imp_Lang_eqb b1 b2)
           (andb (imp_Imp_Lang_eqb i3 i5)
                 (imp_Imp_Lang_eqb i4 i6))
  | WHILE_Imp_Lang b1 i3, WHILE_Imp_Lang b2 i4 =>
      andb (bexp_Imp_Lang_eqb b1 b2)
           (imp_Imp_Lang_eqb i3 i4)
  | _, _ => false
  end.

Lemma not_equal :
  1 <> 2.
Proof.
  congruence.
Defined.
Print not_equal.

(* not_equal = 
(fun H : 1 = 2 =>
 let Heq : 0 = 2 :=
   eq_trans
     (f_equal (fun t : nat => match t with
                              | 0 => 0
                              | S x => x
                              end) H) H in
 let H0 : False :=
   eq_ind 0 (fun e : nat => match e with
                            | 0 => True
                            | S _ => False
                            end) I 2 Heq in
 False_ind False H0)
:
1 <> 2
     : 1 <> 2 *)
Print eq_ind.

Lemma nil_not_cons :
  forall A (h: A) l,
    nil <> h :: l.
Proof.
  intros. congruence.
Defined.

Print nil_not_cons.

Check (fun H: 1 = 2 =>
         f_equal (fun t: nat => match t with
                         | 0 => 0
                         | S x => x
                         end) H).

Program Fixpoint aexp_Imp_Lang_dec (a1 a2: aexp_Imp_Lang) : { a1 = a2 } + {a1 <> a2} :=
  match a1, a2 with
  | _, _ => _
  end.
Next Obligation.
  revert a1 a2.
  eapply (aexp_Imp_Lang_rec2 (fun a1 =>
                                forall a2,
                                  {a1 = a2} + {a1 <> a2})); intros;
    match goal with
    | [ |- { CONST_Imp_Lang _ = _ } + { _ <> _ } ] =>
        destruct a2; try (intros; right; congruence)
    | [ |- { PARAM_Imp_Lang _ = _ } + { _ <> _ } ] =>
        destruct a2; try (intros; right; congruence)
    | [ |- { VAR_Imp_Lang _ = _ } + { _ <> _ } ] =>
        destruct a2; try (intros; right; congruence)
    | [ |- _ ] =>
        idtac
    end.
  - pose proof (PeanoNat.Nat.eq_dec n n0).
    destruct H; [ left | right ]; congruence.
  - pose proof (string_dec x x0).
    destruct H; [ left | right ]; congruence.
  - pose proof (PeanoNat.Nat.eq_dec n n0).
    destruct H; [ left | right ]; congruence.
  - destruct a0; try (right; congruence).
    specialize (H a0_1). specialize (H0 a0_2).
    destruct H, H0; [ left | right .. ]; congruence.
  - destruct a0; try (right; congruence).
    specialize (H a0_1). specialize (H0 a0_2).
    destruct H, H0; [ left | right .. ]; congruence.
  - destruct a2; try (right; congruence).
    revert aexps0. induction H; intros.
    + pose proof (string_dec f f0).
      destruct H; [ | right; congruence].
      pose proof (match aexps0 as aexps' return {nil = aexps'} + {nil <> aexps'} with
                  | nil => @left (nil = nil) (nil <> nil) eq_refl
                  | h :: tl => @right (nil = h :: tl) (nil <> h :: tl) (nil_not_cons (aexp_Imp_Lang) h tl)
                  end).
      destruct H; [ left | right ]; congruence.
    + pose proof (string_dec f f0).
      destruct H0; [ | right; congruence ].
      (* pose proof (match aexps0 as aexps' return {nil = aexps'} + {nil <> aexps'} with *)
      (*             | nil => @left (nil = nil) (nil <> nil) eq_refl *)
      (*             | h :: tl => @right (nil = h :: tl) (nil <> h :: tl) (nil_not_cons (aexp_Imp_Lang) h tl) *)
      (*             end). *)
      destruct aexps0.
      * pose proof (nil_not_cons _ x l).
        eapply not_eq_sym in H0.
        right; congruence.
      * specialize (IHSForall aexps0).
        specialize (p a).
        destruct p, IHSForall; [ left | right .. ]; try congruence.
Defined.

Program Fixpoint bexp_Imp_Lang_dec (b1 b2: bexp_Imp_Lang) : { b1 = b2 } + {b1 <> b2 } :=
  match b1, b2 with
  | _, _ =>
      _
  end.
Next Obligation.
  revert b2. induction b1; intros.
  - destruct b2; [ left | right .. ]; congruence.
  - destruct b2; [ | left | ..]; try right; congruence.
  - destruct b2; try (right; congruence).
    specialize (IHb1 b2).
    destruct IHb1; [left | right]; congruence.
  - destruct b2; try (right; congruence).
    specialize (IHb1_1 b2_1).
    specialize (IHb1_2 b2_2).
    destruct IHb1_1, IHb1_2; [ left | right .. ]; congruence.
  - destruct b2; try (right; congruence).
    specialize (IHb1_1 b2_1).
    specialize (IHb1_2 b2_2).
    destruct IHb1_1, IHb1_2; [ left | right .. ]; congruence.
  - destruct b2; try (right; congruence).
    pose proof (aexp_Imp_Lang_dec a1 a0).
    pose proof (aexp_Imp_Lang_dec a2 a3).
    destruct H, H0; [left | right .. ]; congruence.
Defined.

Program Fixpoint imp_Imp_Lang_dec (i1 i2: imp_Imp_Lang) : { i1 = i2 } + { i1 <> i2 } :=
  match i1, i2 with
  | _, _ => _
  end.
Next Obligation.
  revert i2; induction i1; intros; destruct i2; try (right; congruence); try (left; congruence).
  - pose proof (Bdec := bexp_Imp_Lang_dec b b0).
    specialize (IHi1_1 i2_1). specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2, Bdec; [ left | right .. ]; congruence.
  - pose proof (Bdec := bexp_Imp_Lang_dec b b0).
    specialize (IHi1 i2).
    destruct IHi1, Bdec; [left | right ..]; congruence.
  - pose proof (Xdec := string_dec x x0).
    pose proof (Adec := aexp_Imp_Lang_dec a a0).
    destruct Xdec, Adec; [ left | right .. ]; congruence.
  - specialize (IHi1_1 i2_1). specialize (IHi1_2 i2_2).
    destruct IHi1_1, IHi1_2; [ left | right .. ]; congruence.
Defined.
               
              

Definition fun_Imp_Lang_dec (f1 f2: fun_Imp_Lang) : { f1 = f2 } + { f1 <> f2 }.
Proof.
  destruct f1, f2.
  pose proof (Namedec := string_dec  Name Name0).
  pose proof (Argsdec := PeanoNat.Nat.eq_dec Args Args0).
  pose proof (Bodydec := imp_Imp_Lang_dec Body Body0).
  pose proof (Retdec := string_dec Ret Ret0).
  destruct Namedec, Argsdec, Bodydec, Retdec; [left | right .. ]; congruence.
Defined.

Fixpoint construct_fun_app_well_formed (fenv: fun_env) (funcs: list fun_Imp_Lang) (a: aexp_Imp_Lang) : option (fun_app_well_formed fenv funcs a) :=
  match a as a' return option (fun_app_well_formed fenv funcs a') with
  | CONST_Imp_Lang n => Some (fun_app_const fenv funcs n)
  | PARAM_Imp_Lang p => Some (fun_app_param fenv funcs p)
  | VAR_Imp_Lang x => Some (fun_app_var fenv funcs x)
  | PLUS_Imp_Lang a1 a2 =>
      match construct_fun_app_well_formed fenv funcs a1,
        construct_fun_app_well_formed fenv funcs a2 with
      | Some P1, Some P2 => Some (fun_app_plus fenv funcs a1 a2 P1 P2)
      | _, _ => None
      end
  | MINUS_Imp_Lang a1 a2 =>
      match construct_fun_app_well_formed fenv funcs a1,
        construct_fun_app_well_formed fenv funcs a2 with
      | Some P1, Some P2 => Some (fun_app_minus fenv funcs a1 a2 P1 P2)
      | _, _ => None
      end
  | APP_Imp_Lang f args =>
      let func := fenv f in
      match (fix construct_fun_app_args_well_formed (args: list aexp_Imp_Lang) : option (fun_app_args_well_formed fenv funcs args) :=
               match args with
               | nil => Some (fun_app_args_nil fenv funcs)
               | arg :: args' =>
                   match construct_fun_app_well_formed fenv funcs arg, construct_fun_app_args_well_formed args' with
                   | Some Parg, Some Pargs =>
                       Some (fun_app_args_cons fenv funcs arg args' Parg Pargs)
                   | _, _ => None
                   end
               end) args, construct_in fun_Imp_Lang_dec (fenv f) funcs with
      | Some Pargs, Some Pin =>
          (* match fun_Imp_Lang_dec  *)
          match construct_imp_has_variable (Ret (fenv f)) (Body (fenv f)) with
          | Some imp_has_var =>
              match string_dec (Imp_LangTrickLanguage.Name (fenv f)) f with
              | left name_is_f =>
                  match PeanoNat.Nat.eq_dec (Args (fenv f)) (Datatypes.length args) with
                  | left e =>
                      Some (fun_app_this_fun fenv funcs args f (fenv f)
                                             Pargs
                                             (eq_refl _)(* func = fenv f *)
                                             Pin (* In func wf_funcs *)
                                             e
                                             imp_has_var
                                             (or_introl name_is_f))
                  | _ => None
                  end
              | _ =>
                  match string_dec (Imp_LangTrickLanguage.Name (fenv f)) "id" with
                  | left name_is_id =>
                      match PeanoNat.Nat.eq_dec (Args (fenv f)) (Datatypes.length args) with
                      | left e =>
                          
                          Some (fun_app_this_fun fenv funcs args f (fenv f)
                                                 Pargs
                                                 (eq_refl _) (* func = fenv f *)
                                                 Pin (* In func wf_funcs *)
                                                 e
                                                 imp_has_var
                                                 (or_intror name_is_id))
                      | _ => None
                      end
                  | _ => None
                  end
              end
          | _ => None
          end
      | _, _ => None
      end
  end.

           
Fixpoint construct_fun_app_bexp_well_formed fenv funcs b : option (fun_app_bexp_well_formed fenv funcs b) :=
  match b with
  | TRUE_Imp_Lang =>
      Some (fun_app_true fenv funcs)
  | FALSE_Imp_Lang =>
      Some (fun_app_false fenv funcs)
  | NEG_Imp_Lang b' =>
      match construct_fun_app_bexp_well_formed fenv funcs b' with
      | Some Pb' =>
          Some (fun_app_neg fenv funcs b'
                            Pb')
      | None => None
      end
  | LEQ_Imp_Lang a1 a2 =>
      match construct_fun_app_well_formed fenv funcs a1, construct_fun_app_well_formed fenv funcs a2 with
      | Some Pa1, Some Pa2 =>
          Some (fun_app_leq fenv funcs a1 a2
                            Pa1 Pa2)
      | _, _ => None
      end
  | OR_Imp_Lang b1 b2 =>
      match construct_fun_app_bexp_well_formed fenv funcs b1, construct_fun_app_bexp_well_formed fenv funcs b2 with
      | Some Pb1, Some Pb2 =>
              Some (fun_app_or fenv funcs b1 b2
                               Pb1 Pb2)
      | _, _ => None
      end
  | AND_Imp_Lang b1 b2 =>
      match construct_fun_app_bexp_well_formed fenv funcs b1, construct_fun_app_bexp_well_formed fenv funcs b2 with
      | Some Pb1, Some Pb2 =>
          Some (fun_app_and fenv funcs b1 b2
                            Pb1 Pb2)
      | _, _ =>
          None
      end
  end.

Fixpoint construct_fun_app_imp_well_formed fenv funcs i : option (fun_app_imp_well_formed fenv funcs i) :=
  let cfaiwf := construct_fun_app_imp_well_formed fenv funcs in
  let cfabwf := construct_fun_app_bexp_well_formed fenv funcs in
  match i with
  | SKIP_Imp_Lang =>
      Some (fun_app_skip fenv funcs)
  | ASSIGN_Imp_Lang x a =>
      match construct_fun_app_well_formed fenv funcs a with
      | Some WFa =>
          Some (fun_app_assign fenv funcs x a WFa)
      | _ => None
      end
  | SEQ_Imp_Lang i1 i2 =>
      match cfaiwf i1, cfaiwf i2 with
      | Some WFi1, Some WFi2 =>
          Some (fun_app_seq fenv funcs i1 i2
                            WFi1 WFi2)
      | _, _ => None
      end
  | IF_Imp_Lang b i1 i2 =>
      match cfabwf b, cfaiwf i1, cfaiwf i2 with
      | Some WFb, Some WFi1, Some WFi2 =>
          Some (fun_app_if fenv funcs b i1 i2
                           WFb WFi1 WFi2)
      | _, _, _ => None
      end
  | WHILE_Imp_Lang b i' =>
      match cfabwf b, cfaiwf i' with
      | Some WFb, Some WFi' =>
          Some (fun_app_while fenv funcs b i'
                              WFb WFi')
      | _, _ => None
      end
  end.


Ltac prove_fun_app_wf :=
  match goal with
  | [ |- fun_app_imp_well_formed ?fenv ?funcs ?i ] =>
      exact (ReflectionMachinery.optionOut (fun_app_imp_well_formed fenv funcs i)
                                           (construct_fun_app_imp_well_formed fenv funcs i))
  | [ |- fun_app_bexp_well_formed ?fenv ?funcs ?b ] =>
      exact (ReflectionMachinery.optionOut (fun_app_bexp_well_formed fenv funcs b)
                                           (construct_fun_app_bexp_well_formed fenv funcs b))
  | [ |- fun_app_well_formed ?fenv ?funcs ?a ] =>
      exact (ReflectionMachinery.optionOut (fun_app_well_formed fenv funcs a)
                                           (construct_fun_app_well_formed fenv funcs a))
  end.
