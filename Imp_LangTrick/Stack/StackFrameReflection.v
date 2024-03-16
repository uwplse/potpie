From Coq Require Import Arith List Nat String.
Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick Require Import MyOptionUtils StackLanguage StackFrameBase StackExprWellFormed ReflectionMachinery.
Fixpoint construct_n_le_m (n m: nat) : option (n <= m).
Proof.
  destruct n, m.
  - eapply (Some (le_n 0)).
  - pose proof (Nat.le_0_l (S m)).
    eapply (Some H).
  - eapply None.
  - specialize (construct_n_le_m n m).
    destruct construct_n_le_m.
    + eapply (Some (le_n_S _ _ l)).
    + eapply None.
Defined.

Fixpoint frame_diff (i: imp_stack) (frame: nat): option nat :=
  match i with
  | Skip_Stk => Some frame
  | Assign_Stk _ _ => Some frame
  | Push_Stk => Some (frame + 1)
  | Pop_Stk => match frame with
              | 0 => None
              | S n => Some n
              end
  | Seq_Stk i1 i2 =>
      option_bind (frame_diff i1 frame) (frame_diff i2)
  | If_Stk b i1 i2 =>
      let n1 := frame_diff i1 frame in
      let n2 := frame_diff i2 frame in
      match n1, n2 with
      | Some n1', Some n2' =>
          if Nat.eq_dec n1' n2' then
            Some n1'
          else None
      | _, _ => None
      end
  | While_Stk b i' =>
      let n := frame_diff i' frame in
      option_bind n (fun n =>
                     if Nat.eq_dec frame n then
                       Some n
                     else None)
  end.



Fixpoint construct_aexp_frame_rule (a: aexp_stack) (fenv: fun_env_stk) (frame: nat) (fuel: nat) : option (aexp_frame_rule a fenv frame) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match a with
      | Const_Stk n =>
          Some (FrameConst fenv frame n)
      | Var_Stk k =>
          option_map_map (FrameVar fenv frame k)
                         (construct_1_le_k k)
                         (construct_n_le_m k frame)
      | Plus_Stk a1 a2 =>
          option_map_map (FramePlus fenv frame a1 a2)
                         (construct_aexp_frame_rule a1 fenv frame fuel')
                         (construct_aexp_frame_rule a2 fenv frame fuel')
      | Minus_Stk a1 a2 =>
          option_map_map (FrameMinus fenv frame a1 a2)
                         (construct_aexp_frame_rule a1 fenv frame fuel')
                         (construct_aexp_frame_rule a2 fenv frame fuel')
      | App_Stk f args =>
          let func := fenv f in
          match construct_args_frame_rule args fenv frame fuel', construct_imp_frame_rule (Body func) fenv (Args func) (Args func + Return_pop func) fuel' with
          | Some Hargs, Some Hbody =>
              option_map (FrameApp fenv frame f args func Hargs eq_refl Hbody)
                         (construct_aexp_frame_rule (Return_expr func) fenv (Args func + Return_pop func) fuel')
          | _, _ => None
          end
      end
  end
with construct_args_frame_rule (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat) (fuel: nat): option (args_frame_rule args fenv frame) :=
       match  fuel with
       | 0 => None
       | S fuel' =>
           match args with
           | nil => Some (FrameArgsNil fenv frame)
           | hd :: tl =>
               option_map_map (FrameArgsCons fenv frame hd tl)
                              (construct_aexp_frame_rule hd fenv frame fuel')
                              (construct_args_frame_rule tl fenv frame fuel')
           end
       end
with construct_bexp_frame_rule (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) (fuel: nat) : option (bexp_frame_rule b fenv frame) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match b with
           | True_Stk => Some (FrameTrue fenv frame)
           | False_Stk => Some (FrameFalse fenv frame)
           | Neg_Stk b' => option_map (FrameNeg fenv frame b')
                                      (construct_bexp_frame_rule b' fenv frame fuel')
           | And_Stk b1 b2 =>
               option_map_map
                 (FrameAnd fenv frame b1 b2)
                 (construct_bexp_frame_rule b1 fenv frame fuel')
                 (construct_bexp_frame_rule b2 fenv frame fuel')
           | Or_Stk b1 b2 =>
                option_map_map
                 (FrameOr fenv frame b1 b2)
                 (construct_bexp_frame_rule b1 fenv frame fuel')
                 (construct_bexp_frame_rule b2 fenv frame fuel')
           | Leq_Stk a1 a2 =>
               option_map_map
                 (FrameLeq fenv frame a1 a2)
                 (construct_aexp_frame_rule a1 fenv frame fuel')
                 (construct_aexp_frame_rule a2 fenv frame fuel')
           | Eq_Stk a1 a2 =>
               option_map_map
                 (FrameEq fenv frame a1 a2)
                 (construct_aexp_frame_rule a1 fenv frame fuel')
                 (construct_aexp_frame_rule a2 fenv frame fuel')
           end
       end
with construct_imp_frame_rule (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat) (fuel: nat) : option (imp_frame_rule i fenv frame frame') :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match i with
           | Skip_Stk =>
               match Nat.eq_dec frame frame' with
               | left Heq =>
                   eq_rect
                     frame
                     (fun frame'0 : nat =>
                        option (imp_frame_rule Skip_Stk fenv frame frame'0))
                     (Some (FrameSkip fenv frame)) frame' Heq
               | _ => None
               end
                     
           | Assign_Stk k a =>
               match Nat.eq_dec frame frame', construct_1_le_k k, construct_n_le_m k frame, construct_aexp_frame_rule a fenv frame fuel' with
               | left Heq, Some H1, Some H2, Some Ha =>
                   eq_rect
                     frame
                     (fun frame'0 : nat =>
                        option (imp_frame_rule (Assign_Stk k a) fenv frame frame'0))
                     (Some (FrameAssign fenv frame k a H1 H2 Ha)) frame' Heq
               | _, _, _, _ => None
               end
           | Push_Stk =>
               match Nat.eq_dec frame' (frame + 1) with
               | left Heq =>
                   eq_rec_r
                     (fun frame'0 : nat =>
                        option (imp_frame_rule Push_Stk fenv frame frame'0))
                     (Some (FramePush fenv frame)) Heq
               | _ => None
               end
           | Pop_Stk =>
               match Nat.eq_dec frame' (frame - 1), construct_1_le_k frame with
               | left Heq, Some Hge =>
                   eq_rec_r
                     (fun frame'0 : nat => option (imp_frame_rule Pop_Stk fenv frame frame'0))
                     (Some (FramePop fenv frame Hge)) Heq
               | _, _ => None
               end
           | Seq_Stk i1 i2 =>
               match frame_diff i1 frame with
               | Some frame'' =>
                   option_map_map
                     (FrameSeq fenv frame i1 i2 frame'' frame')
                     (construct_imp_frame_rule i1 fenv frame frame'' fuel')
                     (construct_imp_frame_rule i2 fenv frame'' frame' fuel')
               | None => None
               end
           | If_Stk b i1 i2 =>
               match construct_bexp_frame_rule b fenv frame fuel' with
               | Some Hb =>
                   option_map_map
                     (FrameIf fenv frame b i1 i2 frame'
                              Hb)
                     (construct_imp_frame_rule i1 fenv frame frame' fuel')
                     (construct_imp_frame_rule i2 fenv frame frame' fuel')
               | None => None
               end
           | While_Stk b i' =>
               match Nat.eq_dec frame frame' with
               | left Heq =>
                   option_map_map 
                     (fun (Hb : bexp_frame_rule b fenv frame)
                        (Hi : imp_frame_rule i' fenv frame frame) =>
                        eq_rect
                          frame
                          (fun frame'0 : nat =>
                             imp_frame_rule (While_Stk b i') fenv frame frame'0)
                          (FrameWhile fenv frame b i' Hb Hi) frame' Heq)
                     
                     (construct_bexp_frame_rule b fenv frame fuel')
                     (construct_imp_frame_rule i' fenv frame frame fuel')
               | _ => None
               end
           end
       end.


Ltac prove_frame :=
  match goal with
  | [ |- aexp_frame_rule ?a ?fenv ?frame] =>
      exact (optionOut (aexp_frame_rule a fenv frame) (construct_aexp_frame_rule a fenv frame))
  | [ |- bexp_frame_rule ?b ?fenv ?frame] =>
      exact (optionOut (bexp_frame_rule b fenv frame) (construct_bexp_frame_rule b fenv frame))
  | [ |- imp_frame_rule ?i ?fenv ?frame ?frame'] =>
      exact (optionOut (imp_frame_rule i fenv frame frame') (construct_imp_frame_rule i fenv frame frame'))
  end.
