From Coq Require Import List String Arith.
From Imp_LangTrick Require Import StackLanguage StackDec.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Fixpoint frame_of_aexp (funcs: list fun_stk) (fenv: fun_env_stk) (frame: option nat) a :=
  match a with
  | Const_Stk _ => true
  | Var_Stk k =>
      let res := Nat.leb 1 k in
      match frame with
      | Some size =>
          andb res (Nat.leb k size)
      | _ => res
      end
  | Plus_Stk a1 a2 =>
      andb (frame_of_aexp funcs fenv frame a1) (frame_of_aexp funcs fenv frame a2)
  (* with *)
      (* | Some f1, Some f2 => *)
          (* if f1 =? f2 then *)
            (* if f1 =? frame then *)
              (* Some f1 *)
            (* else None *)
          (* else None *)
      (* | _, _ => None *)
      (* end *)
  | Minus_Stk a1 a2 =>
      andb (frame_of_aexp funcs fenv frame a1) (frame_of_aexp funcs fenv frame a2)
      (* match frame_of_aexp funcs fenv frame a1, frame_of_aexp funcs fenv frame a2 with *)
      (* | Some f1, Some f2 => *)
          (* if f1 =? f2 then *)
            (* if f1 =? frame then *)
              (* Some f1 *)
            (* else None *)
          (* else None *)
      (* | _, _ => None *)
      (* end *)
  | App_Stk f args =>
      let func := fenv f in
      if in_dec fun_stk_dec func funcs then
        if (Args func) =? (List.length args) then
          fold_left (fun acc elmt =>
                       (* match acc with *)
                       (* | Some f => *)
                           andb acc (frame_of_aexp funcs fenv frame elmt)
                       (* | None => None *)
                     (* end *)
                    )
                    args
                    true
        else false
      else false
  (* | _ => None *)
  end.


Fixpoint frame_of_bexp (funcs: list fun_stk) (fenv: fun_env_stk) (frame: option nat) b :=
  match b with
  | True_Stk => true
  | False_Stk => true
  | Neg_Stk b' =>
      frame_of_bexp funcs fenv frame b'
  | And_Stk b1 b2 =>
        
        (fun val => andb val (frame_of_bexp funcs fenv frame b2)) (frame_of_bexp funcs fenv frame b1)
  | Or_Stk b1 b2 =>
        (fun val => andb val (frame_of_bexp funcs fenv frame b2))
        (frame_of_bexp funcs fenv frame b1)
  | Leq_Stk a1 a2 =>
        (fun val => andb val (frame_of_aexp funcs fenv frame a2))
        (frame_of_aexp funcs fenv frame a1)
  | Eq_Stk a1 a2 =>
        (fun val => andb val (frame_of_aexp funcs fenv frame a2))
        (frame_of_aexp funcs fenv frame a1)
  end.


Fixpoint frame_of_imp (funcs: list fun_stk) (fenv: fun_env_stk) (frame: nat) (body: imp_stack) {struct body} : option nat :=
  match body with
  | Skip_Stk => Some frame
  | Assign_Stk k a =>
      if (S O <=? k)%nat then
        if (k <=? frame) then
          if frame_of_aexp funcs fenv (Some frame) a then
          (* | Some frame' => *)
              (* if Nat.eqb frame frame' then *)
                Some frame
          else None
          (* | _ => None *)
          (* end *)
        else None
      else None
  | Push_Stk =>
      Some (frame + (S O))%nat
  | Pop_Stk =>
      if (1 <=? frame)%nat then
        Some (frame - (S O))%nat
      else None
  | Seq_Stk i1 i2 =>
      match frame_of_imp funcs fenv frame i1 with
      | Some frame1 =>
          frame_of_imp funcs fenv frame1 i2
      | None => None
      end
  | If_Stk b i1 i2 =>
      if frame_of_bexp funcs fenv (Some frame) b then
      (* | Some frameb => *)
          (* if frame =? frameb then *)
            match frame_of_imp funcs fenv frame i1, frame_of_imp funcs fenv frame i2 with
            | Some f1, Some f2 =>
                if (f1 =? f2)%nat then Some f1
                else None
            | _, _ => None
            end
          (* else None *)
      (* | _ => None *)
      (* end *)
      else None
  | While_Stk b i' =>
      if frame_of_bexp funcs fenv (Some frame) b then
      (* | Some frameb => *)
          (* if (frame =? frameb)%nat then *)
            frame_of_imp funcs fenv frame i'
          (* else None *)
      (* | _ => None *)
                 (* end *)
      else None
  end.
      


Definition funcs_frame (funcs: list fun_stk) (fenv: fun_env_stk) :=
  fold_left
    (fun acc elmt =>
       let body := Body elmt in
       let ret_expr := Return_expr elmt in
       let args := Args elmt in
       let num_pop := Return_pop elmt in
       match (frame_of_imp funcs fenv args body) with
       | Some f =>
           if frame_of_aexp funcs fenv (Some f) ret_expr then
           (* | Some f' => *)
             if (args + num_pop =? f)%nat then
               andb acc true
             else false
           (* | _ => false *)
           (* end *)
           else false
       | _ => false
       end)
    funcs true.
                   
              
