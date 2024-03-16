From Coq Require Import Arith Psatz Bool String List Program.Equality Nat.
Print LoadPath.
From Imp_LangTrick Require Import StackLanguage.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(* Function for evaluation, with fuel because of while loops *)

Fixpoint popping_helper (stk: stack) (to_pop: nat): option stack :=
  match to_pop with
  | 0 => Some stk
  | S to_pop' =>
      match stk with
      | nil => None
      | _ :: stk' => popping_helper stk' to_pop'
      end
  end.

Fixpoint aexp_stack_eval (a: aexp_stack) (fuel: nat) (fenv: fun_env_stk) (stk: stack): option (stack * nat) :=
  match fuel with
  | 0 =>
      let big_res :=
        (match a with
         | Const_Stk n => Some (stk, n)
         | Var_Stk k =>
             match nth_error stk (k - 1) with
             | Some val =>
                 Some (stk, val)
             | None => None
             end
         | _ => None
         end) in
      big_res
  | S fuel' =>
      match a with
      | Const_Stk n => Some (stk, n)
      | Var_Stk k =>
          match nth_error stk (k - 1) with
          | Some val =>
              Some (stk, val)
          | None => None
          end
      | Plus_Stk a1 a2 =>
          match (aexp_stack_eval a1 fuel' fenv stk) with
          | Some stk_and_num =>
              match stk_and_num with
              | (stk1, n1) =>
                  match (aexp_stack_eval a2 fuel' fenv stk1) with
                  | Some stk_and_num2 =>
                      match stk_and_num2 with
                      | (stk2, n2) =>
                          Some (stk2, n1 + n2)
                      end
                  | None => None
                  end
              end
          | None => None
          end
      | Minus_Stk a1 a2 =>
          match (aexp_stack_eval a1 fuel' fenv stk) with
          | Some stk_and_num =>
              match stk_and_num with
              | (stk1, n1) =>
                  match (aexp_stack_eval a2 fuel' fenv stk1) with
                  | Some stk_and_num2 =>
                      match stk_and_num2 with
                      | (stk2, n2) =>
                          Some (stk2, n1 - n2)
                      end
                  | None => None
                  end
              end
          | None => None
          end
      | App_Stk f aexps =>
          let func := fenv f in
          let body := (Body func) in
          let ret_expr := (Return_expr func) in
          let ret_pop := (Return_pop func) in
          let num_args := (Args func) in
          if Nat.eqb num_args (List.length aexps) then
            match args_stack_eval aexps fuel' fenv stk with
            | Some stklistnat =>
                let (stk', args) := stklistnat in
                match imp_stack_eval body fuel' fenv (args ++ stk') with
                | Some stk'' =>
                    match aexp_stack_eval ret_expr fuel' fenv stk'' with
                    | Some stknat =>
                        let (stk''', ret_val) := stknat in
                        match popping_helper stk''' (num_args + ret_pop) with
                        | Some stk4 => Some (stk4, ret_val)
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
          else None
      end
  end
with args_stack_eval (aexps: list aexp_stack) (fuel: nat) (fenv: fun_env_stk) (stk: stack): option (stack * (list nat)) :=
       match fuel with
       | 0 => None
       | S fuel' =>
           match aexps with
           | a :: aexps' =>
               match aexp_stack_eval a fuel' fenv stk with
               | Some stknat =>
                   let (stk', n) := stknat in
                   match (args_stack_eval aexps' fuel' fenv stk') with
                   | Some stklistnat =>
                       let (stk'', ns) := stklistnat in
                       Some (stk'', n :: ns)
                   | None => None
                   end
               | None => None
               end
           | nil => Some (stk, nil)
           end
       end
with bexp_stack_eval (b: bexp_stack) (fuel: nat) (fenv: fun_env_stk) (stk: stack): option (stack * bool) :=
       match fuel with
       | 0 =>
           let big_res :=
             (match b with
              | True_Stk => Some (stk, true)
              | False_Stk => Some (stk, false)
              | _ => None
              end) in
           big_res
       | S fuel' =>
           match b with
           | True_Stk => Some (stk, true)
           | False_Stk => Some (stk, false)
           | Neg_Stk b =>
               match bexp_stack_eval b fuel' fenv stk with
               | Some stkbool =>
                   match stkbool with
                   | (stk', bval) =>
                       Some (stk', negb bval)
                   end
               | None => None
               end
           | And_Stk b1 b2 =>
               match bexp_stack_eval b1 fuel' fenv stk with
               | Some stkbool1 =>
                   let (stk1, bval1) := stkbool1 in
                   match bexp_stack_eval b2 fuel' fenv stk1 with
                   | Some stkbool2 =>
                       let (stk2, bval2) := stkbool2 in
                       Some (stk2, andb bval1 bval2)
                   | None => None
                   end
               | None => None
               end
           | Or_Stk b1 b2 =>
               match bexp_stack_eval b1 fuel' fenv stk with
               | Some stkbool1 =>
                   match stkbool1 with
                   | (stk1, bval1) =>
                       match bexp_stack_eval b2 fuel' fenv stk1 with
                       | Some stkbool2 =>
                           match stkbool2 with
                           | (stk2, bval2) => Some (stk2, orb bval1 bval2)
                           end
                       | None => None
                       end
                   end
               | None => None
               end          
            | Leq_Stk a1 a2 =>
               match aexp_stack_eval a1 fuel' fenv stk with
               | Some stknat1 =>
                   match stknat1 with
                   | (stk1, val1) =>
                       match aexp_stack_eval a2 fuel' fenv stk1 with
                       | Some stknat2 =>
                           match stknat2 with
                           | (stk2, val2) => Some (stk2, Nat.leb val1 val2)
                           end
                       | None => None
                       end
                   end
               | None => None
               end
           | Eq_Stk a1 a2 =>
               match aexp_stack_eval a1 fuel' fenv stk with
               | Some stknat1 =>
                   match stknat1 with
                   | (stk1, val1) =>
                       match aexp_stack_eval a2 fuel' fenv stk1 with
                       | Some stknat2 =>
                           match stknat2 with
                           | (stk2, val2) => Some (stk2, Nat.eqb val1 val2)
                           end
                       | None => None
                       end
                   end
               | None => None
               end
           end
       end
with imp_stack_eval (i: imp_stack) (fuel: nat) (fenv: fun_env_stk) (stk: stack) : option stack :=
       match fuel with
       | 0 =>
           let bigres :=
             match i with
             | Skip_Stk => Some stk
             | Push_Stk => Some (0 :: stk)
             | Pop_Stk =>
                 match stk with
                 | v :: stk' => Some stk'
                 | nil => None
                 end
             | _ => None
             end in
           bigres
       | S fuel' =>
           match i with
           | Skip_Stk => Some stk
           | Assign_Stk k a =>
               match aexp_stack_eval a fuel' fenv stk with
               | Some stknat =>
                   let (stk', n) := stknat in
                   update_stack stk' k n
               | None => None
               end
           | Push_Stk => Some (0 :: stk)
           | Pop_Stk =>
               match stk with
               | v :: stk' => Some stk'
               | nil => None
               end
           | Seq_Stk i1 i2 =>
               match imp_stack_eval i1 fuel' fenv stk with
               | Some stk1 =>
                   imp_stack_eval i2 fuel' fenv stk1
               | None => None
               end
           | If_Stk b i1 i2 =>
               match bexp_stack_eval b fuel' fenv stk with
               | Some stkbool =>
                   let (stk', b') := stkbool in
                   imp_stack_eval (if b' then i1 else i2) fuel' fenv stk'
               | None => None
               end
           | While_Stk b i =>
               match bexp_stack_eval b fuel' fenv stk with
               | Some stkbool =>
                   match stkbool with
                   | (stk', b') =>
                       if b' then
                         imp_stack_eval (Seq_Stk i (While_Stk b i)) fuel' fenv stk'
                       else Some stk'
                   end
               | None => None
               end
           end
       end.

Definition update {T: Type} (x: ident) (v: T) (s: store T): store T :=
fun y => if string_dec x y then v else s y.

Fixpoint construct_fenv_stk lst (f: fun_env_stk) : fun_env_stk :=
match lst with
| nil => f
| foo::foos => construct_fenv_stk foos (update ((foo).(Name)) foo f)
end.

Definition eval_fuel_stack prog fuel stack :=
    match prog with
    |Prog_Stk funs exp => 
    imp_stack_eval exp fuel (construct_fenv_stk funs init_fenv_stk) stack
end.
         
               
