From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From DanTrick Require Import DanTrickLanguage DanLogProp DanLogicHelpers StackLanguage StackLangEval EnvToStack StackLogicGrammar LogicProp.


Definition comp_arith sig := 
  ((fun a => (compile_aexp a (fun x => one_index_opt x sig) 
  (List.length sig))))
  . 

Definition comp_bool sig := 
  (fun a => (compile_bexp a (fun x => one_index_opt x sig) 
  (List.length sig)))
  . 

Definition comp_lp map lp_Dan :=
  match lp_Dan with
  |Dan_lp_arith l => MetaNat (compile_prop l (comp_arith map))
  |Dan_lp_bool l => MetaBool (compile_prop l (comp_bool map))
  end.
  
Fixpoint comp_logic args map log_Dan :=
  match log_Dan with
  |AbsEnvLP lp => BaseState (AbsStkSize (args + List.length map)) 
    (comp_lp map lp)
  |AbsEnvAnd l1 l2 => AbsAnd (comp_logic args map l1) (comp_logic args map l2)
  |AbsEnvOr l1 l2 => AbsOr (comp_logic args map l1) (comp_logic args map l2)
  end.

Inductive lp_arith_transrelation : 
  nat -> 
  (list DanTrickLanguage.ident) -> 
  LogicProp nat aexp_Dan -> 
  LogicProp nat aexp_stack -> 
  Prop :=
    |CompiledArith : 
      forall sig args d s,
      compile_prop_rel (comp_arith sig) d s ->
      lp_arith_transrelation args sig d s. 


Inductive lp_bool_transrelation : 
  nat ->
  (list DanTrickLanguage.ident) -> 
  LogicProp bool bexp_Dan -> 
  LogicProp bool bexp_stack -> 
  Prop :=
    |CompiledBool : 
      forall sig args d s,
      compile_prop_rel (comp_bool sig) d s ->
      lp_bool_transrelation args sig d s. 

Inductive lp_transrelation : 
  nat ->
  (list DanTrickLanguage.ident) -> 
  Dan_lp -> 
  MetavarPred -> 
  Prop :=
  |ArithlpTransrelation : 
    forall sig args d s,
    lp_arith_transrelation args sig d s -> 
    lp_transrelation args sig (Dan_lp_arith d) (MetaNat s)
  |BoollpTransrelation : 
    forall args sig d s,
    lp_bool_transrelation args sig d s -> 
    lp_transrelation args sig (Dan_lp_bool d) (MetaBool s). 

Inductive logic_transrelation : 
  nat -> 
  (list DanTrickLanguage.ident) -> 
  AbsEnv -> 
  AbsState -> 
  Prop :=
  | LogicLeafTransrelation : 
    forall args sig d s, 
    lp_transrelation args sig d s -> 
    logic_transrelation args sig 
      (AbsEnvLP d) 
      (BaseState (AbsStkSize ((List.length sig) + args)) s)
  | LogicAndTransrelation :
    forall args sig d1 s1 d2 s2,
    logic_transrelation args sig d1 s1 -> 
    logic_transrelation args sig d2 s2 ->
    logic_transrelation args sig (AbsEnvAnd d1 d2) (AbsAnd s1 s2)
  | LogicOrTransrelation : 
    forall args sig d1 s1 d2 s2,
    logic_transrelation args sig d1 s1 -> 
    logic_transrelation args sig d2 s2 ->
    logic_transrelation args sig (AbsEnvOr d1 d2) (AbsOr s1 s2).

Inductive state_to_stack : 
  (list DanTrickLanguage.ident) ->
  nat_env ->
  (list nat) ->
  (list nat) -> 
  Prop := 
  | State_trans : 
    forall map nenv dbenv,
    state_to_stack map nenv dbenv ((List.map nenv map) ++ dbenv).

Inductive compile_arith_args : 
  nat -> 
  (list DanTrickLanguage.ident) -> 
  list aexp_Dan -> 
  list aexp_stack -> 
  Prop :=
  |CompiledArithArgs : 
    forall sig args d s,
    compile_prop_args_rel (comp_arith sig) d s ->
    compile_arith_args args sig d s. 

Inductive compile_bool_args : 
  nat -> 
  (list DanTrickLanguage.ident) -> 
  list bexp_Dan -> 
  list bexp_stack -> 
  Prop :=
  |CompiledBoolArgs : 
    forall sig args d s,
    compile_prop_args_rel (comp_bool sig) d s ->
    compile_bool_args args sig d s.

Scheme compile_prop_args_rel_ind := Induction for compile_prop_args_rel Sort Prop.
Check compile_prop_args_rel_ind. 
