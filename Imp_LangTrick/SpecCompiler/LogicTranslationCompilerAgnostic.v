From Coq Require Import String Arith Psatz Bool List.
From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogProp StackLanguage StackLogicGrammar LogicProp EnvToStack.

Module Type ImpToStackExpressionCompilerType.
  Parameter compile_aexp : aexp_Imp_Lang -> (ident -> nat) -> nat -> aexp_stack.
  Parameter compile_bexp : bexp_Imp_Lang -> (ident -> nat) -> nat -> bexp_stack.
End ImpToStackExpressionCompilerType.

Module Type ImpToStackLogicCompilerType.
  Declare Module I2S: ImpToStackExpressionCompilerType.
  Parameter comp_arith : (list ident) -> aexp_Imp_Lang -> aexp_stack.
  Parameter comp_bool : (list ident) -> bexp_Imp_Lang -> bexp_stack.
  Parameter comp_lp : (list ident) -> Imp_Lang_lp -> MetavarPred.
  Parameter comp_logic: nat -> (list ident) -> AbsEnv -> AbsState.
End ImpToStackLogicCompilerType.


Module ImpToStackLogicCompiler(I2S: ImpToStackExpressionCompilerType) <: ImpToStackLogicCompilerType.
  Module I2S := I2S.

  Definition comp_arith idents :=
    fun (aexp: aexp_Imp_Lang) =>
      I2S.compile_aexp aexp
                       (fun (x: ident) => one_index_opt x idents)
                       (List.length idents).

  Definition comp_bool idents :=
    fun (bexp: bexp_Imp_Lang) =>
      I2S.compile_bexp bexp
                       (fun (x: ident) => one_index_opt x idents)
                       (List.length idents).

  Definition comp_lp (idents: list ident) (lp: Imp_Lang_lp) :=
    match lp with
    | Imp_Lang_lp_arith l => MetaNat (compile_prop l (comp_arith idents))
    | Imp_Lang_lp_bool l => MetaBool (compile_prop l (comp_bool idents))
    end.

  Fixpoint comp_logic (args: nat) (idents: list ident) (ae: AbsEnv) :=
    match ae with
    | AbsEnvLP lp => BaseState (AbsStkSize (args + List.length idents))
                              (comp_lp idents lp)
    | AbsEnvAnd l1 l2 => AbsAnd (comp_logic args idents l1)
                               (comp_logic args idents l2)
    | AbsEnvOr l1 l2 => AbsOr (comp_logic args idents l1)
                             (comp_logic args idents l2)
    end.

  Inductive lp_transrelation: nat -> list ident -> Imp_Lang_lp -> MetavarPred -> Prop :=
  | ArithlpTransrelation :
    forall idents args d m,
      compile_prop_rel (comp_arith idents) d m ->
      lp_transrelation args idents (Imp_Lang_lp_arith d) (MetaNat m)
  | BoollpTransrelation :
    forall idents args d m,
      compile_prop_rel (comp_bool idents) d m ->
      lp_transrelation args idents (Imp_Lang_lp_bool d) (MetaBool m).

  Inductive logic_transrelation: nat -> list ident -> AbsEnv -> AbsState -> Prop :=
  | LogicLeafTransrelation :
    forall args idents d s,
      lp_transrelation args idents d s ->
      logic_transrelation args idents
                          (AbsEnvLP d)
                          (BaseState (AbsStkSize ((List.length idents) + args)) s)
  | LogicAndTransrelation :
    forall args idents d1 s1 d2 s2,
      logic_transrelation args idents d1 s1 ->
      logic_transrelation args idents d2 s2 ->
      logic_transrelation args idents (AbsEnvAnd d1 d2) (AbsAnd s1 s2)
  | LogicOrTransrelation :
    forall args idents d1 s1 d2 s2,
      logic_transrelation args idents d1 s1 ->
      logic_transrelation args idents d2 s2 ->
      logic_transrelation args idents (AbsEnvOr d1 d2) (AbsOr s1 s2).
End ImpToStackLogicCompiler.

Require Import EnvToStackIncomplete.
Module IncompleteExpressionCompiler <: ImpToStackExpressionCompilerType.
  Definition compile_aexp := EnvToStackIncomplete.compile_aexp_incomplete.
  Definition compile_bexp := EnvToStackIncomplete.compile_bexp_incomplete.
End IncompleteExpressionCompiler.


Module IncompleteLogicCompiler := ImpToStackLogicCompiler(IncompleteExpressionCompiler).

Require Import EnvToStackBuggy.
Module BuggyExpressionCompiler <: ImpToStackExpressionCompilerType.
  Definition compile_aexp := EnvToStackBuggy.compile_aexp.
  Definition compile_bexp := EnvToStackBuggy.compile_bexp.
End BuggyExpressionCompiler.

Module BuggyLogicCompiler := ImpToStackLogicCompiler(BuggyExpressionCompiler).


  
  
  
