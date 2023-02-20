From Coq Require Import List Arith String Program.Equality.
From DanTrick Require Import DanTrickLanguage StackLanguage StackLangTheorems ProofCompiler.
From DanTrick Require Import DanLogSubst DanLogProp DanLogHoare StackLogic.
From DanTrick Require Import LogicTranslationBase EnvToStack LogicProp ProofCompilerHelpers ProofCompilerPostHelpers DanImpHigherOrderRel DanHoareWF LogicTranslationAdequate FunctionWellFormed ParamsWellFormed CompilerAssumptionLogicTrans TranslationPure.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope dantrick_scope.

Definition hl_compile := Tests.hl_compile.



Module Type SourceProgramType.
  Parameter program: imp_Dan.
  Parameter precond postcond: AbsEnv.
  Parameter fenv: fun_env.
  Parameter hoare_triple: hl_Dan precond program postcond fenv.
  Parameter idents: list ident.
  Parameter num_args: nat.
  Parameter funcs: list fun_Dan.

End SourceProgramType.

Module Type TargetProgramType.
  Declare Module SP : SourceProgramType.
  Parameter compile_dan_log: AbsEnv -> AbsState.
  Parameter program: imp_stack.
  Parameter precond postcond: AbsState.
  Parameter fenv: fun_env_stk.
End TargetProgramType.
  

Module TargetProgram (SP: SourceProgramType) <: TargetProgramType.
  Module SP := SP.

  Definition compile_dan_log (d: AbsEnv): AbsState :=
    comp_logic SP.num_args SP.idents d.
  
  Definition program: imp_stack := comp_code SP.program SP.idents SP.num_args.
  Definition precond: AbsState := compile_dan_log SP.precond.
  Definition postcond: AbsState := compile_dan_log SP.postcond.
  Definition fenv: fun_env_stk := compile_fenv SP.fenv.
End TargetProgram.

Module Simplest'.
  Definition program: imp_Dan :=
    SKIP_Dan.

  Definition precond: AbsEnv :=
    AbsEnvLP (Dan_lp_bool (TrueProp bool bexp_Dan)).
  Definition postcond: AbsEnv := precond.

  Definition fenv: fun_env := init_fenv.

  Definition hoare_triple: hl_Dan precond program postcond fenv :=
    hl_Dan_skip precond fenv.

  Definition idents: list ident := nil.

  Definition num_args := 0.

  Definition funcs := (init_fenv "id") :: nil.
End Simplest'.

Module SimplestTargetOther := TargetProgram(Simplest').


Print SimplestTargetOther.

Module Type CompileType.
  Declare Module SOURCE : SourceProgramType.
  Declare Module TARGET : TargetProgramType.
  Parameter fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
  Parameter funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
  Parameter all_params_ok_for_funcs_proof : Forall (fun func => all_params_ok (DanTrickLanguage.Args func)
                                                                           (DanTrickLanguage.Body func))
                                                   SOURCE.funcs.
  Parameter fun_app_well_formed_proof : fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
  Parameter aimp_always_wf_proof : aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.hoare_triple.
  Parameter translate_precond_proof : logic_transrelation SOURCE.num_args SOURCE.idents SOURCE.precond TARGET.precond.
  Parameter translate_postcond_proof : logic_transrelation SOURCE.num_args SOURCE.idents SOURCE.postcond TARGET.postcond.
  Check terminator.
  Parameter terminator_proof : terminator SOURCE.fenv SOURCE.num_args SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.hoare_triple.
  Parameter program_compiled_proof : TARGET.program = comp_code SOURCE.program SOURCE.idents SOURCE.num_args.
  Parameter fun_env_compiled_proof : TARGET.fenv = compile_fenv SOURCE.fenv.
  Parameter precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
  Parameter postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
  Parameter imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
End CompileType.

Module Type CompilerType.
  Parameter proof_compiler : forall (d1 d2 : AbsEnv)
                               (i : imp_Dan)
                               (fenv : fun_env)
                               (hl : hl_Dan d1 i d2 fenv),
    forall (funcs: list fun_Dan),
      fenv_well_formed' funcs fenv ->
      forall (map : list DanTrickLanguage.ident) (args : nat) (s1 : AbsState) (i' : imp_stack) (s2 : AbsState) (fenv0 : fun_env_stk),
      forall (OKfuncs: funcs_okay_too funcs fenv0)
        (OKparams : Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) funcs),
        fun_app_imp_well_formed fenv funcs i ->
        aimp_always_wf funcs map args d1 i d2 fenv hl ->
        logic_transrelation args map d1 s1 ->
        logic_transrelation args map d2 s2 ->
        forall (ARNOLD: terminator fenv args d1 d2 i hl),
        i' = comp_code i map args ->
        fenv0 = compile_fenv fenv ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d1 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d2 ->
        imp_rec_rel (var_map_wf_wrt_imp map) i -> hl_stk s1 i' s2 fenv0.
End CompilerType.

Module DefaultCompiler <: CompilerType.
  Definition proof_compiler := hl_compile.
End DefaultCompiler.

Module CompileProof (CT : CompileType) (CerT: CompilerType).
  Module CT := CT.
  Module S := CT.SOURCE.
  Module T := CT.TARGET.

  Definition compiled : hl_stk T.precond T.program T.postcond T.fenv :=
    CerT.proof_compiler S.precond
                        S.postcond
                        S.program
                        S.fenv
                        S.hoare_triple
                        S.funcs
                        CT.fenv_well_formed_proof
                        S.idents
                        S.num_args
                        T.precond
                        T.program
                        T.postcond
                        T.fenv
                        CT.funcs_okay_too_proof
                        CT.all_params_ok_for_funcs_proof
                        CT.fun_app_well_formed_proof
                        CT.aimp_always_wf_proof
                        CT.translate_precond_proof
                        CT.translate_postcond_proof
                        CT.terminator_proof
                        CT.program_compiled_proof
                        CT.fun_env_compiled_proof
                        CT.precond_wf_proof
                        CT.postcond_wf_proof
                        CT.imp_code_wf_proof.
End CompileProof.
