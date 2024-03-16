From Coq Require Import List Arith String Program.Equality.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage StackLangTheorems ProofCompiler.
From Imp_LangTrick Require Import Imp_LangLogSubst Imp_LangLogProp Imp_LangLogHoare StackLogic.
From Imp_LangTrick Require Import LogicTranslationBase EnvToStack LogicProp ProofCompilerHelpers ProofCompilerPostHelpers Imp_LangImpHigherOrderRel Imp_LangHoareWF LogicTranslationAdequate FunctionWellFormed ParamsWellFormed CompilerAssumptionLogicTrans TranslationPure FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompilableCodeCompiler ProofCompMod.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.

Module Type TargetProgramInputs.
  Parameter target_fenv : fun_env_stk.
  Parameter target_facts : list Base.ident -> nat -> StackLogic.implication_env_stk.
End TargetProgramInputs.

Module CompilerAgnosticProofCompilableTargetProgram (SP: SourceProgramType) (CC: CodeCompilerType) (SC: SpecificationCompilerType) (TPI: TargetProgramInputs) <: TargetProgramType.
  Module SP := SP.
  Definition compile_imp_lang_log (d: AbsEnv) : AbsState :=
    SC.comp_logic SP.num_args SP.idents d.
  Definition program : imp_stack := CC.compile_imp SP.program SP.idents SP.num_args.
  Definition precond : AbsState := compile_imp_lang_log SP.precond.
  Definition postcond : AbsState := compile_imp_lang_log SP.postcond.
  Definition fenv : fun_env_stk := TPI.target_fenv.
  Definition facts : StackLogic.implication_env_stk := TPI.target_facts SP.idents SP.num_args.
End CompilerAgnosticProofCompilableTargetProgram.
  

Module Type CompilerAgnosticProofCompilerType.
  Declare Module PC : ProofCompilableType.
  Declare Module CC : CheckableCodeCompilerType.
  Declare Module SC : CheckableSpecificationCompilerType.

  Parameter proof_compiler :
    forall (d1 d2: AbsEnv) (i: imp_Imp_Lang) (fenv: fun_env)
      (facts: implication_env)
      (fact_cert: Imp_LangLogHoare.fact_env_valid facts fenv)
      facts'
      (hl: hl_Imp_Lang d1 i d2 facts fenv),
    forall (funcs: list fun_Imp_Lang),
      fenv_well_formed' funcs fenv ->
      forall (map: list ident) (args : nat)
        (s1: AbsState) (i': imp_stack)
        (s2: AbsState) (fenv': fun_env_stk),
      forall (OKfuncs: funcs_okay_too funcs fenv')
        (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs),
        fun_app_imp_well_formed fenv funcs i ->
        aimp_always_wf funcs map args d1 i d2 fenv facts hl ->
        PC.check_proof fenv funcs d1 d2 i facts map args hl ->
        SC.comp_logic args map d1 = s1 ->
        SC.comp_logic args map d2 = s2 ->
        SC.check_logic d1 = true ->
        SC.check_logic d2 = true ->
        i' = CC.compile_imp i map args ->
        CC.check_imp i = true ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d1 ->
        AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d2 ->
        imp_rec_rel (var_map_wf_wrt_imp map) i ->
        PC.valid_imp_trans_def facts facts' fenv fenv' map args ->
        hl_stk s1 i' s2 facts' fenv'.
End CompilerAgnosticProofCompilerType.

Module Type ProgramProofCompilationType.
  Declare Module CAPC : CompilerAgnosticProofCompilerType.
  Declare Module SOURCE : SourceProgramType.
  Declare Module TARGET : TargetProgramType.

  
  Parameter pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Parameter post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Parameter fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
  Parameter fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
  Parameter funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
  Parameter all_params_ok_for_funcs_proof :
    Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func)
                                   (Imp_LangTrickLanguage.Body func))
           SOURCE.funcs.
  Parameter fun_app_well_formed_proof : fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
  Parameter aimp_always_wf_proof : aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
  Parameter check_proof_proof : CAPC.PC.check_proof SOURCE.fenv SOURCE.funcs SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.facts SOURCE.idents SOURCE.num_args SOURCE.hoare_triple.
  
  Parameter translate_precond_proof : CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.precond = TARGET.precond.
  Parameter translate_postcond_proof : CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.postcond = TARGET.postcond.

  Parameter check_logic_precond_proof :
    CAPC.SC.check_logic SOURCE.precond = true.

  Parameter check_logic_postcond_proof :
    CAPC.SC.check_logic SOURCE.postcond = true.
  Parameter program_compiled_proof : TARGET.program = CAPC.CC.compile_imp SOURCE.program SOURCE.idents SOURCE.num_args.
  Parameter check_imp_proof :
    CAPC.CC.check_imp SOURCE.program = true.
  Parameter precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
  Parameter postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
  Parameter imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
  Parameter implication_transformer :  CAPC.PC.valid_imp_trans_def SOURCE.facts TARGET.facts SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args. 
End ProgramProofCompilationType.

Module CompileProof (CT : ProgramProofCompilationType).
  Module CT := CT.
  Module S := CT.SOURCE.
  Module T := CT.TARGET.

  Definition compiled : hl_stk T.precond T.program T.postcond T.facts T.fenv :=
    CT.CAPC.proof_compiler S.precond
                        S.postcond
                        S.program
                        S.fenv
                        S.facts
                        CT.fact_cert
                        T.facts
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
                        CT.check_proof_proof
                        CT.translate_precond_proof
                        CT.translate_postcond_proof
                        CT.check_logic_precond_proof
                        CT.check_logic_postcond_proof
                        (* CT.terminator_proof *)
                        CT.program_compiled_proof
                        CT.check_imp_proof
                        (* CT.fun_env_compiled_proof *)
                        CT.precond_wf_proof
                        CT.postcond_wf_proof
                        CT.imp_code_wf_proof
                        CT.implication_transformer.
End CompileProof.
