## Claims
1. `stack_pure`: This captures what it means for an expression to
   preserve the stack: the rest of the stack will be the same before
   and after.
6. `transform_prop_exprs_adequacy_forward`: The formalization is very similar 
   to the prose description in theorem 4.
7. `UIP_AbsEnv`: This is just UIP for specifications in our source logic
8. `UIP_fun_env_refl`: UIP for function environments - there should 
   only ever be one function environment by compilation. 
9. `fun_app_while`: This rule is fully described in the paper. 
10. `inv_fun_app_imp_while`: Note that this is a `Qed` as opposed to a
	`Defined`. This is for opacity and runtime reasons, as it makes the
	application of the inversion tactic opaque.
11. `hl_compile`: This is the program definition for our proof compiler. The 
	type `induction_P` contains all of the well-formedness and termination 
	conditions required for the soundness of the logic translation as in 13. 
12. `log_sound_forward`: This contains the same basic well-formedness 
	constraints as 21, except the `OKfuncs` and `OKparams` assumptions. `OKfuncs`
	states that all functions in the target language must obey the frame rule, and
	`OKparams` states that all non-identity functions in the Imp function 
	environment do not invoke more parameters than they take arguments. 
13. `log_sound_backwards`: This contains the same well-formedness 
	constraints as 12, plus a termination condition that states that all language
	expressions contained within the logical formulae in the Imp logic will always
	terminate. 
14. `LPModule`: The module for LogicProp instantiations with UIP for types `V`
and `A`. 
17. `aexp_compiler_term_assump_backwards`: This contains largely the same 
	constraints as 21, save that it contains the condition 
	`(exists x, a_Dan aD dbenv fenv_d nenv x)`, 
	which ensures that the expression being compiled terminates. 
18. `bexp_compiler_term_assump_backwards`: This contains largely the same 
	constraints as 21, save that it contains the condition 
	`(exists x, b_Dan aD dbenv fenv_d nenv x)`, 
	which ensures that the expression being compiled terminates. 
19. `a_Dan`, `args_Dan`, `b_Dan`, `i_Dan`: The semantics for the Imp language. 
	This is projected into `Prop`. If 
	`_Dan exp args function_environment variable_environment val` 
	has a proof, then `exp` evaluates to `val` under the corresponding environment. 
20. `aexp_stack_sem`, `bexp_stack_sem`, `imp_stack_sem`, `args_stack_sem`: The 
	semantics for the Stack language. This is project into `Prop`. If 
	`_stack_em exp function_environment stack val` has a proof, then has a proof, 
	then `exp` evaluates to `val` under `stack`. 
21. `compiler_sound_mut_ind`: This is a mutually inductive statement of compiler
	correctness. Because the mutual induction helper lemmas somewhat obfuscate the 
	intuition behind this theorem in the statement, we encourage the reader to 
	scroll up to line 12, where `P_compiler_sound` is defined and has the 
	assumptions exposed. The well-formedness conditions ensure that functions are 
	called on the correct number of arguments and that the called functions 
	themselves are well-formed (`FUN_WF`), the function environment itself contains
	only a finite number of non-identity, well-formed functions (`FENV_WF`), the 
	program being compiled has the correct number of argument values in its 
	argument environment (`List.length dbenv = num_args`), and that the mapping 
	from variables actually translates all of the variables contained in the 
	program being compiled (`imp_rec_rel (var_map_wf_wrt_imp idents) i`). 
22. `Hoare_Dan_sound`: This is the statement and proof of soundness of
	the `hl_Dan` Hoare proof construct for the Imp language with
	regards to the Hoare triple definition `triple_Dan`.
23. `Hoare_stk_sound`: This is the statement and proof of soundness of
	the `hl_stk` Hoare proof construct for the Stack language with
	regards to the Hoare triple definition `triple_stk`.
