From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems.
From Imp_LangTrick Require Export MultiplicationCompiled ExponentiationCompiled.

Local Open Scope imp_langtrick_scope.

(* sticking this here to reference the tactic... *)
(*Lemma fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
    Proof.
      unfold fenv_well_formed'; unfold SOURCE.funcs; unfold SOURCE.fenv.
      repeat split; unfold square_root_funcs in *; unfold square_root_fenv in *; cbn -[In] in *.
      - finite_nodup.
      - unfold update in H.
        Ltac fenv_well_formed_base :=
          try match goal with
              | [ H: ?func = (update _ _ _) ?f |- _ ] =>
                  unfold update in H
              end;
          match goal with
          | [ H: ?func = (if _ then  _  else  _) |- _ ] =>
              repeat match goal with
                     | [ H: func = (if string_dec ?a ?b then _ else _) |- _ ] =>
                         destruct (string_dec a b)
                     end;
              match goal with
              | [ H: func = _ |- _ ] =>
                  subst func
              end
          end.
        fenv_well_formed_base; try match goal with
                                   | [ |- In ?a ?b \/ _ ] =>
                                       cbn -[In];
                                       match b with
                                       | context P [a] =>
                                           left; finite_in
                                       | _ =>
                                           match a with
                                           | context P [init_fenv] =>
                                               unfold init_fenv;
                                               left; finite_in
                                           end
                                       end
                                   end.
      - fenv_well_formed_base.
        
    Admitted.*)
