From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems.


From Imp_LangTrick Require Import Multiplication HelperFenvWF.
From Imp_LangTrick Require Import MultiplicationTreeCompiled.
Local Open Scope imp_langtrick_scope.



Module CompileProdTreeCorrect.
  Include CompileProdTreeOnly.
    Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. constructor. intros. split.
    - intros. simpl. 
      inversion H1; subst. inversion H3; subst. 
      inversion H4; subst. inversion H9; subst. 
      inversion H8; subst. 
      econstructor.
      + inversion H0; subst. simpl. econstructor. simpl. 
        lia.
      + inversion H0; subst. econstructor. econstructor;
        econstructor; try lia.
        * simpl. lia.  
        * simpl. apply H11.
        * simpl. lia.
        * simpl. apply H6.
        * repeat econstructor.       
    - unfold SourceProd.num_args in H. econstructor.
      inversion H1; subst. inversion H4; subst.
      inversion H0; subst. inversion H7; subst. 
      inversion H5; subst. inversion H11; subst.
      simpl in *.
      inversion H12; subst. simpl in *.       
      repeat econstructor; try lia.
      apply H16. apply H19.    
  Defined.

  Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. unfold compile_fenv. unfold series_fenv. unfold imp_fenv_ify. simpl. constructor; split; intros; simpl. 
    - invs H0. simpl in H0. invs H1. invs H3. invs H4. invs H9.
      invs H10. invs H11. simpl. 
      econstructor. econstructor. simpl. lia.
      econstructor. econstructor. econstructor; try simpl; try lia. 
      apply H6. econstructor; try simpl; try lia. apply H8.
      econstructor. simpl. lia. simpl. lia. simpl. exists. apply H12.
      repeat econstructor.
    - invs H0. simpl in H0. invs H1. invs H7. invs H3. invs H11.
      invs H12. invs H13. simpl in *.
      econstructor. econstructor. econstructor.
      + econstructor. lia. apply H16.
      + econstructor. lia. apply H19.
      + econstructor.  exists.
      + invs H22. apply H14.            
  Defined.
End CompileProdTreeCorrect.
