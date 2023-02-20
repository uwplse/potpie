From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From DanTrick Require Import DanTrickLanguage DanLogProp DanLogicHelpers 
  StackLanguage StackLangEval EnvToStack StackLogicGrammar LogicProp
  LogicTranslationBase.

Lemma arith_args_comp_adequacy : 
  forall map lp_args meta_args, 
  compile_prop_args_rel (comp_arith map) lp_args meta_args
  ->
  List.map (comp_arith map) lp_args = meta_args.
Proof.
  induction lp_args.
  - intros. inversion H. cbv. auto.
  - intros. inversion H. subst.
    simpl. 
    pose proof (IHlp_args args' H4).
    rewrite H0. auto.
Defined.

Lemma bool_args_comp_adequacy : 
  forall map lp_args meta_args, 
  compile_prop_args_rel (comp_bool map) lp_args meta_args
  ->
  List.map (comp_bool map) lp_args = meta_args.
Proof.
  induction lp_args.
  - intros. inversion H. cbv. auto.
  - intros. inversion H. subst.
    simpl. 
    pose proof (IHlp_args args' H4).
    rewrite H0. auto.
Defined.

Lemma arith_args_comp_terminates : 
  forall map lp_args,
  exists meta_args, 
  compile_prop_args_rel (comp_arith map) lp_args meta_args.
Proof.
  induction lp_args.
  - exists (nil (A:= (aexp_stack))). constructor.  
  - inversion IHlp_args. subst. 
    exists ((comp_arith map a)::x).
    econstructor. auto.   
Qed. 

Lemma bool_args_comp_terminates : 
  forall map lp_args,
  exists meta_args,  
  compile_prop_args_rel (comp_bool map) lp_args meta_args. 
Proof.
  induction lp_args.
  - exists (nil (A:= (bexp_stack))). constructor.  
  - inversion IHlp_args. subst. 
    exists ((comp_bool map a)::x).
    econstructor. auto.   
Qed. 

Lemma lp_comp_rel_terminates : 
forall args map lp_Dan, 
exists metavp, 
lp_transrelation args map lp_Dan metavp.
Proof. 
induction lp_Dan; induction l.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - inversion IHl1.
    inversion H. subst.
    inversion H3. subst.
    inversion IHl2.
    inversion H1. subst.
    inversion H6. subst.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    + apply H0.
    + apply H2.
  - inversion IHl1.
    inversion H. subst.
    inversion H3. subst.
    inversion IHl2.
    inversion H1. subst.
    inversion H6. subst.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    + apply H0.
    + apply H2.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - pose proof (arith_args_comp_terminates map a_list).
    inversion H.  
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    apply H0.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - inversion IHl1.
    inversion H. subst.
    inversion H3. subst.
    inversion IHl2.
    inversion H1. subst.
    inversion H6. subst.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    + apply H0.
    + apply H2.
  - inversion IHl1.
    inversion H. subst.
    inversion H3. subst.
    inversion IHl2.
    inversion H1. subst.
    inversion H6. subst.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    + apply H0.
    + apply H2.
  - econstructor.
    econstructor.
    econstructor.
    econstructor.
  - pose proof (bool_args_comp_terminates map a_list).
    inversion H.  
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    apply H0.
Defined.

Lemma log_comp_rel_terminates : 
forall args map lp_Dan, 
exists metavp, 
logic_transrelation args map lp_Dan metavp.
Proof.
  induction lp_Dan.
  - pose proof (lp_comp_rel_terminates args map s).
    inversion H. 
    exists (BaseState (AbsStkSize (List.length map + args)) x).
    econstructor. auto.
  - inversion IHlp_Dan1.
    inversion IHlp_Dan2.  
    exists (AbsAnd x x0).
    econstructor; assumption.   
  - inversion IHlp_Dan1.
    inversion IHlp_Dan2.  
    exists (AbsOr x x0).
    econstructor; assumption.
Defined.



Lemma lp_comp_adequacy_forward :
  forall args map lp_Dan metavp, 
  lp_transrelation args map lp_Dan metavp
    -> 
  comp_lp map lp_Dan = metavp. 
Proof. 
  induction lp_Dan. 
  - induction l. 
    + intros. inversion H. subst. inversion H3. subst. 
      inversion H0. subst. cbv. auto.
    + intros. inversion H. subst. inversion H3. subst. 
      inversion H0. subst. cbv. auto.
    + intros. inversion H. subst. inversion H3. subst. 
      inversion H0. subst. cbv. auto.
    + intros. inversion H. subst. inversion H3. subst. 
      inversion H0. subst. cbv. auto.
    + intros. inversion H. subst. inversion H3. subst.
      inversion H0. subst. 
      pose proof (CompiledArith map args l1 q1 H5).
      pose proof (CompiledArith map args l2 q2 H7).
      pose proof (ArithlpTransrelation map args l1 q1 H1).
      pose proof (ArithlpTransrelation map args l2 q2 H2).
      pose proof (IHl1 (MetaNat q1) H4).
      pose proof (IHl2 (MetaNat q2) H6).
      unfold comp_lp in *. simpl. inversion H8.
      inversion H9. auto.
    + intros. inversion H. subst. inversion H3. subst.
      inversion H0. subst. 
      pose proof (CompiledArith map args l1 q1 H5).
      pose proof (CompiledArith map args l2 q2 H7).
      pose proof (ArithlpTransrelation map args l1 q1 H1).
      pose proof (ArithlpTransrelation map args l2 q2 H2).
      pose proof (IHl1 (MetaNat q1) H4).
      pose proof (IHl2 (MetaNat q2) H6).
      unfold comp_lp in *. simpl. inversion H8.
      inversion H9. auto.
    + intros. inversion H. subst. inversion H3. subst.
      inversion H0. subst. cbv. auto.
    + intros. inversion H. subst. inversion H3. subst.
      inversion H0. subst. inversion H6; subst.
      --cbv. auto.
      --unfold comp_lp in *. simpl.
        pose proof (arith_args_comp_adequacy map args0 args' H1).
        rewrite H2. auto.
  - induction l; intros; inversion H; subst;
    inversion H3; subst; inversion H0; subst. 
    + cbn. auto.
    + cbn. auto.
    + cbn. auto.
    + cbn. auto.
    + pose proof (CompiledBool map args l1 q1 H5).
      pose proof (CompiledBool map args l2 q2 H7).
      pose proof (BoollpTransrelation args map l1 q1 H1).
      pose proof (BoollpTransrelation args map l2 q2 H2).
      pose proof (IHl1 (MetaBool q1) H4).
      pose proof (IHl2 (MetaBool q2) H6).
      unfold comp_lp in *. simpl. inversion H8.
      inversion H9. auto.
    + pose proof (CompiledBool map args l1 q1 H5).
      pose proof (CompiledBool map args l2 q2 H7).
      pose proof (BoollpTransrelation args map l1 q1 H1).
      pose proof (BoollpTransrelation args map l2 q2 H2).
      pose proof (IHl1 (MetaBool q1) H4).
      pose proof (IHl2 (MetaBool q2) H6).
      unfold comp_lp in *. simpl. inversion H8.
      inversion H9. auto.
    + cbn. auto.
    + inversion H6; subst.
      --cbn. auto.
      --unfold comp_lp in *. simpl.
        pose proof (bool_args_comp_adequacy map args0 args' H1).
        rewrite H2. auto.
Defined. 


Lemma log_comp_adequacy_forward :
  forall args map lp_Dan metavp, 
  logic_transrelation args map lp_Dan metavp
    -> 
  comp_logic args map lp_Dan = metavp. 
Proof.
  induction lp_Dan.
  - intros. inversion H. subst.
    pose proof (lp_comp_adequacy_forward args map s s0 H3).
    simpl. subst. rewrite Nat.add_comm. auto.
  - intros. inversion H. subst.
    pose proof (IHlp_Dan1 s1 H4). 
    pose proof (IHlp_Dan2 s2 H6).
    simpl. subst. auto.
  - intros. inversion H. subst.
    pose proof (IHlp_Dan1 s1 H4). 
    pose proof (IHlp_Dan2 s2 H6).
    simpl. subst. auto.
Defined.

Lemma lp_comp_determ : 
  forall args map lp_Dan metavp metavp', 
  lp_transrelation args map lp_Dan metavp
  -> 
  lp_transrelation args map lp_Dan metavp'
  -> 
  metavp = metavp'. 
Proof.
  intros. pose proof (lp_comp_adequacy_forward args map lp_Dan metavp H).
  pose proof (lp_comp_adequacy_forward args map lp_Dan metavp' H0).
  rewrite <- H1. rewrite <- H2. auto.
Defined.

Lemma log_comp_determ : 
  forall args map lp_Dan metavp metavp', 
  logic_transrelation args map lp_Dan metavp
  -> 
  logic_transrelation args map lp_Dan metavp'
  -> 
  metavp = metavp'. 
Proof.
  intros. pose proof (log_comp_adequacy_forward args map lp_Dan metavp H).
  pose proof (log_comp_adequacy_forward args map lp_Dan metavp' H0).
  rewrite <- H1. rewrite <- H2. auto.
Defined.




Lemma logic_transrelation_deterministic :
  forall args map d s s',
    logic_transrelation args map d s ->
    logic_transrelation args map d s' ->
    s = s'.
Proof.
  eapply log_comp_determ.
Defined.

Lemma lp_comp_adequacy_backwards :
  forall args map lp_Dan metavp, 
  comp_lp map lp_Dan = metavp
  ->
  lp_transrelation args map lp_Dan metavp. 
Proof.
  intros. 
  pose proof (lp_comp_rel_terminates args map lp_Dan).
  inversion H0. 
  pose proof (lp_comp_determ args map lp_Dan x metavp H1).
  pose proof (lp_comp_adequacy_forward args map lp_Dan x H1).
  rewrite H3 in H.   
  rewrite <- H. auto.
Defined.

Lemma log_comp_adequacy_backwards : 
  forall args map lp_Dan metavp, 
  comp_logic args map lp_Dan = metavp
  ->
  logic_transrelation args map lp_Dan metavp.
Proof.
  intros. 
  pose proof (log_comp_rel_terminates args map lp_Dan).
  inversion H0. 
  pose proof (log_comp_determ args map lp_Dan x metavp).
  pose proof (log_comp_adequacy_forward args map lp_Dan x H1).
  rewrite H3 in H.   
  rewrite <- H. auto.
Defined.

Lemma log_comp_adequacy : 
  forall args map lp_Dan metavp, 
  logic_transrelation args map lp_Dan metavp
  <->
  comp_logic args map lp_Dan = metavp
.
Proof.
  intros. split.
  - apply log_comp_adequacy_forward.
  - apply log_comp_adequacy_backwards.
Defined.


