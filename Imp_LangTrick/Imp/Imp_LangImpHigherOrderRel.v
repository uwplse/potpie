From Imp_LangTrick Require Import Imp_LangTrickLanguage.

(** Higher order relation(s) (HORs) on the Imp_Lang language *)

Local Definition phi_t := imp_Imp_Lang -> Prop.

Inductive imp_rec_rel : (imp_Imp_Lang -> Prop) -> imp_Imp_Lang -> Prop :=
| ImpRecRelSkip :
  forall (phi: phi_t),
    phi SKIP_Imp_Lang ->
    imp_rec_rel phi SKIP_Imp_Lang
| ImpRecRelAssign :
  forall (phi: phi_t) (x: ident) (a: aexp_Imp_Lang),
    phi (ASSIGN_Imp_Lang x a) ->
    imp_rec_rel phi (ASSIGN_Imp_Lang x a)
| ImpRecRelSeq :
  forall (phi: phi_t) (i1 i2: imp_Imp_Lang),
    imp_rec_rel phi i1 ->
    imp_rec_rel phi i2 ->
    phi (SEQ_Imp_Lang i1 i2) ->
    imp_rec_rel phi (SEQ_Imp_Lang i1 i2)
| ImpRecRelIf :
  forall (phi: phi_t) (b: bexp_Imp_Lang) (i__then i__else: imp_Imp_Lang),
    imp_rec_rel phi i__then ->
    imp_rec_rel phi i__else ->
    phi (IF_Imp_Lang b i__then i__else) -> 
    imp_rec_rel phi (IF_Imp_Lang b i__then i__else)
| ImpRecRelWhile :
  forall (phi: phi_t) (b: bexp_Imp_Lang) (i__loop: imp_Imp_Lang),
    imp_rec_rel phi i__loop ->
    phi (WHILE_Imp_Lang b i__loop) ->
    imp_rec_rel phi (WHILE_Imp_Lang b i__loop).
                
                     
    
Lemma imp_rec_rel_self :
  forall (i: imp_Imp_Lang) (phi: phi_t),
    imp_rec_rel phi i ->
    phi i.
Proof.
  induction i; intros; inversion H; subst; eassumption.
Qed.
