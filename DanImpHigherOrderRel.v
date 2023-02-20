From DanTrick Require Import DanTrickLanguage.

(** Higher order relation(s) (HORs) on the Dan language *)

Local Definition phi_t := imp_Dan -> Prop.

Inductive imp_rec_rel : (imp_Dan -> Prop) -> imp_Dan -> Prop :=
| ImpRecRelSkip :
  forall (phi: phi_t),
    phi SKIP_Dan ->
    imp_rec_rel phi SKIP_Dan
| ImpRecRelAssign :
  forall (phi: phi_t) (x: ident) (a: aexp_Dan),
    phi (ASSIGN_Dan x a) ->
    imp_rec_rel phi (ASSIGN_Dan x a)
| ImpRecRelSeq :
  forall (phi: phi_t) (i1 i2: imp_Dan),
    imp_rec_rel phi i1 ->
    imp_rec_rel phi i2 ->
    phi (SEQ_Dan i1 i2) ->
    imp_rec_rel phi (SEQ_Dan i1 i2)
| ImpRecRelIf :
  forall (phi: phi_t) (b: bexp_Dan) (i__then i__else: imp_Dan),
    imp_rec_rel phi i__then ->
    imp_rec_rel phi i__else ->
    phi (IF_Dan b i__then i__else) -> 
    imp_rec_rel phi (IF_Dan b i__then i__else)
| ImpRecRelWhile :
  forall (phi: phi_t) (b: bexp_Dan) (i__loop: imp_Dan),
    imp_rec_rel phi i__loop ->
    phi (WHILE_Dan b i__loop) ->
    imp_rec_rel phi (WHILE_Dan b i__loop).
                
                     
    
Lemma imp_rec_rel_self :
  forall (i: imp_Dan) (phi: phi_t),
    imp_rec_rel phi i ->
    phi i.
Proof.
  induction i; intros; inversion H; subst; eassumption.
Qed.
