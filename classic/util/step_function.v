From rt.util Require Export step_function.

Require Import rt.classic.util.tactics rt.classic.util.notation rt.classic.util.induction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.

Section StepFunction.

  (* In this section, we prove an analogue of the intermediate
     value theorem, but for predicates of natural numbers. *) 
  Section ExistsIntermediateValuePredicates. 

    (* Let P be any predicate on natural numbers. *)
    Variable P: nat -> bool.

    (* Consider a time interval [t1,t2] such that ... *)
    Variables t1 t2: nat.
    Hypothesis H_t1_le_t2: t1 <= t2.

    (* ... P doesn't hold for t1 ... *)
    Hypothesis H_not_P_at_t1: ~~ P t1.

    (* ... but holds for t2. *)
    Hypothesis H_P_at_t2: P t2.
    
    (* Then we prove that within time interval [t1,t2] there exists time 
       instant t such that t is the first time instant when P holds. *)
    Lemma exists_first_intermediate_point:
      exists t, (t1 < t <= t2) /\ (forall x, t1 <= x < t -> ~~ P x) /\ P t.
    Proof.
      have EX: exists x, P x && (t1 < x <= t2).
      { exists t2.
        apply/andP; split; first by done.
        apply/andP; split; last by done.
        move: H_t1_le_t2; rewrite leq_eqVlt; move => /orP [/eqP EQ | NEQ1]; last by done.
          by exfalso; subst t2; move: H_not_P_at_t1 => /negP NPt1. 
      }
      have MIN := ex_minnP EX.
      move: MIN => [x /andP [Px /andP [LT1 LT2]] MIN]; clear EX.
      exists x; repeat split; [ apply/andP; split | | ]; try done.
      move => y /andP [NEQ1 NEQ2]; apply/negPn; intros Py.
      feed (MIN y). 
      { apply/andP; split; first by done.
        apply/andP; split.
        - move: NEQ1. rewrite leq_eqVlt; move => /orP [/eqP EQ | NEQ1]; last by done.
            by exfalso; subst y; move: H_not_P_at_t1 => /negP NPt1. 
        - by apply ltnW, leq_trans with x.
      }
        by move: NEQ2; rewrite ltnNge; move => /negP NEQ2.
    Qed.
    
  End ExistsIntermediateValuePredicates.  

End StepFunction.