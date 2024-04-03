From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
Require Import prosa.util.tactics prosa.util.notation.

(** We say that a function [f] is a unit growth function iff for any
    time instant [t] it holds that [f (t + 1) <= f t + 1]. *)
Definition unit_growth_function (f : nat -> nat) :=
  forall t, f (t + 1) <= f t + 1.

(** In this section, we prove a few useful lemmas about unit growth functions. *)
Section Lemmas.

  (** Let [f] be any unit growth function over natural numbers. *)
  Variable f : nat -> nat.
  Hypothesis H_unit_growth_function : unit_growth_function f.

  (** In the following section, we prove a result similar to the
      intermediate value theorem for continuous functions. *)
  Section ExistsIntermediateValue.

    (** Consider any interval <<[x1, x2]>>. *)
    Variable x1 x2 : nat.
    Hypothesis H_is_interval : x1 <= x2.

    (** Let [y] be any value such that [f x1 <= y < f x2]. *)
    Variable y : nat.
    Hypothesis H_between : f x1 <= y < f x2.

    (** Then, we prove that there exists an intermediate point [x_mid] such that [f x_mid = y]. *)
    Lemma exists_intermediate_point :
      exists x_mid,
        x1 <= x_mid < x2 /\ f x_mid = y.
    Proof.
      rename H_is_interval into INT, H_unit_growth_function into UNIT, H_between into BETWEEN.
      move: x2 INT BETWEEN; clear x2.
      suff DELTA:
        forall delta,
          f x1 <= y < f (x1 + delta) ->
          exists x_mid, x1 <= x_mid < x1 + delta /\ f x_mid = y.
      { move => x2 LE /andP [GEy LTy].
        specialize (DELTA (x2 - x1)); feed DELTA.
        { by apply/andP; split; last by rewrite addnBA // addKn. }
        by rewrite subnKC in DELTA.
      }
      elim=> [|delta IHdelta].
      { rewrite addn0; move => /andP [GE0 LT0].
        by apply (leq_ltn_trans GE0) in LT0; rewrite ltnn in LT0.
      }
      { move => /andP [GT LT].
        specialize (UNIT (x1 + delta)); rewrite leq_eqVlt in UNIT.
        have LE: y <= f (x1 + delta).
        { move: UNIT => /orP [/eqP EQ | UNIT]; first by rewrite !addn1 in EQ; rewrite addnS EQ ltnS in LT.
          rewrite [X in _ < X]addn1 ltnS in UNIT.
          apply: (leq_trans _ UNIT).
          by rewrite addn1 -addnS ltnW.
        } clear UNIT LT.
        rewrite leq_eqVlt in LE.
        move: LE => /orP [/eqP EQy | LT].
        { exists (x1 + delta); split; last by rewrite EQy.
          by apply/andP; split; [apply leq_addr | rewrite addnS].
        }
        { feed (IHdelta); first by apply/andP; split.
          move: IHdelta => [x_mid [/andP [GE0 LT0] EQ0]].
          exists x_mid; split; last by done.
          apply/andP; split; first by done.
          by apply: (leq_trans LT0); rewrite addnS.
        }
      }
    Qed.

  End ExistsIntermediateValue.

  (** Next, we prove the same lemma with slightly different boundary conditions. *)
  Section ExistsIntermediateValueLEQ.

    (** Consider any interval <<[x1, x2]>>. *)
    Variable x1 x2 : nat.
    Hypothesis H_is_interval : x1 <= x2.

    (** Let [y] be any value such that [f x1 <= y <= f x2]. Note that
        [y] is allowed to be equal to [f x2]. *)
    Variable y : nat.
    Hypothesis H_between : f x1 <= y <= f x2.

    (** Then, we prove that there exists an intermediate point [x_mid] such that [f x_mid = y]. *)
    Corollary exists_intermediate_point_leq :
      exists x_mid,
        x1 <= x_mid <= x2 /\ f x_mid = y.
    Proof.
      move: (H_between) => /andP [H1 H2].
      move: H2; rewrite leq_eqVlt => /orP [/eqP EQ | LT].
      { exists x2; split.
        - by apply /andP; split => //.
        - by done.
      }
      { edestruct exists_intermediate_point with (x1 := x1) (x2 := x2) as [mid [NEQ EQ]] => //.
        { by apply/andP; split; [ apply H1 | apply LT]. }
        exists mid; split; last by done.
        move: NEQ => /andP [NEQ1 NEQ2].
        by apply/andP; split => //.
      }
    Qed.

  End ExistsIntermediateValueLEQ.

  (** In this section, we, again, prove an analogue of the
      intermediate value theorem, but for predicates over natural
      numbers. *) 
  Section ExistsIntermediateValuePredicates. 

    (** Let [P] be any predicate on natural numbers. *)
    Variable P : nat -> bool.

    (** Consider a time interval <<[t1,t2]>> such that ... *)
    Variables t1 t2 : nat.
    Hypothesis H_t1_le_t2 : t1 <= t2.

    (** ... [P] doesn't hold for [t1] ... *)
    Hypothesis H_not_P_at_t1 : ~~ P t1.

    (** ... but holds for [t2]. *)
    Hypothesis H_P_at_t2 : P t2.
    
    (** Then we prove that within time interval <<[t1,t2]>> there exists
        time instant [t] such that [t] is the first time instant when
        [P] holds. *)
    Lemma exists_first_intermediate_point :
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

End Lemmas.
