From mathcomp Require Import ssreflect ssrbool eqtype ssrnat zify.zify.
Require Import prosa.util.tactics prosa.util.notation prosa.util.rel.

(** We say that a function [f] is a unit growth function iff for any
    time instant [t] it holds that [f (t + 1) <= f t + 1]. *)
Definition unit_growth_function (f : nat -> nat) :=
  forall t, f (t + 1) <= f t + 1.

(** In this section, we prove a few useful lemmas about unit growth functions. *)
Section Lemmas.

  (** Let [f] be any unit growth function over natural numbers. *)
  Variable f : nat -> nat.
  Hypothesis H_unit_growth_function : unit_growth_function f.

  (** Since [f] is a unit-growth function, the value of [f] after [k]
      steps is at most [k] greater than its value at the starting
      point. *)
  Lemma unit_growth_function_k_steps_bounded :
    forall (x k : nat),
      f (x + k) <= k + f x.
  Proof.
    intros x k; induction k.
    { by rewrite addn0 add0n. }
    { rewrite addnS; apply: leq_trans.
      { by rewrite -addn1; apply H_unit_growth_function. }
      { lia. }
    }
  Qed.

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
      { rewrite addn0 => /andP [GE0 LT0].
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
        move: H_t1_le_t2; rewrite leq_eqVlt => /orP [/eqP EQ | NEQ1]; last by done.
        by exfalso; subst t2; move: H_not_P_at_t1 => /negP NPt1.
      }
      have MIN := ex_minnP EX.
      move: MIN => [x /andP [Px /andP [LT1 LT2]] MIN]; clear EX.
      exists x; repeat split; [ apply/andP; split | | ]; try done.
      move => y /andP [NEQ1 NEQ2]; apply/negPn; intros Py.
      feed (MIN y).
      { apply/andP; split; first by done.
        apply/andP; split.
        - move: NEQ1. rewrite leq_eqVlt => /orP [/eqP EQ | NEQ1]; last by done.
          by exfalso; subst y; move: H_not_P_at_t1 => /negP NPt1.
        - by apply ltnW, leq_trans with x.
      }
      by move: NEQ2; rewrite ltnNge => /negP NEQ2.
    Qed.

  End ExistsIntermediateValuePredicates.

End Lemmas.


(** * Slowing Functions to Unit-Step Growth

    Next, we define and prove a few properties about a function that
    converts any function into a unit-step function. This construction
    will be used later to define Supply-Bound Functions (SBFs), which
    must satisfy this growth constraint in some of the RTAs.  *)

(** ** Slowed Function

    Given a function [F : nat -> nat], we define a slowed version [slowed
    F] such that [slowed F n] grows no faster than one unit per input
    increment. Intuitively, [slowed F] matches [F] when [slowed F n =
    F n], and otherwise "lags behind" [F] to enforce the unit-growth
    constraint.

    The definition is recursive: [slowed F n] is the minimum of [F n]
    and [1 + slowed F (n-1)].  *)
Fixpoint slowed (F : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => F 0
  | n'.+1 => minn (F n'.+1) (slowed F n').+1
  end.

(** Given two functions [f] and [F], if [f] is a unit-growth function
    and [f <= F] pointwise up to [Δ], then [f Δ <= slowed F Δ]. *)
Lemma slowed_respects_pointwise_leq :
  forall (f F : nat -> nat) (Δ : nat),
    unit_growth_function f  ->
    (forall x, x <= Δ -> f x <= F x) ->
    f Δ <= slowed F Δ.
Proof.
  move => f F x SL LE; induction x as [|n IH]; first by apply: LE.
  have [CLE|Hcase] := leqP (F n.+1) (slowed F n + 1).
  { rewrite leq_min; apply/andP; split; first by apply LE.
    apply: leq_trans; first by apply LE.
    by rewrite addn1 in CLE.
  }
  { rewrite leq_min; apply/andP; split; first by apply LE.
    apply: leq_trans; first by rewrite -addn1; apply SL.
    by rewrite -[in leqRHS]addn1 leq_add2r; apply IH.
  }
Qed.

(** The [slowed] function grows at most by 1 per step (i.e., it's unit-growth). *)
Lemma slowed_is_unit_step :
  forall (f : nat -> nat),
    unit_growth_function (slowed f).
Proof.
  unfold unit_growth_function; intros f x; rewrite !addn1.
  by induction x; simpl; lia.
Qed.

(** If [f] is monotone, then [slowed f] is also monotone. *)
Lemma slowed_respects_monotone :
  forall (f : nat -> nat),
    monotone leq f ->
    monotone leq (slowed f).
Proof.
  move => f MON x y NEQ.
  interval_to_duration x y k; induction k as [ | k IHk].
  { by rewrite addn0. }
  { rewrite addnS //=; apply:leq_trans; first by apply IHk.
    move: (MON (x + k) (x + k).+1 ltac:(done)) => MONS.
    rewrite leq_min; apply/andP; split; last by done.
    apply: leq_trans; last by apply MONS.
    by clear; induction (x + k); [done | simpl; lia].
  }
Qed.

(** The slowed version of a function never exceeds the original
    function. *)
Lemma slowed_never_exceeds :
  forall (f : nat -> nat) (x : nat),
    slowed f x <= f x.
Proof.
  by intros f x; destruct x; [ simpl | apply geq_minl].
Qed.

(** If some value [A] is bounded by [F - f δ] for a function [f], then
    it is also bounded above by [F - slowed f δ]. *)
Corollary bound_preserved_under_slowed :
  forall (f : nat -> nat) (δ : nat) (A F : nat),
    A <= F - f δ ->
    A <= F - slowed f δ.
Proof.
  intros f δ A F LE; apply: leq_trans; first by apply: LE.
  by apply leq_sub2l; destruct δ; last by apply geq_minl.
Qed.

(** Consider a monotone function [f] and the derived function [Δ ↦ Δ -
    f Δ]. We show that whenever this derived function attains a value
    at some interval length [Δ], there exists a (possibly smaller)
    interval length [δ ≤ Δ] at which the same value is obtained after
    applying the "slowing" transformation [slowed f].

    Intuitively, this lemma justifies replacing [f] by its slowed
    version without losing any possible output of [Δ - f Δ], because
    for any [Δ] we can find a suitable [δ] where the slowed version
    matches. *)
Lemma slowed_subtraction_value_preservation :
  forall (f : nat -> nat) (Δ : nat),
    monotone leq f ->
    exists (δ : nat),
      δ <= Δ
      /\ Δ - f Δ = δ - slowed f δ.
Proof.
  move=> f Δ MON.
  set g := fun n => n - slowed f n.
  have NNDC: forall n, g n <= g n.+1.
  { move=> n.
    have STEP: slowed f n.+1 <= slowed f n + 1 by rewrite -addn1; apply slowed_is_unit_step.
    by rewrite /g; lia.
  }
  have SLOW : forall n, g n.+1 <= g n + 1.
  { intros n; rewrite /g -addn1 leq_subLR.
    have [O1|O2] := leqP (slowed f n) n.
    { rewrite addnA addnBA // [_ + n]addnC -addnBA; first by lia.
      by apply slowed_respects_monotone => //; lia.
    }
    { by have LE: slowed f n <=  slowed f (n + 1);
      [apply slowed_respects_monotone => //; lia | lia].
    }
  }
  have SLLE: forall n, slowed f n <= f n by intros n; induction n as [|n IH];[ simpl; lia | apply geq_minl].
  have LEG: Δ - f Δ <= g Δ by apply: leq_sub => //.
  set P := fun n => (n <= Δ) && (Δ - f Δ <= g n).
  have PEX : exists n, P n by (exists Δ); apply/andP; split; [apply leqnn| apply LEG].
  have MIN := ex_minnP PEX; move: MIN => [δmin Pmin MIN].
  move: Pmin => /andP [LE Pδmin].
  exists δmin; split; first by done.
  have [ZERO|POS] := posnP δmin; first by have g0: g 0 = 0; [done | subst; rewrite /g in Pδmin; lia].
  have [δs EQ] : exists δs, δs.+1 = δmin by (exists δmin.-1; lia).
  have LTs: g δs < Δ - f Δ.
  { move_neq_up LEδs.
    specialize (MIN δs).
    by feed MIN; [apply/andP; split; lia | lia].
  }
  move: (Pδmin) => Hδ. rewrite -EQ in Hδ.
  have GAP: g δs + 1 <= Δ - f Δ by lia.
  have F1 : Δ - f Δ <= g (δs.+1) by unfold g in *; lia.
  have F2 : g δs.+1 <= g δs + 1 by apply SLOW.
  have F3 : g δs + 1 <= Δ - f Δ by lia.
  unfold g in *.
  by apply/eqP; rewrite eqn_leq; apply/andP; split; [lia | rewrite -!EQ; lia].
Qed.
