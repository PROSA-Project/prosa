From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
Require Export prosa.implementation.definitions.generic_scheduler.
Require Export prosa.analysis.facts.transform.replace_at.

(** * Properties of the Generic Reference Scheduler *)

(** This file establishes some facts about the generic reference scheduler that
    constructs a schedule via pointwise scheduling decisions based on a given
    policy and the preceding prefix. *)

Section GenericScheduleProperties.
  (** For any type of jobs and type of schedule, ... *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any scheduling policy, and ... *)
  Variable policy : PointwisePolicy PState.

  (** ... any notion of idleness. *)
  Variable idle_state : PState.

  (** For notational convenience, we define [prefix t] to denote the finite
      prefix considered when scheduling a job at time [t]. *)
  Let prefix t := if t is t'.+1 then schedule_up_to policy idle_state  t' else empty_schedule idle_state.

  (** To begin with, we establish two simple rewriting lemmas for unrolling
      [schedule_up_to]. First, we observe that the allocation is indeed
      determined by the policy based on the preceding prefix. *)
  Lemma schedule_up_to_def:
    forall t,
      schedule_up_to policy idle_state t t = policy (prefix t) t.
  Proof. by elim=> [|n IH]; rewrite [LHS]/schedule_up_to -/(schedule_up_to _) /replace_at; apply ifT. Qed.

  (** Second, we note how to replace [schedule_up_to] in the general case with
      its definition. *)
  Lemma schedule_up_to_unfold:
    forall h t,
      schedule_up_to policy idle_state h t = replace_at (prefix h) h (policy (prefix h) h) t.
  Proof. by move=> h t; rewrite [LHS]/schedule_up_to /prefix; elim: h. Qed.

  (** Next, we observe that we can increase a prefix's horizon by one
        time unit without changing any allocations in the prefix. *)
  Lemma schedule_up_to_widen:
    forall h t,
      t <= h ->
      schedule_up_to policy idle_state h t = schedule_up_to policy idle_state h.+1 t.
  Proof.
    move=> h t RANGE.
    rewrite [RHS]schedule_up_to_unfold rest_of_schedule_invariant // => EQ.
    now move: RANGE; rewrite EQ ltnn.
  Qed.

  (** After the horizon of a prefix, the schedule is still "empty", meaning
        that all instants are idle. *)
  Lemma schedule_up_to_empty:
    forall h t,
      h < t ->
      schedule_up_to policy idle_state h t = idle_state.
  Proof.
    move=> h t.
    elim: h => [LT|h IH LT].
    { rewrite /schedule_up_to rest_of_schedule_invariant // => ZERO.
      now subst. }
    { rewrite /schedule_up_to rest_of_schedule_invariant -/(schedule_up_to _ h t);
        first by apply IH => //; apply ltn_trans with (n := h.+1).
      move=> EQ. move: LT.
      now rewrite EQ ltnn. }
  Qed.

  (** A crucial fact is that a prefix up to horizon [h1] is identical to a
       prefix up to a later horizon [h2] at times up to [h1]. *)
  Lemma schedule_up_to_prefix_inclusion:
    forall h1 h2,
      h1 <= h2 ->
      forall t,
        t <= h1 ->
        schedule_up_to policy idle_state h1 t = schedule_up_to policy idle_state h2 t.
  Proof.
    move=> h1 h2 LEQ t BEFORE.
    elim: h2 LEQ BEFORE; first by rewrite leqn0 => /eqP ->.
    move=> t' IH.
    rewrite leq_eqVlt ltnS => /orP [/eqP <-|LEQ] // t_H1.
    rewrite IH // schedule_up_to_widen //.
    now apply (leq_trans t_H1).
  Qed.

End GenericScheduleProperties.
