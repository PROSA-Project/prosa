Require Export prosa.analysis.facts.model.ideal_schedule.
Require Export prosa.analysis.facts.behavior.deadlines.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.model.priority.edf.
Require Export prosa.model.schedule.edf.
Require Export prosa.model.schedule.priority_driven.
Require Import prosa.model.readiness.basic.
Require Import prosa.model.preemption.fully_preemptive.

(** * Equivalence of EDF Definitions *)

(** Recall that we have defined "EDF schedules" in two ways.

    The generic way to define an EDF schedule is by using the EDF priority
    policy defined in [model.priority.edf] and the general notion of
    priority-compliant schedules defined in [model.schedule.priority_driven].

    Another, more straight-forward way to define an EDF schedule is the standalone
    definition given in [model.schedule.edf], which is less general but simpler
    and used in the EDF optimality proof.

    In this file, we show that both definitions are equivalent assuming:

    (1) ideal uniprocessor schedules,

    (2) the classic Liu & Layland model of readiness without jitter and
    without self-suspensions, where pending jobs are always ready, and

    (3) that jobs are fully preemptive. *)

Section Equivalence.

  (** We assume the basic (i.e., Liu & Layland)
      readiness model under which any pending job is ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** We assume that jobs are fully preemptive. *)
  #[local] Existing Instance fully_preemptive_model.

  (** For any given type of jobs, each characterized by an arrival time,
      an execution cost, and an absolute deadline, ... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...consider a given valid job arrival sequence ... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ...and a corresponding schedule. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** Suppose jobs don't execute after their completion, ... *)
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...all jobs come from the arrival sequence [arr_seq], ...*)
  Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

  (** ...and jobs from [arr_seq] don't miss their deadlines. *)
  Hypothesis H_no_deadline_misses: all_deadlines_of_arrivals_met arr_seq sched.

  (** We first show that a schedule that satisfies the standalone
      [EDF_schedule] predicate is also compliant with the generic notion of EDF
      policy defined in Prosa, namely the [respects_policy_at_preemption_point]
      predicate. *)
  Lemma EDF_schedule_implies_respects_policy_at_preemption_point :
    EDF_schedule sched ->
    respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).
  Proof.
    move=> EDF j' j t ARR PREEMPTION BL SCHED.
    have suff: exists t' : nat, t <= t' < job_deadline j' /\ scheduled_at sched j' t'.
    { move=> [t' [/andP [LE _] SCHED']].
      apply: (EDF t); [done | exact LE | exact SCHED' |].
      by apply: (backlogged_implies_arrived sched j' t). }
    apply; apply: incomplete_implies_scheduled_later;
      first by apply: H_no_deadline_misses => //.
    by apply: (backlogged_implies_incomplete sched j' t).
  Qed.

  (** Conversely, the reverse direction also holds: a schedule that satisfies
      the [respects_policy_at_preemption_point] predicate is also an EDF
      schedule in the sense of [EDF_schedule]. *)
  Lemma respects_policy_at_preemption_point_implies_EDF_schedule :
    respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job) ->
    EDF_schedule sched.
  Proof.
    move=> H_priority_driven t j_hp SCHED t' j LEQ SCHED' EARLIER_ARR.
    case (boolP (j == j_hp)); first by move /eqP => EQ; subst.
    move /neqP => NEQ.
    exploit (H_priority_driven j j_hp t) => //.
    { by apply (H_from_arr_seq _ _ SCHED'). }
    { by rewrite /preemption_time; destruct (sched t). }
    { apply /andP; split => //.
      - apply /andP; split => //.
        apply (incompletion_monotonic _ j _ _ LEQ).
        by apply scheduled_implies_not_completed.
      - apply /negP; move => SCHED''.
        by exploit (ideal_proc_model_is_a_uniprocessor_model j j_hp sched t). }
  Qed.

  (** From the two preceding lemmas, it follows immediately that the two EDF
      definitions are indeed equivalent, which we note with the following
      corollary. *)
  Corollary EDF_schedule_equiv:
    EDF_schedule sched <-> respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).
  Proof.
    split.
    - by apply EDF_schedule_implies_respects_policy_at_preemption_point.
    - by apply respects_policy_at_preemption_point_implies_EDF_schedule.
  Qed.

End Equivalence.
