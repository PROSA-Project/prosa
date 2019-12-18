From mathcomp Require Import ssrnat ssrbool fintype.
Require Export prosa.behavior.all.

(** * Fully-Preemptive EDF Schedules *)

(** This module provides an alternative definition of what it means to be an
    "EDF schedule".

    Note that the "proper" way to define an EDF schedule in Prosa is to use the
    EDF priority policy defined in model.priority.edf and the notion of
    priority-compliant schedules defined in model.schedule.priority_driven, as
    well as the general notion of work-conservation provided in
    model.schedule.work_conserving, which will have the benefit of taking into
    account issues such as various readiness models (e.g., jitter) and diverse
    preemption models (e.g., limited-preemptive jobs).

    The simpler definition offered in this module is (intentionally) oblivious
    to (i.e., not compatible with) issues such as non-preemptive regions or
    self-suspensions, and does not imply anything about work-conservation. In
    other words, it implicitly assumes that pending jobs are always ready and
    at all times preemptable.

    The advantage of this alternative definition is, however, that it is
    largely self-contained and fairly simple, following primarily from first
    principles. This makes it easier to use in certain contexts such as the
    proof of optimality of EDF. *)

Section AlternativeDefinitionOfEDF.

  (** Consider any type of jobs with arrival times, costs, and deadlines ... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any processor model. *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** We say that a schedule is _locally EDF-compliant_ at a given point in
      time [t] if the job [j] scheduled at time [t] has a deadline that is
      earlier than or equal to the deadline of any other job [j'] that could be
      scheduled at time [t] (i.e., arrives at or before time [t]) but is
      actually scheduled later in the given schedule.

      In other words, a schedule is locally EDF-compliant at time [t] if there
      is no witness of a priority inversion (= an already arrived job with an
      earlier deadline) at a later point in the schedule. *)
  Definition EDF_at (sched: schedule PState) (t: instant) :=
    forall (j: Job),
      scheduled_at sched j t ->
      forall (t': instant) (j': Job),
        t <= t' ->
        scheduled_at sched j' t' ->
        job_arrival j' <= t ->
        job_deadline j <= job_deadline j'.

  (** Based on the notion of a locally EDF-compliant schedule given by
      [EDF_at], we say that a schedule is (globally) EDF-compliant
      schedule if it is locally EDF-compliant at every point in
      time. *)
  Definition EDF_schedule (sched: schedule PState) := forall t, EDF_at sched t.

End AlternativeDefinitionOfEDF.







