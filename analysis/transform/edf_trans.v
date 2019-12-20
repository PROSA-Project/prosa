Require Export prosa.analysis.transform.prefix.
Require Export prosa.analysis.transform.swap.
Require Export prosa.analysis.facts.model.ideal_schedule.

(** In this file we define the EDF transformation of a schedule, which turns a
    (finite prefix of a) schedule into an EDF schedule. This operation is at
    the core of the EDF optimality proof. *)

Section EDFTransformation.
  (** Consider any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and ideal uni-processor schedules. *)
  Let PState := ideal.processor_state Job.
  Let SchedType := schedule (PState).

  (** We say that a state [s1] "has an earlier or equal deadline" than a state
      [s2] if the job scheduled in state [s1] has has an earlier or equal
      deadline than the job scheduled in state [s2]. This function is never
      used on idle states, so the default values are irrelevant. *)
  Definition earlier_deadline (s1 s2: PState) :=
    (oapp job_deadline 0 s1) <= (oapp job_deadline 0 s2).

  (** We say that a state is relevant (for the purpose of the transformation)
      if it is not idle and if the job scheduled in it has arrived prior to
      some given reference time. *)
  Definition relevant_pstate (reference_time: instant) (s: PState) :=
    match s with
    | None => false
    | Some j' => job_arrival j' <= reference_time
    end.

  (** Next, we define a central element of the EDF transformation procedure:
      given a job scheduled at a time [t1], find a later time [t2] before the
      job's deadline at which a job with an earlier-or-equal deadline is
      scheduled. In other words, find a job that causes the [EDF_at] property
      to be violated at time [t1]. *)
  Definition find_swap_candidate (sched: SchedType) (t1: instant) (j: Job) :=
    if search_arg sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j) is Some t
    then t
    else 0.

  (** The point-wise EDF transformation procedure: given a schedule and a time
      [t1], ensure that the schedule satisfies [EDF_at] at time [t1]. *)
  Definition make_edf_at (sched: SchedType) (t1: instant): SchedType :=
    match sched t1 with
    | None => sched (* leave idle instants alone *)
    | Some j =>
      let
        t2 := find_swap_candidate sched t1 j
      in swapped sched t1 t2
    end.

  (** To transform a finite prefix of a given reference schedule, apply
      [make_edf_at] to every point up to the given finite horizon. *)
  Definition edf_transform_prefix (sched: SchedType) (horizon: instant): SchedType :=
    prefix_map sched make_edf_at horizon.

  (** Finally, a full EDF schedule (i.e., one that satisfies [EDF_at] at any
      time) is obtained by first computing an EDF prefix up to and including
      the requested time [t], and by then looking at the last point of the
      prefix. *)
  Definition edf_transform (sched: SchedType) (t: instant): ideal.processor_state Job :=
    let
      edf_prefix := edf_transform_prefix sched t.+1
    in edf_prefix t.

End EDFTransformation.

