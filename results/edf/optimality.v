Require Export prosa.analysis.facts.transform.edf_opt.

(** * Optimality of EDF on Ideal Uniprocessors *)

(** This module provides the famous EDF optimality theorem: if there
    is any way to meet all deadlines (assuming an ideal uniprocessor
    schedule), then there is also an (ideal) EDF schedule in which all
    deadlines are met. *)

(** The following results assume ideal uniprocessor schedules... *)
Require prosa.model.processor.ideal.
(** ... and the basic (i.e., Liu & Layland) readiness model under which any
    pending job is always ready. *)
Require prosa.model.readiness.basic.

(** ** Optimality Theorem *)

Section Optimality.
  (** For any given type of jobs, each characterized by execution
      costs, an arrival time, and an absolute deadline,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any valid job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** We observe that EDF is optimal in the sense that, if there exists
     any schedule in which all jobs of arr_seq meet their deadline,
     then there also exists an EDF schedule in which all deadlines are
     met. *)
  Theorem EDF_optimality:
    (exists any_sched : schedule (ideal.processor_state Job),
        valid_schedule any_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq any_sched) ->
    exists edf_sched : schedule (ideal.processor_state Job),
        valid_schedule edf_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq edf_sched /\
        EDF_schedule edf_sched.
  Proof.
    move=> [sched [[COME READY] DL_ARR_MET]].
    have ARR  := jobs_must_arrive_to_be_ready sched READY.
    have COMP := completed_jobs_are_not_ready sched READY.
    move: (all_deadlines_met_in_valid_schedule _ _ COME DL_ARR_MET) => DL_MET.
    set sched' := edf_transform sched.
    exists sched'. split; last split.
    - by apply edf_schedule_is_valid.
    - by apply edf_schedule_meets_all_deadlines_wrt_arrivals.
    - by apply edf_transform_ensures_edf.
  Qed.

End Optimality.

(** ** Weak Optimality Theorem *)

(** We further state a weaker notion of the above optimality result
    that avoids a dependency on a given arrival
    sequence. Specifically, it establishes that, given a reference
    schedule without deadline misses, there exists an EDF schedule of
    the same jobs in which no deadlines are missed. *)
Section WeakOptimality.

  (** For any given type of jobs, each characterized by execution
      costs, an arrival time, and an absolute deadline,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... if we have a well-behaved reference schedule ... *)
  Variable any_sched: schedule (ideal.processor_state Job).
  Hypothesis H_must_arrive: jobs_must_arrive_to_execute any_sched.
  Hypothesis H_completed_dont_execute: completed_jobs_dont_execute any_sched.

  (**  ... in which no deadlines are missed, ... *)
  Hypothesis H_all_deadlines_met: all_deadlines_met any_sched.

  (** ...then there also exists an EDF schedule in which no deadlines
      are missed (and in which exactly the same set of jobs is
      scheduled, as ensured by the last clause). *)
  Theorem weak_EDF_optimality:
    exists edf_sched : schedule (ideal.processor_state Job),
      jobs_must_arrive_to_execute edf_sched /\
      completed_jobs_dont_execute edf_sched /\
      all_deadlines_met edf_sched /\
      EDF_schedule edf_sched /\
      forall j,
          (exists t,  scheduled_at any_sched j t) <->
          (exists t', scheduled_at edf_sched j t').
  Proof.
    set sched' := edf_transform any_sched.
    exists sched'. repeat split.
    - by apply edf_transform_jobs_must_arrive.
    - by apply edf_transform_completed_jobs_dont_execute.
    - by apply edf_transform_deadlines_met.
    - by apply edf_transform_ensures_edf.
    - by move=> [t SCHED_j]; apply edf_transform_job_scheduled' with (t0 := t).
    - by move=> [t SCHED_j]; apply edf_transform_job_scheduled with (t0 := t).
  Qed.

End WeakOptimality.
