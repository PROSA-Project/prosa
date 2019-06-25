From rt.restructuring.model Require Export schedule.edf.
From rt.restructuring.analysis Require Import schedulability transform.facts.edf_opt.

(** This file contains the theorem that states the famous EDF
    optimality result: if there is any way to meet all deadlines
    (assuming an ideal uniprocessor), then there is also an EDF
    schedule in which all deadlines are met. *)

Section Optimality.
  (* For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.
  
  (* ... and any valid job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (* We observe that EDF is optimal in the sense that, if there exists
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
        is_EDF_schedule edf_sched.
  Proof.
    move=> [sched [[COME [ARR COMP]] DL_ARR_MET]].
    move: (all_deadlines_met_in_valid_schedule _ _ COME DL_ARR_MET) => DL_MET.
    set sched' := edf_transform sched.
    exists sched'. split; last split.
    - by apply edf_schedule_is_valid.
    - by apply edf_schedule_meets_all_deadlines_wrt_arrivals.
    - by apply edf_transform_ensures_edf.
  Qed.

End Optimality.

(** We further state a weaker notion of the above optimality claim
    that avoids a dependency on a given arrival sequence. *)
Section WeakOptimality.

  (* For any given type of jobs,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (* ...if we have a well-behaved schedule in which no deadlines are missed,... *)
  Variable any_sched: schedule (ideal.processor_state Job).
  Hypothesis H_must_arrive: jobs_must_arrive_to_execute any_sched.
  Hypothesis H_completed_dont_execute: completed_jobs_dont_execute any_sched.
  Hypothesis H_all_deadlines_met: all_deadlines_met any_sched.

  (* ...then there also exists a corresponding EDF schedule in which
     no deadlines are missed (and in which exactly the same set of
     jobs is scheduled, as ensured by the last clause). *)
  Theorem weak_EDF_optimality:
    exists edf_sched : schedule (ideal.processor_state Job),
      jobs_must_arrive_to_execute edf_sched /\
      completed_jobs_dont_execute edf_sched /\
      all_deadlines_met edf_sched /\
      is_EDF_schedule edf_sched /\
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
