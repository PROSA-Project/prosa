Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.jitter.job prosa.classic.model.arrival.jitter.task_arrival
               prosa.classic.model.arrival.jitter.arrival_sequence prosa.classic.model.arrival.jitter.arrival_bounds.
Require Import prosa.classic.model.schedule.uni.schedule_of_task prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.schedulability prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.jitter.schedule
               prosa.classic.model.schedule.uni.jitter.busy_interval
               prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.analysis.uni.jitter.workload_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTimeAnalysisFP.

  Import ArrivalSequenceWithJitter JobWithJitter TaskArrivalWithJitter ArrivalBounds
         UniprocessorScheduleWithJitter ScheduleOfTask SporadicTaskset Priority
         ResponseTime WorkloadBoundFP Platform Schedulability BusyInterval.

  (* In this section, we prove that any fixed point in the RTA for jitter-aware
     uniprocessor FP scheduling is a response-time bound. *)
  Section ResponseTimeBound.

    Context {SporadicTask: eqType}.
    Variable task_cost: SporadicTask -> time.
    Variable task_period: SporadicTask -> time.
    Variable task_deadline: SporadicTask -> time.
    Variable task_jitter: SporadicTask -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> SporadicTask.
    
    (* Consider any task set ts... *)
    Variable ts: seq SporadicTask.

    (* ...with positive task periods. *)
    Hypothesis H_positive_periods: forall tsk, tsk \in ts -> task_period tsk > 0.

    (* Consider any job arrival sequence with consistent, duplicate-free arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
    
    (* ... in which jobs arrive sporadically,... *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.

    (* ...the cost of each job is bounded by the cost of its task, ... *)
    Hypothesis H_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).

    (* ...and the jitter of each job is bounded by the jitter of its task. *)
    Hypothesis H_job_jitter_le_task_jitter:
      forall j,
        arrives_in arr_seq j ->
        job_jitter j <= task_jitter (job_task j).

    (* Assume that all jobs in the arrival sequence come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Next, consider any uniprocessor schedule of this arrival sequence... *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
    (* ...such that jobs do not execute before the jitter has passed nor after completion. *)
    Hypothesis H_jobs_execute_after_jitter: jobs_execute_after_jitter job_arrival job_jitter sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Consider any FP policy that indicates a higher-or-equal priority relation,
       where the relation is reflexive and transitive. *)
    Variable higher_eq_priority: FP_policy SporadicTask.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    
    (* Next, assume that the schedule is a jitter-aware, work-conserving FP schedule. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost job_jitter arr_seq sched.
    Hypothesis H_respects_fp_policy:
      respects_FP_policy job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority.
    
    (* Now we proceed with the analysis.
       Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: SporadicTask.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Recall the definition of response-time bound and the total workload bound W
       for higher-or-equal-priority tasks (with respect to tsk). *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    Let W := total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk.

    (* Let R be any positive fixed point of the response-time recurrence. *)
    Variable R: time.
    Hypothesis H_R_positive: R > 0.
    Hypothesis H_response_time_is_fixed_point: R = W R.

    (* Since R = W R bounds the workload of higher-or-equal priority and actual arrival
       time in any interval of length R, it follows from the busy-interval lemmas that
       R bounds the response-time of job j.
       (For more details, see model/uni/jitter/busy_interval.v and
        analysis/uni/jitter/workload_bound_fp.v.) *)
    Theorem uniprocessor_response_time_bound_fp:
      response_time_bounded_by tsk (task_jitter tsk + R).
    Proof.
      unfold valid_sporadic_job_with_jitter, valid_sporadic_job,
             valid_sporadic_taskset, is_valid_sporadic_task in *.
      rename H_response_time_is_fixed_point into FIX.
      intros j IN JOBtsk.
      set arr := actual_arrival job_arrival job_jitter.
      apply completion_monotonic with (t := arr j + R); try (by done).
      {
        rewrite -addnA leq_add2l leq_add2r.
        by rewrite -JOBtsk; apply H_job_jitter_le_task_jitter.
      }
      set prio := FP_to_JLFP job_task higher_eq_priority.
      apply busy_interval_bounds_response_time with (arr_seq0 := arr_seq)
                                                    (higher_eq_priority0 := prio); try (by done).
        - by intros x; apply H_priority_is_reflexive.
        - by intros x z y; apply H_priority_is_transitive.
      intros t.
      apply fp_workload_bound_holds with (task_cost0 := task_cost)
            (task_period0 := task_period) (task_jitter0 := task_jitter) (ts0 := ts); try (by done).
      by rewrite JOBtsk.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.