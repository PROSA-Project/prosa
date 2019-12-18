Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task
               prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.schedule.uni.schedulability prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.jitter.schedule
               prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.valid_schedule
               prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule
               prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties
               prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service
               prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_taskset_generation.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* In this file, we determine task response-time bounds in suspension-aware
   schedules using a reduction to jitter-aware schedules. *)
Module RTAByReduction.

  Import TaskArrival SporadicTaskset Suspension Priority Workload Service Schedulability
         UniprocessorScheduleWithJitter ResponseTime SuspensionIntervals ValidSuspensionAwareSchedule.

  Module susp_aware := PlatformWithSuspensions.
  Module reduction := JitterScheduleConstruction.
  Module reduction_prop := JitterScheduleProperties.
  Module reduction_serv := JitterScheduleService.
  Module ts_gen := JitterTaskSetGeneration.

  Section ComparingResponseTimeBounds.

    Context {Task: eqType}.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (** Basic Setup & Setting *)
    
    (* Let ts be any task set with constrained deadlines. *)
    Variable ts: seq Task.
    Hypothesis H_constrained_deadlines:
      constrained_deadline_model task_period task_deadline ts.

    (* Consider any consistent, duplicate-free job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.
    
    (* ...with sporadic arrivals... *)
    Hypothesis H_sporadic_arrivals:
      sporadic_task_model task_period job_arrival job_task arr_seq.

    (* ...and in which all jobs come from task set ts. *)
    Hypothesis H_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Since we consider real-time tasks, assume that job deadlines are equal to task deadlines. *)
    Hypothesis H_job_deadlines_equal_task_deadlines:
      forall j, arrives_in arr_seq j -> job_deadline j = task_deadline (job_task j).

    (* Consider any FP policy that is reflexive, transitive and total.
       Note that the policy does not depend on the schedule. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: FP_is_total_over_task_set higher_eq_priority ts.
    Let job_higher_eq_priority := FP_to_JLDP job_task higher_eq_priority.
     
    (* Assume that jobs and tasks have associated costs... *)
    Variable job_cost: Job -> time.
    Variable task_cost: Task -> time.

    (* ...and suspension times. *)
    Variable job_suspension_duration: job_suspension Job.
    Variable task_suspension_bound: Task -> time.

    (* Assume that jobs have positive cost. *)
    Hypothesis H_positive_costs:
      forall j, arrives_in arr_seq j -> job_cost j > 0.
    
    (* Next, consider any valid suspension-aware schedule of this arrival sequence.
       (Note: see prosa.classic.model.schedule.uni.susp.valid_schedule.v for details) *)
    Variable sched_susp: schedule Job.
    Hypothesis H_valid_schedule:
      valid_suspension_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                      job_suspension_duration job_cost sched_susp.
    
    (** Analysis Setup *)

    (* Now we proceed with the proof. Let tsk be the task to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* For simplicity, let's define some local names. *)
    Let other_hep_task tsk_other :=
      higher_eq_priority tsk_other tsk && (tsk_other != tsk).    
    Let task_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched_susp.
    Let job_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_job job_arrival job_cost sched_susp.
    Let completed_in_sched_susp_by := completed_by job_cost sched_susp.
    Let job_misses_no_deadline_in_sched_susp :=
      job_misses_no_deadline job_arrival job_cost job_deadline sched_susp.
    
    (* Assume that each task is associated a value R... *)
    Variable R: Task -> time.   
    
    (* ...that bounds the response-time of all tasks with higher-or-equal priority
       (other than tsk) in the suspension-aware schedule sched_susp. *)
    Hypothesis H_valid_response_time_bound_of_hp_tasks:
      forall tsk_hp,
        tsk_hp \in ts ->
        other_hep_task tsk_hp ->
        task_response_time_in_sched_susp_bounded_by tsk_hp (R tsk_hp).

    (* The existence of those response-time bounds implies that we can compute the actual
       response times of the higher-priority jobs in sched_susp. *)
    Definition actual_response_time (j_hp: Job) : time :=
      [pick-min r <= R (job_task j_hp) |
         job_response_time_in_sched_susp_bounded_by j_hp r].

    (* Next, let j be any job of tsk... *)
    Variable j: Job.
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_of_tsk: job_task j = tsk.

    (* ...and assume that all the previous jobs of same task do not miss any
       deadlines in sched_susp. *)
    Hypothesis H_no_deadline_misses_for_previous_jobs:
      forall j0,
        arrives_in arr_seq j0 ->
        job_arrival j0 < job_arrival j ->
        job_task j0 = job_task j ->
        job_misses_no_deadline_in_sched_susp j0.
    
    (** Instantiation of the Reduction *)
    
    (* First, recall the parameters of the jitter-aware task set. *)
    Let inflated_task_cost := ts_gen.inflated_task_cost task_cost task_suspension_bound tsk.
    Let task_jitter := ts_gen.task_jitter task_cost higher_eq_priority tsk.

    (* Then, using the actual response times of higher-priority jobs as parameters, we construct
       the jitter-aware schedule from sched_susp. *)
    Let sched_jitter := reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority
                        job_cost job_suspension_duration j actual_response_time.

    (* Next, recall the corresponding job parameters... *)
    Let inflated_job_cost := reduction.inflated_job_cost job_cost job_suspension_duration j.
    Let job_jitter := reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j
                                           actual_response_time.
    
    (* ...and the definition of job response-time bound in sched_jitter. *)
    Let job_response_time_in_sched_jitter_bounded_by :=
      is_response_time_bound_of_job job_arrival inflated_job_cost sched_jitter.

    (** Central Hypothesis *)
    
    (* Assume that using some jitter-aware RTA, we determine that
       (R tsk) is a response-time bound for tsk in sched_jitter. *)
    Hypothesis H_valid_response_time_bound_in_sched_jitter:
      job_response_time_in_sched_jitter_bounded_by j (R tsk).

    (** **** Main Claim *)

    (* Then, we use the properties of the reduction to prove that (R tsk) is also a
       response-time bound for tsk in the original schedule sched_susp. *)
    Theorem valid_response_time_bound_in_sched_susp:
      job_response_time_in_sched_susp_bounded_by j (R tsk).
    Proof.
      rename H_priority_is_reflexive into REFL, H_priority_is_transitive into TRANS,
             H_priority_is_total into TOT, H_jobs_from_taskset into FROM,
             H_valid_response_time_bound_of_hp_tasks into RESPhp,
             H_valid_response_time_bound_in_sched_jitter into RESPj.
      rewrite -H_job_of_tsk /job_response_time_in_sched_susp_bounded_by.
      apply reduction_serv.jitter_reduction_job_j_completes_no_later with (job_task0 := job_task)
        (ts0 := ts) (arr_seq0 := arr_seq) (higher_eq_priority0 := higher_eq_priority)
        (task_period0 := task_period) (task_deadline0 := task_deadline) (job_deadline0 := job_deadline)
        (job_suspension_duration0 := job_suspension_duration) (R_hp := actual_response_time);
        try (by done).
      {
        intros j_hp ARRhp OTHERhp.
        rewrite /actual_response_time.
        apply pick_min_holds; last by intros r _ RESP _.
        exists (R (job_task j_hp)); split; first by done.
        by apply RESPhp; try (by done); [by apply FROM | rewrite /other_hep_task -H_job_of_tsk].
      }
      {
        by rewrite /is_response_time_bound_of_job H_job_of_tsk; apply RESPj.
      }
    Qed.
        
  End ComparingResponseTimeBounds.

End RTAByReduction.