Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.susp.schedule prosa.classic.model.schedule.uni.susp.platform
               prosa.classic.model.schedule.uni.susp.valid_schedule.
Require Import prosa.classic.model.schedule.uni.jitter.valid_schedule.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.rta_by_reduction
               prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_taskset_generation
               prosa.classic.analysis.uni.susp.dynamic.jitter.taskset_membership.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file we use the reduction to jitter-aware schedule to analyze
   individual tasks using RTA. *)
Module TaskSetRTA.

  Import SporadicTaskset Suspension Priority ValidSuspensionAwareSchedule
         ScheduleWithSuspensions ResponseTime PlatformWithSuspensions
         TaskArrival ValidJitterAwareSchedule RTAByReduction TaskSetMembership.

  Module ts_gen := JitterTaskSetGeneration.
  Module job_susp := Job.
  Module job_jitter := JobWithJitter.

  (* In this section, we are going to assume we have obtained response-time
     bounds for high-priority tasks and then use the reduction to infer a
     response-time bound for a particular task. *)
  Section PerTaskAnalysis.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (** Basic Setup & Setting*)
    
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

    (* ...and in which all jobs come from the task set. *)
    Hypothesis H_jobs_come_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Assume that job deadlines equal task deadlines. *)
    Hypothesis H_job_deadline_eq_task_deadline:
      forall j, arrives_in arr_seq j -> job_deadline j = task_deadline (job_task j).

    (* Consider any job suspension times and task suspension bound. *)
    Variable job_suspension_duration: job_suspension Job.
    Variable task_suspension_bound: Task -> time.

    (* Assume any FP policy that is reflexive, transitive and total. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: FP_is_total_over_task_set higher_eq_priority ts.
    Let job_higher_eq_priority := FP_to_JLDP job_task higher_eq_priority.

    (* Recall the definition of a valid suspension-aware and jitter-aware schedules. *)
    Let is_valid_suspension_aware_schedule :=
      valid_suspension_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                      job_suspension_duration.
    Let is_valid_jitter_aware_schedule :=
      valid_jitter_aware_schedule job_arrival arr_seq job_higher_eq_priority.

    (* Also recall the definition of task response-time bound for given job cost and schedule. *)
    Let is_task_response_time_bound_with job_cost sched :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.

    (** Analysis Setup *)
    
    (* Let tsk_i be any task to be analyzed. *)
    Variable tsk_i: Task.
    Hypothesis H_tsk_in_ts: tsk_i \in ts.

    (* Recall the definition of higher-or-equal-priority tasks (other than tsk_i). *)
    Let other_hep_task tsk_other := higher_eq_priority tsk_other tsk_i && (tsk_other != tsk_i).

    (* Next, assume that for each of those higher-or-equal-priority tasks (other than tsk_i),
       we know a response-time bound R that is valid across all suspension-aware schedules of ts. *)
    Variable R: Task -> time.   
    Hypothesis H_valid_response_time_bound_of_hp_tasks_in_all_schedules:
      forall job_cost sched,
        is_valid_suspension_aware_schedule job_cost sched ->
        forall tsk_hp,
          tsk_hp \in ts ->
          other_hep_task tsk_hp ->
          is_task_response_time_bound_with job_cost sched tsk_hp (R tsk_hp).

    (* Since this analysis is for constrained deadlines, also assume that
       (R tsk_i) is no larger than the deadline of tsk_i. *)
    Hypothesis H_R_le_deadline: R tsk_i <= task_deadline tsk_i.
      
    (** Recall: Properties of Valid Jitter-Aware Jobs *)

    (* Recall that a valid jitter-aware schedule must have positive job costs,... *)
    Let job_cost_positive job_cost :=
      forall j, arrives_in arr_seq j -> job_cost j > 0.

    (* ...job costs that are no larger than the task costs... *)
    Let job_cost_le_task_cost job_cost task_cost :=
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).

    (* ...and job jitter no larger than the task jitter. *)
    Let job_jitter_le_task_jitter job_jitter task_jitter :=
      forall j,
        arrives_in arr_seq j ->
        job_jitter j <= task_jitter (job_task j).

    (* This is summarized in the following predicate. *)
    Definition valid_jobs_with_jitter job_cost job_jitter task_cost task_jitter :=
      job_cost_positive job_cost /\
      job_cost_le_task_cost job_cost task_cost /\
      job_jitter_le_task_jitter job_jitter task_jitter.

    (** Conclusion: Response-time Bound for Task tsk_i *)

    (* Recall the parameters of the generated jitter-aware task set. *)
    Let inflated_task_cost := ts_gen.inflated_task_cost task_cost task_suspension_bound tsk_i.
    Let task_jitter := ts_gen.task_jitter task_cost higher_eq_priority tsk_i R.

    (* By using a jitter-aware RTA, assume that we proved that (R tsk_i) is a valid
       response-time bound for task tsk_i in any jitter-aware schedule of the same
       arrival sequence. *)
    Hypothesis H_valid_response_time_bound_of_tsk_i:
      forall job_cost job_jitter sched,
        valid_jobs_with_jitter job_cost job_jitter inflated_task_cost task_jitter ->
        is_valid_jitter_aware_schedule job_cost job_jitter sched ->
        is_task_response_time_bound_with job_cost sched tsk_i (R tsk_i).
    
    (* Next, consider any job cost function... *)
    Variable job_cost: Job -> time.

    (* ...and let sched_susp be any valid suspension-aware schedule with those job costs. *)
    Variable sched_susp: schedule Job.
    Hypothesis H_valid_schedule: is_valid_suspension_aware_schedule job_cost sched_susp.

    (* Assume that the job costs are positive... *)
    Hypothesis H_job_cost_positive:
      forall j, arrives_in arr_seq j -> job_cost j > 0.

    (* ...and no larger than the task costs. *)
    Hypothesis H_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).

    (* Also assume that job suspension times are bounded by the task suspension bounds. *)
    Hypothesis H_dynamic_suspensions:
      dynamic_suspension_model job_cost job_task job_suspension_duration task_suspension_bound.

    (* Using the reduction to a jitter-aware schedule, we conclude that (R tsk_i) must
       also be a response-time bound for task tsk_i in the suspension-aware schedule. *)
    Theorem valid_response_time_bound_of_tsk_i:
      is_task_response_time_bound_with job_cost sched_susp tsk_i (R tsk_i).
    Proof.
      unfold is_task_response_time_bound_with,
             is_response_time_bound_of_task, is_response_time_bound_of_job in *.
      rename H_valid_response_time_bound_of_hp_tasks_in_all_schedules into RESPhp,
             H_valid_response_time_bound_of_tsk_i into RESPi.

      move: (H_valid_schedule) => [_ [_ [COMP _]]].
      intros j ARRj JOBtsk.
       
      (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
      remember (job_arrival j + R tsk_i) as ctime.
      
      (* Now, we apply strong induction on the absolute response-time bound. *)
      generalize dependent j.
      induction ctime as [ctime IH] using strong_ind.

      intros j ARRj JOBtsk EQc; subst ctime.

      (* First, let's simplify the induction hypothesis. *)
      have BEFOREok:
         forall j0,
           arrives_in arr_seq j0 ->
           job_task j0 = tsk_i ->
           job_arrival j0 < job_arrival j ->
           completed_by job_cost sched_susp j0 (job_arrival j0 + R tsk_i);
        [by ins; apply IH; try (by done); rewrite ltn_add2r | clear IH].
      set actual_response_time :=
        actual_response_time job_arrival job_task job_cost sched_susp R.
      set inflated_job_cost :=
          reduction.inflated_job_cost job_cost job_suspension_duration. 
      set job_jitter := reduction.job_jitter job_arrival job_task
                        higher_eq_priority job_cost j actual_response_time.
      apply valid_response_time_bound_in_sched_susp with
        (task_period0 := task_period) (task_deadline0 := task_deadline)
        (job_deadline0 := job_deadline) (job_task0 := job_task) (ts0 := ts)
        (arr_seq0 := arr_seq) (higher_eq_priority0 := higher_eq_priority)
        (job_suspension_duration0:=job_suspension_duration); try (by done).
      - by intros tsk_hp IN OHEP j'; apply RESPhp.
      {   
        intros j0 ARR0 LT0 JOB0.
        apply completion_monotonic with (t := job_arrival j0 + R tsk_i);
          [ | by apply BEFOREok; rewrite // -JOBtsk].
        by rewrite leq_add2l H_job_deadline_eq_task_deadline // JOB0 JOBtsk.
      }  
      {
        apply RESPi with (job_jitter := job_jitter); try (by done);
          last by eapply reduction_prop.sched_jitter_is_valid; eauto 1.       
        repeat split; intros j' ARR.
        - by eapply ts_membership_inflated_job_cost_positive; eauto 1.  
        - by eapply ts_membership_inflated_job_cost_le_inflated_task_cost;
            eauto 1.
        - by eapply ts_membership_job_jitter_le_task_jitter; eauto 1.
      }
    Qed.
    
  End PerTaskAnalysis.

End TaskSetRTA.