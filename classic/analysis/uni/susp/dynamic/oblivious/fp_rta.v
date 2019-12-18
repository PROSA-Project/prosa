Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.priority prosa.classic.model.suspension prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedule prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.analysis.uni.basic.fp_rta_comp.
Require Import prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module SuspensionObliviousFP.

  Import Job TaskArrival SporadicTaskset Suspension Priority Schedulability
         PlatformWithSuspensions SuspensionIntervals.
  Export ResponseTimeIterationFP ReductionToBasicSchedule.

  (* In this section, we formalize the suspension-oblivious RTA
     for fixed-priority tasks under the dynamic self-suspension model.
     This is just a straightforward application of the reduction
     in analysis/uni/susp/dynamic/oblivious/reduction.v with the basic
     response-time analysis for uniprocessor FP scheduling. *)
  Section ReductionToBasicAnalysis.

    Context {SporadicTask: eqType}.
    Variable task_cost: SporadicTask -> time.
    Variable task_period: SporadicTask -> time.
    Variable task_deadline: SporadicTask -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> SporadicTask.

    (* Let ts be any task set to be analyzed... *)
    Variable ts: taskset_of SporadicTask.
    
    (* ...such that tasks have valid parameters. *)
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    
    (* Next, consider any job arrival sequence with consistent, duplicate-free arrivals,... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.    
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* ...in which all jobs come from task set ts, ... *)
    Hypothesis H_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* ...have valid parameters,...*)
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* ... and satisfy the sporadic task model. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq. 
    
    (* Consider any FP policy that is reflexive, transitive and total, indicating
       "higher or equal task priority". *)
    Variable higher_eq_priority: FP_policy SporadicTask.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: FP_is_total_over_task_set higher_eq_priority ts.
      
    (* Assume that the total suspension time of any job is bounded according
       to the dynamic suspension model. *)
    Variable next_suspension: job_suspension Job.
    Variable task_suspension_bound: SporadicTask -> time.
    Hypothesis H_dynamic_suspensions:
      dynamic_suspension_model job_cost job_task next_suspension task_suspension_bound.

    (* As part of the analysis, we are going to use task costs inflated with suspension bounds, ... *)
    Let inflated_cost := inflated_task_cost task_cost task_suspension_bound.

    (* ...with the condition that they are no larger than the deadline nor the period of each task. *)
    Hypothesis H_inflated_cost_le_deadline_and_period:
      forall tsk,
        tsk \in ts ->
          inflated_cost tsk <= task_deadline tsk /\
          inflated_cost tsk <= task_period tsk.
      
    (* Now we proceed with the schedulability analysis. *)
    Section MainProof.

      (* Consider any suspension-aware schedule of the arrival sequence... *)
      Variable sched: schedule Job.
      Hypothesis H_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched arr_seq.

      (* ...where jobs only execute after they arrive... *)
      Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.

      (* ...and no longer than their execution costs. *)
      Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

      (* Also assume that the schedule is work-conserving when there are non-suspended jobs, ... *)
      Hypothesis H_work_conserving: work_conserving job_arrival job_cost next_suspension arr_seq sched.

      (* ...that the schedule respects job priority... *)
      Hypothesis H_respects_priority:
        respects_FP_policy job_arrival job_cost job_task next_suspension arr_seq
                           sched higher_eq_priority.

      (* ...and that suspended jobs are not allowed to be scheduled. *)
      Hypothesis H_respects_self_suspensions:
        respects_self_suspensions job_arrival job_cost next_suspension sched.

      (* For simplicity, let's also define some local names. *)
      Let task_is_schedulable :=
        task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.
      
      (* Next, recall the response-time analysis for FP scheduling instantiated with
         the inflated task costs. *)
      Let claimed_to_be_schedulable :=
        fp_schedulable inflated_cost task_period task_deadline higher_eq_priority.

      (* Then, we prove that if this suspension-oblivious response-time analysis suceeds... *)
      Hypothesis H_claimed_schedulable_by_suspension_oblivious_RTA:
        claimed_to_be_schedulable ts.

      (* ...then no task misses its deadline in the suspension-aware schedule.
         The proof is a straightforward application of the following lemma from
         reduction.v: suspension_oblivious_preserves_schedulability. *)
      Theorem suspension_oblivious_fp_rta_implies_schedulability:
        forall tsk,
          tsk \in ts ->
          task_is_schedulable tsk.
      Proof.
        rename H_claimed_schedulable_by_suspension_oblivious_RTA into SCHED,
               H_jobs_from_taskset into FROMTS, H_inflated_cost_le_deadline_and_period into LEdl.
        intros tsk INts j ARRj JOBtsk.
        apply suspension_oblivious_preserves_schedulability with
              (higher_eq_priority0 := (FP_to_JLDP job_task higher_eq_priority))
              (arr_seq0 := arr_seq) (next_suspension0 := next_suspension); try (by done).
        - by intros t y x z; apply H_priority_is_transitive.
        - by intros j1 j2 t ARR1 ARR2; apply/orP; apply H_priority_is_total; apply FROMTS.
        apply jobs_schedulable_by_fp_rta with (task_cost0 := inflated_cost) (ts0 := ts)
            (task_period0 := task_period) (task_deadline0 := task_deadline) (job_task0 := job_task)
            (higher_eq_priority0 := higher_eq_priority); try (by done).
        - by apply suspension_oblivious_task_parameters_remain_valid.
        - by apply suspension_oblivious_job_parameters_remain_valid with (ts0 := ts)
                                                       (task_period0 := task_period).
        - by apply sched_newjobs_come_from_arrival_sequence.
        - by apply sched_new_jobs_must_arrive_to_execute. 
        - by apply sched_new_completed_jobs_dont_execute.
        - by apply sched_new_work_conserving.
        {
          intros j_low j_hp t; apply sched_new_respects_policy; try (by done).
          - by intros t' j1 j2 j3; apply H_priority_is_transitive.
          - by intros j1 j2 t' ARR1 ARR2; apply/orP; apply H_priority_is_total; apply FROMTS.
        }
      Qed.

    End MainProof.

  End ReductionToBasicAnalysis.

End SuspensionObliviousFP.