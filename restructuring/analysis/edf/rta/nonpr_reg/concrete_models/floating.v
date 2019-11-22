Require Import rt.util.all.
Require Import rt.restructuring.behavior.all.
Require Import rt.restructuring.analysis.basic_facts.all.
Require Import rt.restructuring.analysis.definitions.job_properties.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.aggregate.workload.
Require Import rt.restructuring.model.processor.ideal.
Require Import rt.restructuring.model.readiness.basic.
Require Import rt.restructuring.model.arrival.arrival_curves.
Require Import rt.restructuring.model.preemption.floating.
Require Import rt.restructuring.model.schedule.work_conserving.
Require Import rt.restructuring.model.priority.classes.
Require Import rt.restructuring.analysis.facts.edf.
Require Import rt.restructuring.model.schedule.priority_driven.
Require Import rt.restructuring.analysis.arrival.workload_bound.
Require Import rt.restructuring.analysis.arrival.rbf.
Require Import rt.restructuring.analysis.edf.rta.nonpr_reg.response_time_bound.
Require Export rt.restructuring.analysis.basic_facts.preemption.job.limited.
Require Export rt.restructuring.analysis.basic_facts.preemption.task.floating.
Require Export rt.restructuring.analysis.basic_facts.preemption.rtc_threshold.floating.

Require Export rt.restructuring.analysis.facts.priority_inversion_is_bounded.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * RTA for Model with Floating Non-Preemptive Regions *)
(** In this module we prove the RTA theorem for floating non-preemptive regions EDF model. *)
Section RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** For clarity, let's denote the relative deadline of a task as D. *)
  Let D tsk := task_deadline tsk.

  (** Consider the EDF policy that indicates a higher-or-equal priority relation. *)
  Let EDF := EDF Job.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** Assume we have the model with floating nonpreemptive regions.
      I.e., for each task only the length of the maximal nonpreemptive
      segment is known _and_ each job level is divided into a number
      of nonpreemptive segments by inserting preemption points. *)
  Context `{JobPreemptionPoints Job}
          `{TaskMaxNonpreemptiveSegment Task}.
  Hypothesis H_valid_task_model_with_floating_nonpreemptive_regions:
    valid_model_with_floating_nonpreemptive_regions arr_seq.
  
  (** Consider an arbitrary task set ts, ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from this task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and the cost of a job cannot be larger than the task cost. *)
  Hypothesis H_job_cost_le_task_cost:
    cost_of_jobs_from_arrival_sequence_le_task_cost arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
      any task tsk in ts [max_arrival tsk] is (1) an arrival bound of
      tsk, and (2) it is a monotonic function that equals 0 for the
      empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let tsk be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Next, consider any ideal uniprocessor schedule with limited
      preemptions of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_schedule_with_limited_preemptions:
    valid_schedule_with_limited_preemptions arr_seq sched.
  
  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume we have sequential tasks, i.e, jobs from the 
     same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  
  (** ... and the schedule respects the policy defined by the
      job_preemptable function (i.e., jobs have bounded nonpreemptive
      segments). *)
  Hypothesis H_respects_policy : respects_policy_at_preemption_point arr_seq sched.

  (** Let's define some local names for clarity. *)
  Let response_time_bounded_by :=
    task_response_time_bound arr_seq sched.
  Let task_rbf_changes_at A := task_rbf_changes_at tsk A.
  Let bound_on_total_hep_workload_changes_at :=
    bound_on_total_hep_workload_changes_at ts tsk.
  
  (** We introduce the abbreviation "rbf" for the task request bound function,
       which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce task_rbf as an abbreviation
      for the task request bound function of task tsk. *)
  Let task_rbf := rbf tsk.

  (** Using the sum of individual request bound functions, we define the request bound 
      function of all tasks (total request bound function). *)
  Let total_rbf := total_request_bound_function ts.
  
  (** We define a bound for the priority inversion caused by jobs with lower priority. *)
  Definition blocking_bound :=
    \max_(tsk_other <- ts | (tsk_other != tsk) && (D tsk_other > D tsk))
     (task_max_nonpreemptive_segment tsk_other - ε).
  
  (** Next, we define an upper bound on interfering workload received from jobs 
      of other tasks with higher-than-or-equal priority. *)
  Let bound_on_total_hep_workload A Δ :=
    \sum_(tsk_o <- ts | tsk_o != tsk)
     rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).
  
  (** Let L be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_rbf L.

  (** To reduce the time complexity of the analysis, recall the notion of search space. *)
  Let is_in_search_space (A : duration) :=
    (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A).
  
  (** Consider any value R, and assume that for any given arrival offset A in the search space,
      there is a solution of the response-time bound recurrence which is bounded by R. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum:
    forall (A : duration),
      is_in_search_space A -> 
      exists (F : duration),
        A + F = blocking_bound + task_rbf (A + ε) + bound_on_total_hep_workload A (A + F) /\
        F <= R.

  (** Now, we can leverage the results for the abstract model with
      bounded nonpreemptive segments to establish a response-time
      bound for the more concrete model with floating nonpreemptive
      regions.  *)
  Theorem uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions:
    response_time_bounded_by tsk R.  
  Proof.
    move: (H_valid_task_model_with_floating_nonpreemptive_regions) => [LIMJ JMLETM].
    move: (LIMJ) => [BEG [END _]].
    eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments with (L0 := L).
    all: eauto 2 with basic_facts.
    { rewrite subnn.
      intros A SP.
      apply H_R_is_maximum in SP.
      move: SP => [F [EQ LE]].
      exists F.
        by rewrite subn0 addn0; split.
    }
  Qed.

End RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves.