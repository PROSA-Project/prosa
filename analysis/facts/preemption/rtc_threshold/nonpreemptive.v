Require Export prosa.analysis.facts.preemption.job.nonpreemptive.

(** Furthermore, we assume the fully non-preemptive task model. *)
Require Import prosa.model.preemption.fully_nonpreemptive.
Require Import prosa.model.task.preemption.fully_nonpreemptive.
 
(** * Task's Run to Completion Threshold *)
(** In this section, we prove that instantiation of function [task run
    to completion threshold] to the fully non-preemptive model
    indeed defines a valid run-to-completion threshold function. *)
Section TaskRTCThresholdFullyNonPreemptive.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}. 
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any ideal non-preemptive uniprocessor schedule of
      this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule  sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** First we prove that if the cost of a job j is equal to 0, then 
      [job_run_to_completion_threshold j = 0] ...  *)
  Fact job_rtc_threshold_is_0:
    forall j,
      job_cost j = 0 -> 
      job_run_to_completion_threshold j = 0.
  Proof.
    intros.
    apply/eqP; rewrite eqn_leq; apply/andP; split; last by done.
    unfold job_run_to_completion_threshold.
      by rewrite H3; compute.
  Qed.
  
  (** ... and ε otherwise. *)
  Fact job_rtc_threshold_is_ε:
    forall j,
      job_cost j > 0 ->
      arrives_in arr_seq j ->
      job_run_to_completion_threshold j = ε.
  Proof.
    intros ? ARRj POSj; unfold ε in *.
    unfold job_run_to_completion_threshold.
    rewrite job_last_nps_is_job_cost.
      by rewrite subKn.
  Qed.
  
  (** Consider a task with a positive cost. *)
  Variable tsk : Task.
  Hypothesis H_positive_cost : 0 < task_cost tsk.
                
  (** Then, we prove that [task_run_to_completion_threshold] function
      defines a valid task's run to completion threshold. *)     
  Lemma fully_nonpreemptive_valid_task_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.
  Proof.
    intros; split.
    - by unfold task_rtc_bounded_by_cost.
    - intros j ARR TSK.
      rewrite -TSK /task_run_to_completion_threshold /fully_nonpreemptive.
      edestruct (posnP (job_cost j)) as [ZERO|POS].
      + by rewrite job_rtc_threshold_is_0.
      + by erewrite job_rtc_threshold_is_ε; eauto 2. 
  Qed.
    
End TaskRTCThresholdFullyNonPreemptive.
Hint Resolve fully_nonpreemptive_valid_task_run_to_completion_threshold : basic_facts.
