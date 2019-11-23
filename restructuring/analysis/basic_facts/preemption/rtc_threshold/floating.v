Require Import rt.restructuring.model.preemption.limited_preemptive.
Require Import rt.restructuring.model.task.preemption.floating_nonpreemptive.
Require Export rt.restructuring.analysis.basic_facts.preemption.task.floating.
Require Export rt.restructuring.analysis.basic_facts.preemption.rtc_threshold.job_preemptable.

(** * Task's Run to Completion Threshold *)
(** In this section, we instantiate function [task run to completion
    threshold] for the model with floating non-preemptive regions. *)
Section TaskRTCThresholdFloatingNonPreemptiveRegions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.
  
  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_job_cost_le_task_cost:
    cost_of_jobs_from_arrival_sequence_le_task_cost arr_seq.

  (** Then, we prove that [task_run_to_completion_threshold] function
      defines a valid task's run to completion threshold. *)   
  Lemma floating_preemptive_valid_task_run_to_completion_threshold:
    forall tsk, valid_task_run_to_completion_threshold arr_seq tsk.
  Proof.
    intros; split.
    - by rewrite /task_run_to_completion_threshold_le_task_cost.
    - intros j ARR TSK.
      apply leq_trans with (job_cost j); eauto 2 with basic_facts.
        by rewrite-TSK; apply H_job_cost_le_task_cost.
  Qed.
  
End TaskRTCThresholdFloatingNonPreemptiveRegions.
Hint Resolve floating_preemptive_valid_task_run_to_completion_threshold : basic_facts.
