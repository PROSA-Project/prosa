Require Export prosa.analysis.facts.preemption.task.floating.
Require Export prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.

(** Furthermore, we assume the task model with floating non-preemptive regions. *)
Require Import prosa.model.preemption.limited_preemptive.
Require Import prosa.model.task.preemption.floating_nonpreemptive.

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
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Then, we prove that [task_run_to_completion_threshold] function
      defines a valid task's run to completion threshold. *)   
  Lemma floating_preemptive_valid_task_run_to_completion_threshold:
    forall tsk, valid_task_run_to_completion_threshold arr_seq tsk.
  Proof.
    intros; split.
    - by rewrite /task_rtc_bounded_by_cost.
    - intros j ARR TSK.
      apply leq_trans with (job_cost j); eauto 2 with basic_facts.
        by rewrite-TSK; apply H_valid_job_cost.
  Qed.
  
End TaskRTCThresholdFloatingNonPreemptiveRegions.
Hint Resolve floating_preemptive_valid_task_run_to_completion_threshold : basic_facts.
