(** Furthermore, we assume the fully preemptive task model. *)
Require Import prosa.model.preemption.fully_preemptive.
Require Import prosa.model.task.preemption.fully_preemptive.
Require Import prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.

(** * Task's Run to Completion Threshold *)
(** In this section, we prove that instantiation of function [task run
    to completion threshold] to the fully preemptive model
    indeed defines a valid run-to-completion threshold function. *)
Section TaskRTCThresholdFullyPreemptiveModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  
  (** Next, consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Then, we prove that [task_run_to_completion_threshold] function
      defines a valid task's run to completion threshold. *)     
  Lemma fully_preemptive_valid_task_run_to_completion_threshold:
    forall tsk, valid_task_run_to_completion_threshold arr_seq tsk.
  Proof.
    intros; split.
    - by rewrite /task_rtc_bounded_by_cost.
    - intros j ARR TSK.
      apply leq_trans with (job_cost j); eauto 2 with basic_facts.
        by rewrite-TSK; apply H_valid_job_cost.
  Qed.
    
End TaskRTCThresholdFullyPreemptiveModel.
Hint Resolve fully_preemptive_valid_task_run_to_completion_threshold : basic_facts.
