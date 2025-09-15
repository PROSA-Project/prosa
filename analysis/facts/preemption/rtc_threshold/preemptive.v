Require Export prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.
Require Export prosa.model.preemption.fully_preemptive.
Require Export prosa.model.task.preemption.fully_preemptive.

(** * Task's Run to Completion Threshold *)

(** In this section, we prove that the instantiation of the task
    run-to-completion threshold for the fully preemptive model is valid. *)
Section TaskRTCThresholdFullyPreemptiveModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Assume that jobs and tasks are fully preemptive. *)
  #[local] Existing Instance fully_preemptive_job_model.
  #[local] Existing Instance fully_preemptive_task_model.
  #[local] Existing Instance fully_preemptive_rtc_threshold.  

  (** Next, consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Then, we prove that [task_rtct] function
      defines a valid task's run to completion threshold. *)     
  Lemma fully_preemptive_valid_task_run_to_completion_threshold :
    forall tsk, valid_task_run_to_completion_threshold arr_seq tsk.
  Proof.
    intros; split.
    - by rewrite /task_rtc_bounded_by_cost.
    - intros j ARR TSK.
      apply leq_trans with (job_cost j) => //.
      by move: TSK => /eqP <-; apply H_valid_job_cost.
  Qed.
    
End TaskRTCThresholdFullyPreemptiveModel.
Global Hint Resolve fully_preemptive_valid_task_run_to_completion_threshold : basic_rt_facts.
