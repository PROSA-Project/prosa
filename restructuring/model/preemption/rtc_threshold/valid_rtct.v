Require Import rt.util.all.
Require Import rt.util.nondecreasing.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.preemption.valid_model.
Require Import rt.restructuring.model.preemption.job.parameters.
Require Import rt.restructuring.model.preemption.task.parameters.

(** * Task's Run-to-Completion Threshold *)
(** Since a task model may not provide exact information about
     preemption point of a task, task's run-to-completion threshold
     cannot be defined in terms of preemption points of a task (unlike
     job's run-to-completion threshold). Therefore, we can assume the
     existence of a function that maps a task to its run-to-completion
     threshold. In this section we define the notion of a valid
     run-to-completion threshold of a task. *)
Section ValidTaskRunToCompletionThreshold.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** In addition, we assume existence of a function
     maping jobs to theirs preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ...and a function mapping tasks to theirs
     run-to-completion threshold. *)
  Context `{TaskRunToCompletionThreshold Task}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched: schedule PState. 

  (** A task's run-to-completion threshold should be at most the cost of the task. *)
  Definition task_run_to_completion_threshold_le_task_cost tsk :=
    task_run_to_completion_threshold tsk <= task_cost tsk.
  
  (** We say that the run-to-completion threshold of a task tsk bounds
      the job run-to-completionthreshold iff for any job j of task tsk
      the job run-to-completion threshold is less than or equal to the
      task run-to-completion threshold. *) 
  Definition task_run_to_completion_threshold_bounds_job_run_to_completion_threshold tsk :=
    forall j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_run_to_completion_threshold j <= task_run_to_completion_threshold tsk.

  (** We say that task_run_to_completion_threshold is a valid task
      run-to-completion threshold for a task tsk iff
      [task_run_to_completion_threshold tsk] is (1) no bigger than
      tsk's cost, (2) for any job of task tsk
      job_run_to_completion_threshold is bounded by
      task_run_to_completion_threshold. *)
  Definition valid_task_run_to_completion_threshold tsk :=
    task_run_to_completion_threshold_le_task_cost tsk /\
    task_run_to_completion_threshold_bounds_job_run_to_completion_threshold tsk.

End ValidTaskRunToCompletionThreshold.