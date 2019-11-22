Require Export rt.util.all.
Require Export rt.restructuring.model.preemption.job.parameters.
Require Export rt.restructuring.model.task.concept.
(** * Static information about preemption points *)

(** Definition of a generic type of parameter relating a task 
    to the length of the maximum nonpreeptive segment. *)
Class TaskMaxNonpreemptiveSegment (Task : TaskType) :=
  task_max_nonpreemptive_segment : Task -> work.

(** Definition of a generic type of parameter relating a task
    to its run-to-completion threshold. *)
Class TaskRunToCompletionThreshold (Task : TaskType) :=
  task_run_to_completion_threshold : Task -> work.

(** Definition of a generic type of parameter relating task
    to the sequence of its preemption points. *)
Class TaskPreemptionPoints (Task : TaskType) :=
  task_preemption_points : Task -> seq work.

(** We provide a conversion from task preemption points to task max non-preemptive segment. *)
Instance TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
         (Task : TaskType) `{TaskPreemptionPoints Task} : TaskMaxNonpreemptiveSegment Task :=
  fun tsk => max0 (distances (task_preemption_points tsk)).

(** * Derived Parameters *) 
(** * Task Maximum and Last Non-preemptive Segment *)
(** In this section we define the notions of the maximal and 
    the last non-preemptive segments of a task. *)
Section MaxAndLastNonpreemptiveSegment.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In addition, assume the existence of a function that
      maps a job to the sequence of its preemption points. *)
  Context `{TaskPreemptionPoints Task}.

  (** Next, we define a function [task_max_nonpr_segment] that
      maps a task to the length of the longest nonpreemptive segment
      of this task. *)
  Definition task_max_nonpr_segment (tsk : Task) :=
    max0 (distances (task_preemption_points tsk)).

  (** Similarly, [task_last_nonpr_segment] is a function that
      maps a job to the length of the last nonpreemptive segment. *)
  Definition task_last_nonpr_segment (tsk : Task) :=
    last0 (distances (task_preemption_points tsk)).
    
End MaxAndLastNonpreemptiveSegment.


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
