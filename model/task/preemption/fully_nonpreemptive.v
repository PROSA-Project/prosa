Require Export prosa.model.task.preemption.parameters.

(** * Fully Non-Preemptive Task Model *)

(** In this module, we instantiate the task model in which jobs cannot be
    preempted once they have commenced execution. *)
Section FullyNonPreemptiveModel.

  (** Consider any type of tasks with WCET bounds. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In the fully non-preemptive model, no job can be preempted until its
      completion. The maximal non-preemptive segment of a job [j] has length
      [job_cost j], which is bounded by [task_cost tsk].*)
  Global Program Instance fully_nonpreemptive_model : TaskMaxNonpreemptiveSegment Task :=
    {
      task_max_nonpreemptive_segment (tsk : Task) := task_cost tsk
    }.

End FullyNonPreemptiveModel.

(** ** Run-to-Completion Threshold *)

(** In this section, we instantiate the task-level run-to-completion threshold
    for the fully non-preemptive model. *)
Section TaskRTCThresholdFullyNonPreemptive.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.

  (** In the fully non-preemptive model, no job can be preempted prior to its
      completion. In other words, once a job starts running, it is guaranteed
      to finish. Thus, we can set the task-level run-to-completion threshold
      to ε. *)
  Global Program Instance fully_nonpreemptive : TaskRunToCompletionThreshold Task :=
    {
      task_run_to_completion_threshold (tsk : Task) := ε
    }.

End TaskRTCThresholdFullyNonPreemptive.
