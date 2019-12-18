Require Export prosa.model.task.preemption.parameters.

(** * Fully Preemptive Task Model *)

(** In this module, we instantiate the common task model in which all jobs are
    always preemptable. *)

Section FullyPreemptiveModel.

  (** Consider any type of jobs. *)
  Context {Task : JobType}.

  (** In the fully preemptive model, any job can be preempted at any
      time. Thus, the maximal non-preemptive segment has length at most ε
      (i.e., one time unit such as a processor cycle). *)
  Global Program Instance fully_preemptive_model : TaskMaxNonpreemptiveSegment Task :=
    {
      task_max_nonpreemptive_segment (tsk : Task) := ε
    }.

End FullyPreemptiveModel.

(** ** Run-to-Completion Threshold *)

(** Since jobs are always preemptive, there is no offset after which a job is
    guaranteed to run to completion. *)

Section TaskRTCThresholdFullyPreemptiveModel.

  (** Consider any type of tasks with WCETs. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In the fully preemptive model, any job can be preempted at any
      time. Thus, the only safe run-to-completion threshold for a task is its WCET. *)
  Global Program Instance fully_preemptive : TaskRunToCompletionThreshold Task :=
    {
      task_run_to_completion_threshold (tsk : Task) := task_cost tsk
    }.

End TaskRTCThresholdFullyPreemptiveModel.
