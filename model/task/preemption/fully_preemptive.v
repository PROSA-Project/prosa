Require Export prosa.model.task.preemption.parameters.

(** * Fully Preemptive Task Model *)

(** In this module, we instantiate the common task model in which all jobs are
    always preemptable. *)

Section FullyPreemptiveModel.

  (** Consider any type of jobs. *)
  Context {Task : TaskType}.

  (** In the fully preemptive model, any job can be preempted at any
      time. Thus, the maximal non-preemptive segment has length at most ε
      (i.e., one time unit such as a processor cycle). *)
  Definition fully_preemptive_task_model : TaskMaxNonpreemptiveSegment Task :=
    fun tsk : Task => ε.

End FullyPreemptiveModel.

(** ** Run-to-Completion Threshold *)

(** Since jobs are always preemptive, there is no offset after which a job is
    guaranteed to run to completion. *)

Section TaskRTCThresholdFullyPreemptiveModel.

  (** Consider any type of tasks with WCETs. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In the fully preemptive model, any job can be preempted at any
      time. Thus, the only safe run-to-completion threshold for a task
      is its WCET. *)
  Definition fully_preemptive_rtc_threshold : TaskRunToCompletionThreshold Task :=
    fun tsk : Task => task_cost tsk.

End TaskRTCThresholdFullyPreemptiveModel.
