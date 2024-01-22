Require Export prosa.model.task.preemption.parameters.

(** * Blocking Bound for FP *)
(** In this section, we define a bound on the length of a
    non-preemptive segment of a lower-priority job (w.r.t. a task
    [tsk]) under FP scheduling. *)
Section MaxNPSegmentBlockingBound.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** Consider an FP policy. *)
  Context {FP : FP_policy Task}.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Assuming that tasks are independent, the maximum non-preemptive
      segment length w.r.t. any lower-priority task bounds the maximum
      possible duration of priority inversion. *)
  Definition blocking_bound (tsk : Task) :=
    \max_(tsk_other <- ts | ~~ hep_task tsk_other tsk)
     (task_max_nonpreemptive_segment tsk_other - ε).

End MaxNPSegmentBlockingBound.
