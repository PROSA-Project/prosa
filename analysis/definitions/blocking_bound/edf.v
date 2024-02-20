Require Export prosa.model.task.preemption.parameters.
Require Export prosa.model.task.arrival.curves.

(** * Blocking Bound for EDF *)
(** In this section, we define a bound on the length of a
    non-preemptive segment of a lower-priority job (w.r.t. a task
    [tsk]) under EDF scheduling. *)
Section MaxNPSegmentBlockingBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** For clarity, let's denote the relative deadline of a task as [D]. *)
  Let D tsk := task_deadline tsk.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Let [max_arrivals] be a family of arrival curves. *)
  Context `{MaxArrivals Task}.

  (** Only other tasks that potentially release non-zero-cost jobs are
      relevant, so we define a predicate to exclude pathological
      cases. *)
  Definition blocking_relevant (tsk_o : Task) :=
    (max_arrivals tsk_o ε > 0) && (task_cost tsk_o > 0).

  (** For a job of a given task [tsk], the relative arrival offset [A]
      within its busy window, we define the following blocking
      bound. This bound assumes that task are independent (i.e., it
      does not account for possible blocking due to locking
      protocols). *)
  Definition blocking_bound (tsk : Task) (A : duration)  :=
    \max_(tsk_o <- ts | blocking_relevant tsk_o && (D tsk_o > D tsk + A))
     (task_max_nonpreemptive_segment tsk_o - ε).

End MaxNPSegmentBlockingBound.
