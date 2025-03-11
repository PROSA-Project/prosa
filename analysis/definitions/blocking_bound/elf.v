Require Export prosa.model.task.preemption.parameters.
Require Export prosa.model.task.arrival.curves.
Require Import prosa.model.priority.elf.

(** * Blocking Bound for ELF *)
(** In this section, we define a bound on the length of a
    non-preemptive segment of a lower-priority job (w.r.t. a task
    [tsk]) under ELF scheduling. *)
Section MaxNPSegmentBlockingBound.

  (** Consider any type of tasks ... *)
  Context {Job : JobType}{Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... with relative priority points. *)
  Context `{PriorityPoint Task}.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Let [max_arrivals] be a family of arrival curves. *)
  Context `{MaxArrivals Task}.

  (** Consider any FP policy. *)
  Context {FP : FP_policy Task}.

  (** Only other tasks that potentially release non-zero-cost jobs are
      relevant, so we define a predicate to exclude pathological
      cases. *)
  Let blocking_relevant (tsk_o : Task) :=
    (max_arrivals tsk_o ε > 0) && (task_cost tsk_o > 0).

  (** Now we define a predicate to only include [blocking_relevant] tasks
      that have a lower priority than [tsk]. *)
  Let lp_tsk_blocking_relevant (tsk : Task) (tsk_o : Task) :=
    (hp_task tsk tsk_o) && (blocking_relevant tsk_o).

  (** Next we define a predicate for filtering [blocking_relevant] tasks
      that have the same priority as [tsk]. *)
  Let ep_tsk_blocking_relevant (tsk : Task) (tsk_o : Task) (A : duration) :=
    let ep_tsk_j_blocking_relevant :=  (task_priority_point tsk_o > A%:R +  task_priority_point tsk)%R in
      (ep_task tsk tsk_o) && ep_tsk_j_blocking_relevant && (blocking_relevant tsk_o).

  (** For a job of a given task [tsk], given the relative arrival offset [A]
      within its busy window, we define the following blocking
      bound. This bound assumes that task are independent (i.e., it
      does not account for possible blocking due to locking
      protocols). *)
  Definition blocking_bound (tsk : Task) (A : duration)  :=
    \max_(tsk_o <- ts | lp_tsk_blocking_relevant tsk tsk_o || ep_tsk_blocking_relevant tsk tsk_o A)
      (task_max_nonpreemptive_segment tsk_o - ε).

End MaxNPSegmentBlockingBound.
