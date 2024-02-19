Require Export prosa.analysis.definitions.request_bound_function.

(** * Bound on Higher-or-Equal Priority Workload under EDF Scheduling  *)

(** In this file, we define an upper bound on workload incurred by a
    job from jobs with higher-or-equal priority that come from other
    tasks under EDF scheduling. *)
Section EDFWorkloadBound.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], and an arrival curve [max_arrivals]. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{MaxArrivals Task}.

  (** Consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and a task [tsk]. *)
  Variable tsk : Task.

  (** For brevity, let's denote the relative deadline of a task as [D] ... *)
  Let D tsk := task_deadline tsk.

  (** ... and let's use the abbreviation [rbf] for the task
      request-bound function. *)
  Let rbf := task_request_bound_function.

  (** Finally, we define an upper bound on workload received from jobs
      with higher-than-or-equal priority that come from other
      tasks. *)
  Definition bound_on_athep_workload A Δ :=
    \sum_(tsk_o <- ts | tsk_o != tsk)
     rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

End EDFWorkloadBound.
