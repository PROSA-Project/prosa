Require Export prosa.analysis.definitions.request_bound_function.

(** * Demand Bound Function (DBF) *)
(** Here we define Baruah et al.'s classic notion of a demand bound function,
    generalized to arbitrary arrival curves. *)
Section DemandBoundFunction.
  (** Consider any type of tasks. *)
  Context {Task : TaskType}.

  (** Suppose each task is characterized by a WCET, a relative deadline, and an arrival curve. *)
  Context `{TaskCost Task} `{TaskDeadline Task} `{MaxArrivals Task}.

  (** A task's DBF is its request-bound function (RBF) shifted by [task_deadline tsk - 1] time units. *)
  Definition task_demand_bound_function (tsk : Task) (delta : duration) :=
    let delta' := delta - (task_deadline tsk - 1) in
      task_request_bound_function tsk delta'.

  (** A task set's total demand bound function is simply the sum of each task's DBF.*)
  Definition total_demand_bound_function (ts: seq Task) (delta : duration) :=
    \sum_(tsk <- ts) task_demand_bound_function tsk delta.

End DemandBoundFunction.
