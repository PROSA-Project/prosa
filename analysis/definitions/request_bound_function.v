Require Export prosa.model.task.arrival.curves.
Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.util.sum.

(** * Request Bound Function (RBF) *)

(** We define the notion of a task's request-bound function (RBF), as well as
    the total request bound function of a set of tasks. *)

Section TaskWorkloadBoundedByArrivalCurves.

  (** Consider any type of task characterized by a WCET bound and an arrival curve. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task} `{MaxArrivals Task}.

  (** ** RBF of a Single Task *)

  (** We define the classic notion of an RBF, which for a given task [tsk]
      and interval length [Δ], bounds the maximum cumulative processor demand
      of all jobs released by [tsk] in any interval of length [Δ]. *)
  Definition task_request_bound_function (tsk : Task) (Δ : duration) :=
    task_cost tsk * max_arrivals tsk Δ.

  (** ** Total RBF of Multiple Tasks *)

  (** Next, we extend the notion of an RBF to multiple tasks in the obvious way. *)

  (** Consider a set of tasks [ts]. *)
  Variable ts : seq Task.

  (** The joint total RBF of all tasks in [ts] is simply the sum of each task's RBF. *)
  Definition total_request_bound_function (Δ : duration) :=
    \sum_(tsk <- ts) task_request_bound_function tsk Δ.

  (** For convenience, we additionally introduce specialized notions of total RBF for use
      under FP scheduling that consider only certain tasks.
      relation. *)
  Context `{FP_policy Task}.

  (** We define the following bound for the total workload of
      tasks of higher-or-equal priority (with respect to [tsk]) in any interval
      of length Δ. *)
  Definition total_hep_request_bound_function_FP (tsk : Task) (Δ : duration) :=
    \sum_(tsk_other <- ts | hep_task tsk_other tsk)
     task_request_bound_function tsk_other Δ.

  (** We also define a bound for the total workload of higher-or-equal-priority
      tasks other than [tsk] in any interval of length [Δ]. *)
  Definition total_ohep_request_bound_function_FP (tsk : Task) (Δ : duration) :=
    \sum_(tsk_other <- ts | hep_task tsk_other tsk && (tsk_other != tsk))
      task_request_bound_function tsk_other Δ.

  (** We also define a bound for the total workload of higher-or-equal-priority
      tasks other than [tsk] in any interval of length [Δ]. *)
  Definition total_ep_request_bound_function_FP (tsk : Task) (Δ : duration) :=
    \sum_(tsk_other <- ts | ep_task tsk_other tsk)
      task_request_bound_function tsk_other Δ.

  (** Finally, we define a bound for the total workload of higher-priority
      tasks in any interval of length [Δ]. *)
  Definition total_hp_request_bound_function_FP (tsk : Task) (Δ : duration) :=
    \sum_(tsk_other <- ts | hp_task tsk_other tsk)
     task_request_bound_function tsk_other Δ.

End TaskWorkloadBoundedByArrivalCurves.
