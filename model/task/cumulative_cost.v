Require Export prosa.model.task.arrivals.

(** * WCET(n): Cumulative Task Costs *)

(** In this module, we introduce a task parameter for cumulative execution-time
    bounds, which is commonly referred to as WCET(n). Whereas [task_cost tsk]
    bounds the cost of any one job of task [tsk], [task_cumulative_cost tsk n]
    bounds the total cost of any [n] _consecutive_ jobs of [tsk]. *)

(** We first define a task-model parameter that expresses each task's
    cumulative worst-case execution-time bound WCET(n). *)
Class TaskCumulativeCost (Task : TaskType) :=
  {
    task_cumulative_cost : Task -> nat -> work
  }.

(** A cumulative cost parameter also induces the ordinary scalar WCET parameter
    by considering exactly one job, i.e., WCET(1). We make this conversion a
    local instance so that it needs explicit opt-in, as it is a rather rare
    case. *)
#[local,program] Instance task_cost_from_cumulative_cost
  {Task : TaskType} `{TaskCumulativeCost Task} : TaskCost Task :=
  {
    task_cost tsk := task_cumulative_cost tsk 1
  }.

(** Conversely, a legacy scalar WCET parameter induces a default cumulative
    bound by multiplying the scalar WCET by the number of arrivals. This is a
    compatibility fallback for contexts that provide only a scalar WCET and
    hence is made globally visible. *)
#[global,program] Instance task_cost_as_cumulative_cost
  {Task : TaskType} `{TaskCost Task} : TaskCumulativeCost Task :=
  {
    task_cumulative_cost tsk n := n * task_cost tsk
  }.

(** In the following section, we define basic validity conditions for
    cumulative task costs. *)
Section ValidTaskCumulativeCost.

  (** Consider any type of tasks with cumulative cost bounds. *)
  Context {Task : TaskType} `{TaskCumulativeCost Task}.

  (** A cumulative cost bound is well-formed if it maps zero arrivals to zero
      cost and is monotonic in the number of arrivals. *)
  Definition valid_task_cumulative_cost (tsk : Task) :=
    task_cumulative_cost tsk 0 = 0
    /\ monotone leq (task_cumulative_cost tsk).

  (** We lift the constraint to task sets. *)
  Definition taskset_has_valid_cumulative_cost_bounds (ts : TaskSet Task) :=
    forall tsk,
      tsk \in ts ->
      valid_task_cumulative_cost tsk.

End ValidTaskCumulativeCost.

(** Next, we define what it means for an arrival sequence to respect a
    cumulative cost bound. *)
Section RespectsTaskCumulativeCost.

  (** Consider any type of tasks with cumulative cost bounds ... *)
  Context {Task : TaskType} `{TaskCumulativeCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** Consider a given arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** A sequence of jobs [js] is a consecutive block of arrivals of task [tsk]
      if it occurs contiguously in the list of task arrivals up to some time. *)
  Definition consecutive_task_arrivals (tsk : Task) (js : seq Job) :=
    exists t prefix suffix,
      task_arrivals_up_to arr_seq tsk t = prefix ++ js ++ suffix.

  (** The arrival sequence respects the cumulative cost bound of task [tsk] if
      every consecutive block of jobs of [tsk] is bounded by
      [task_cumulative_cost tsk]. *)
  Definition respects_task_cumulative_cost (tsk : Task) :=
    forall js,
      consecutive_task_arrivals tsk js ->
      \sum_(j <- js) job_cost j <= task_cumulative_cost tsk (size js).

  (** Finally, we lift the validity constraint to task sets. *)
  Definition taskset_respects_cumulative_cost_bounds (ts : TaskSet Task) :=
    forall tsk,
      tsk \in ts ->
      respects_task_cumulative_cost tsk.

End RespectsTaskCumulativeCost.
