Require Export prosa.util.rel.
Require Export prosa.model.task.arrivals.

(** * Request Bound Functions (RBF) *)

(** In the following, we define the notion of Request Bound Functions
    (RBF), which can be used to reason about the job cost arrivals. In
    contrast to arrival curves which constrain the number of arrivals
    per time interval, request bound functions bound the sum of costs
    of arriving jobs. *)

(** ** Task Parameters for the Request Bound Functions *)

(** The request bound functions give an upper bound and, optionally, a
    lower bound on the cost of new job arrivals during any given
    interval. *)

(** We let [max_request_bound tsk Δ] denote a bound on the maximum
    cost of arrivals of jobs of task [tsk] in any interval of length
    [Δ]. *)
Class MaxRequestBound (Task : TaskType) := max_request_bound : Task -> duration -> work.

(** Conversely, we let [min_request_bound tsk Δ] denote a bound on the
    minimum cost of arrivals of jobs of task [tsk] in any interval of
    length [Δ]. *)
Class MinRequestBound (Task : TaskType) := min_request_bound : Task -> duration -> work.

(** ** Parameter Semantics *)

(** In the following, we precisely define the semantics of the request
    bound functions. *)
Section RequestBoundFunctions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** *** Definition of Request Bound Functions *)

  (** First, what constitutes a valid request bound function for a task? *)
  Section RequestBoundFunctions.

    (** We say that a given bound [request_bound] is a valid request
        bound function iff [request_bound] is a monotonic function
        that equals 0 for the empty interval [delta = 0]. *)
    Definition valid_request_bound_function (request_bound : duration -> work) :=
      request_bound 0 = 0
      /\ monotone leq request_bound.

    (** We say that [request_bound] is an upper request bound for task
        [tsk] iff, for any interval <<[t1, t2)>>, [request_bound (t2 -
        t1)] bounds the sum of costs of jobs of [tsk] that arrive in
        that interval. *)
    Definition respects_max_request_bound (tsk : Task) (max_request_bound : duration -> work) :=
      forall (t1 t2 : instant),
        t1 <= t2 ->
        cost_of_task_arrivals arr_seq tsk t1 t2 <= max_request_bound (t2 - t1).

    (** We analogously define the lower request bound. *)
    Definition respects_min_request_bound (tsk : Task) (min_request_bound : duration -> work) :=
      forall (t1 t2 : instant),
        t1 <= t2 ->
        min_request_bound (t2 - t1) <= cost_of_task_arrivals arr_seq tsk t1 t2.

  End RequestBoundFunctions.

End RequestBoundFunctions.


(** ** Model Validity *)

(** Based on the just-established semantics, we define the properties of a
    valid request bound model. *)
Section RequestBoundFunctionsModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.

  (** ...and all kinds of request bounds. *)
  Context `{MaxRequestBound Task}
          `{MinRequestBound Task}.

  (** Let [ts] be an arbitrary task set. *)
  Variable ts : TaskSet Task.

  (** We say that [request_bound] is a valid arrival curve for a task set
      if it is valid for any task in the task set *)
  Definition valid_taskset_request_bound_function (request_bound : Task -> duration -> work) :=
    forall (tsk : Task), tsk \in ts -> valid_request_bound_function (request_bound tsk).

  (** Finally, we lift the per-task semantics of the respective
      request bound functions to the entire task set.  *)

  Definition taskset_respects_max_request_bound :=
    forall (tsk : Task), tsk \in ts -> respects_max_request_bound arr_seq tsk (max_request_bound tsk).

  Definition taskset_respects_min_request_bound :=
    forall (tsk : Task), tsk \in ts -> respects_min_request_bound arr_seq tsk (min_request_bound tsk).

End RequestBoundFunctionsModel.
