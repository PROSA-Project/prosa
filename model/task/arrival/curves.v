Require Export prosa.util.rel.
Require Export prosa.model.task.arrivals.

(** * The Arbitrary Arrival Curves Model *)

(** In the following, we define the notion of arbitrary arrival curves, which
    can be used to reason about the frequency of job arrivals. In contrast to
    the sporadic task model, the arbitrary arrival curves model is well-suited
    to expressing bursty and irregular arrival processes. *)

(** ** Task Parameters for the Arrival Curves Model *)

(** The arrival curves model describes tasks by giving an upper bound and,
    optionally, a lower bound on the number of new job arrivals during any
    given interval. These bounds are typically called arrival curves. *)

(** We let [max_arrivals tsk Δ] denote a bound on the maximum number of
    arrivals of jobs of task [tsk] in any interval of length [Δ]. *)
Class MaxArrivals (Task : TaskType) := max_arrivals : Task -> duration -> nat.

(** Conversely, we let [min_arrivals tsk Δ] denote a bound on the minimum
    number of arrivals of jobs of task [tsk] in any interval of length [Δ]. *)
Class MinArrivals (Task : TaskType) := min_arrivals : Task -> duration -> nat.

(** Alternatively, it is also possible to describe arbitrary arrival processes
    by specifying the minimum and maximum lengths of an interval in which a
    given number of jobs arrive. Such bounds are typically called minimum- and
    maximum-distance functions. *)

(** We let [min_separation tsk N] denote the minimal length of an interval in
    which exactly [N] jobs of task [tsk] arrive. *)
Class MinSeparation (Task : TaskType) := min_separation : Task -> nat -> duration.

(** Conversely, we let [max_separation tsk N] denote the maximal length of an interval in
    which exactly [N] jobs of task [tsk] arrive. *)
Class MaxSeparation (Task : TaskType) := max_separation : Task -> nat -> duration.


(** ** Parameter Semantics *)

(** In the following, we precisely define the semantics of the arrival curves
    model. *)
Section ArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** *** Definition of Arrival Curves *)

  (** First, what constitutes a valid arrival bound for a task? *)
  Section ArrivalCurves.

    (** We say that a given curve [num_arrivals] is a valid arrival curve for
        task [tsk] iff [num_arrivals] is a monotonic function that equals 0 for
        the empty interval [delta = 0]. *)
    Definition valid_arrival_curve (tsk : Task) (num_arrivals : duration -> nat) :=
      num_arrivals 0 = 0 /\
      monotone num_arrivals leq.

    (** We say that [max_arrivals] is an upper arrival bound for task [tsk]
        iff, for any interval <<[t1, t2)>>, [max_arrivals (t2 - t1)] bounds the
        number of jobs of [tsk] that arrive in that interval. *)
    Definition respects_max_arrivals (tsk : Task) (max_arrivals : duration -> nat) :=
      forall (t1 t2 : instant),
        t1 <= t2 ->
        number_of_task_arrivals arr_seq tsk t1 t2 <= max_arrivals (t2 - t1).

    (** We analogously define the lower arrival bound.. *)
    Definition respects_min_arrivals (tsk : Task) (min_arrivals : duration -> nat) :=
      forall (t1 t2 : instant),
        t1 <= t2 ->
        min_arrivals (t2 - t1) <= number_of_task_arrivals arr_seq tsk t1 t2.

  End ArrivalCurves.

  (** *** Definition of Minimum Distance Bounds *)

  (** Next, we define the semantics of minimum-distance bounds. *)
  Section SeparationBound.

    (** We say that a given function [min_separation] is a lower separation
        bound iff, for any number of jobs of task [tsk], [min_separation]
        lower-bounds the minimum interval length in which that many jobs can
        arrive. *)
    Definition respects_min_separation (tsk : Task) (min_separation: nat -> duration) :=
      forall t1 t2,
          t1 <= t2 ->
          min_separation (number_of_task_arrivals arr_seq tsk t1 t2) <= t2 - t1.

    (** We analogously define in upper separation bounds. *)
    Definition respects_max_separation (tsk : Task) (max_separation: nat -> duration):=
      forall t1 t2,
        t1 <= t2 ->
        t2 - t1 <= max_separation (number_of_task_arrivals arr_seq tsk t1 t2).

  End SeparationBound.

End ArrivalCurves.


(** ** Model Validity *)

(** Based on the just-established semantics, we define the properties of a
    valid arrival curves model. *)

Section ArrivalCurvesModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.

  (** ..and all kinds of arrival and separation curves. *)
  Context `{MaxArrivals Task}
          `{MinArrivals Task}
          `{MaxSeparation Task}
          `{MinSeparation Task}.

  (** Let [ts] be an arbitrary task set. *)
  Variable ts : TaskSet Task.

  (** We say that [arrivals] is a valid arrival curve for a task set
      if it is valid for any task in the task set *)
  Definition valid_taskset_arrival_curve (arrivals : Task -> duration -> nat) :=
    forall (tsk : Task), tsk \in ts -> valid_arrival_curve tsk (arrivals tsk).

  (** Finally, we lift the per-task semantics of the respective arrival and
  separation curves to the entire task set.  *)

  Definition taskset_respects_max_arrivals :=
    forall (tsk : Task), tsk \in ts -> respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  Definition taskset_respects_min_arrivals :=
    forall (tsk : Task), tsk \in ts -> respects_min_arrivals arr_seq tsk (min_arrivals tsk).

  Definition taskset_respects_max_separation :=
    forall (tsk : Task), tsk \in ts -> respects_max_separation arr_seq tsk (max_separation tsk).

  Definition taskset_respects_min_separation :=
    forall (tsk : Task), tsk \in ts -> respects_min_separation arr_seq tsk (min_separation tsk).

End ArrivalCurvesModel.
