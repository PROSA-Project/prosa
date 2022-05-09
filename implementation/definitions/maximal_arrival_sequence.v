Require Export prosa.model.task.arrival.curves.
Require Export prosa.util.supremum.

(** * A Maximal Arrival Sequence *)

(** In this section, we propose a concrete instantiation of an arrival sequence.
    Given an arbitrary arrival curve, the defined arrival sequence tries to
    generate as many jobs as possible at any time instant by adopting a greedy
    strategy: at each time [t], the arrival sequence contains the maximum possible
    number of jobs that does not violate the given arrival curve's constraints. *)
Section MaximalArrivalSequence.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Let [max_arrivals] denote any function that takes a task and an interval length
      and returns the associated number of job arrivals of the task. *)
  Context `{MaxArrivals Task}.

  (** In this section, we define a procedure that computes the maximal number of
      jobs that can be released at a given instant without violating the
      corresponding arrival curve. *)
  Section NumberOfJobs.

    (** Let [tsk] be any task. *)
    Variable tsk : Task.

    (** First, we introduce a function that computes the sum of all elements in
        a given list's suffix of length [n]. *)
    Definition suffix_sum xs n := \sum_(size xs - n <= t < size xs) nth 0 xs t.

    (** Let the arrival prefix [arr_prefix] be a sequence of natural numbers,
        where [nth xs t] denotes the number of jobs that arrive at time [t].
        Then, given an arrival curve [max_arrivals] and an arrival prefix
        [arr_prefix], we define a function that computes the number of jobs that
        can be additionally released without violating the arrival curve.

        The high-level idea is as follows. Let us assume that the length of the
        arrival prefix is [Δ]. To preserve the sub-additive property, one needs
        to go through all suffixes of the arrival prefix and pick the
        minimum. *)
    Definition jobs_remaining (arr_prefix : seq nat) :=
      supremum leq [seq (max_arrivals tsk Δ.+1 - suffix_sum arr_prefix Δ) | Δ <- iota 0 (size arr_prefix).+1].

    (** Further, we define the function [next_max_arrival] to handle a special
        case: when the arrival prefix is empty, the function returns the value
        of the arrival curve with a window length of [1]. Otherwise, it returns
        the number the number of jobs that can additionally be generated.  *)
    Definition next_max_arrival (arr_prefix : seq nat) :=
      match jobs_remaining arr_prefix with
      | None => max_arrivals tsk 1
      | Some n => n
      end.

    (** Next, we define a function that extends by one a given arrival prefix... *)
    Definition extend_arrival_prefix (arr_prefix : seq nat) :=
      arr_prefix ++ [:: next_max_arrival arr_prefix ].

    (** ... and a function that generates a maximal arrival prefix
        of size [t], starting from an empty arrival prefix. *)
    Definition maximal_arrival_prefix (t : nat) :=
      iter t.+1 extend_arrival_prefix [::].

    (** Finally, we define a function that returns the maximal number
        of jobs that can be released at time [t]; this definition
        assumes that at each time instant prior to time [t] the maximal
        number of jobs were released. *)
    Definition max_arrivals_at t := nth 0 (maximal_arrival_prefix t) t.

  End NumberOfJobs.

  (** Consider a function that generates [n] concrete jobs of
      the given task at the given time instant. *)
  Variable generate_jobs_at : Task -> nat -> instant -> seq Job.

  (** The maximal arrival sequence of task set [ts] at time [t] is a
      concatenation of sequences of generated jobs for each task. *)
  Definition concrete_arrival_sequence (ts : seq Task) (t : instant) :=
    \cat_(tsk <- ts) generate_jobs_at tsk (max_arrivals_at tsk t) t.

End MaximalArrivalSequence.
