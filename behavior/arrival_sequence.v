From mathcomp Require Export ssreflect seq ssrnat ssrbool bigop eqtype ssrfun.
Require Export prosa.behavior.job.
Require Export prosa.util.notation.

(** This module contains basic definitions and properties of job arrival
    sequences. *)

(** * Notion of an Arrival Sequence *)

(** We begin by defining a job arrival sequence. *)
Section ArrivalSequence.

  (** Given any job type with decidable equality, ... *)
  Variable Job: JobType.

  (** ..., an arrival sequence is a mapping from any time to a (finite) sequence of jobs. *)
  Definition arrival_sequence := instant -> seq Job.

End ArrivalSequence.

(** * Arrival of a Job *)

(** Next, we define properties of jobs in a given arrival sequence. *)
Section JobProperties.

  (** Consider any job arrival sequence. *)
  Context {Job: JobType}.
  Variable arr_seq: arrival_sequence Job.

  (** First, we define the sequence of jobs arriving at time t. *)
  Definition arrivals_at (t : instant) := arr_seq t.

  (** Next, we say that job j arrives at a given time t iff it belongs to the
       corresponding sequence. *)
  Definition arrives_at (j : Job) (t : instant) := j \in arrivals_at t.

  (** Similarly, we define whether job j arrives at some (unknown) time t, i.e.,
       whether it belongs to the arrival sequence. *)
  Definition arrives_in (j : Job) := exists t, j \in arrivals_at t.

End JobProperties.

(** * Validity of an Arrival Sequence *)

(** Next, we define valid arrival sequences. *)
Section ValidArrivalSequence.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** We say that arrival times are consistent if any job that arrives in the
     sequence has the corresponding arrival time. *)
  Definition consistent_arrival_times :=
    forall j t,
      arrives_at arr_seq j t -> job_arrival j = t.

  (** We say that the arrival sequence is a set iff it doesn't contain duplicate
     jobs at any given time. *)
  Definition arrival_sequence_uniq := forall t, uniq (arrivals_at arr_seq t).

  (** We say that the arrival sequence is valid iff it is a set and arrival times
     are consistent *)
  Definition valid_arrival_sequence :=
    consistent_arrival_times /\ arrival_sequence_uniq.

End ValidArrivalSequence.

(** * Arrival Time Predicates *)

(** Next, we define properties of job arrival times. *)
Section ArrivalTimeProperties.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Let j be any job. *)
  Variable j: Job.

  (** We say that job j has arrived at time t iff it arrives at some time t_0
     with t_0 <= t. *)
  Definition has_arrived (t : instant) := job_arrival j <= t.

  (** Next, we say that job j arrived before t iff it arrives at some time t_0
     with t_0 < t. *)
  Definition arrived_before (t : instant) := job_arrival j < t.

  (** Finally, we say that job j arrives between t1 and t2 iff it arrives at
     some time t with t1 <= t < t2. *)
  Definition arrived_between (t1 t2 : instant) := t1 <= job_arrival j < t2.

End ArrivalTimeProperties.

(** * Finite Arrival Sequence Prefixes *)

(** In this section, we define arrival sequence prefixes, which are useful to
   define (computable) properties over sets of jobs in the schedule. *)
Section ArrivalSequencePrefix.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** By concatenation, we construct the list of jobs that arrived in the
     interval <<[t1, t2)>>. *)
  Definition arrivals_between (t1 t2 : instant) :=
    \cat_(t1 <= t < t2) arrivals_at arr_seq t.

  (** Based on that, we define the list of jobs that arrived up to time t, ...*)
  Definition arrivals_up_to (t : instant) := arrivals_between 0 t.+1.

  (** ...and the list of jobs that arrived strictly before time t. *)
  Definition arrivals_before (t : instant) := arrivals_between 0 t.

End ArrivalSequencePrefix.
