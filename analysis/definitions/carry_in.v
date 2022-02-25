From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
Require Export prosa.model.priority.classes.

(** * No Carry-In *)
(** In this module, we define the notion of a time without any carry-in work. *)
Section NoCarryIn.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has an arrival time and a cost. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job}.

  (** Consider any arrival sequence of such jobs with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and the resultant schedule. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** There is no carry-in at time [t] iff every job (regardless of priority)
      from the arrival sequence released before [t] has completed by that time. *)
  Definition no_carry_in (t : instant) :=
    forall j_o,
      arrives_in arr_seq j_o ->
      arrived_before j_o t ->
      completed_by sched j_o t.

End NoCarryIn.
