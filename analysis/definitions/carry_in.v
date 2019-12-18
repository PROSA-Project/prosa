Require Export prosa.model.priority.classes.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require Import prosa.model.processor.ideal.

(** * No Carry-In *)
(** In this module we define the notion of no carry-in time for uni-processor schedulers. *)
Section NoCarryIn.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.    

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  
  (** Next, consider any ideal uni-processor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** The processor has no carry-in at time t iff every job (regardless of priority) 
      from the arrival sequence released before t has completed by that time. *)
  Definition no_carry_in (t : instant) :=
    forall j_o,
      arrives_in arr_seq j_o ->
      arrived_before j_o t ->
      completed_by sched j_o t.

End NoCarryIn. 