Require Export prosa.behavior.all.

(** This file defines simple allocation substitutions and a swapping operation
    as used for instance in the classic EDF optimality proof. *)

(** We begin by defining the notion of a schedule with a "tweaked" (i.e.,
    overridden) allocation. *)
Section ReplaceAt.
  (** For any given type of jobs... *)
  Context {Job : JobType}.
  (** ... any given type of processor states, ... *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ...consider any given reference schedule. *)
  Variable original_sched: schedule PState.

  (** Suppose we are given a specific time [t'] ... *)
  Variable t': instant.

  (** ...and a replacement state [new_state]. *)
  Variable new_state: PState.

  (** Then the schedule with replacement is simply one that returns the given
     [new_state] at [t'], and the original allocation at all other times. *)
  Definition replace_at (t : instant) :=
    if t' == t then new_state else (original_sched t).

End ReplaceAt.


(** Based on [replace_at], we define the notion of a schedule with swapped
    allocations. *)
Section Swapped.
  (** For any given type of jobs... *)
  Context {Job : JobType}.
  (** ... any given type of processor states, ... *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ...consider any given reference schedule. *)
  Variable original_sched: schedule PState.

  (** Given two specific times [t1] and [t2]... *)
  Variable t1 t2: instant.

  (** ...we define the notion of a schedule in which the two allocations at [t1]
     and [t2] have been swapped. *)
  Definition swapped : schedule PState :=
    let s1 := original_sched t1 in
    let s2 := original_sched t2 in
    let replaced_s1 := replace_at original_sched t1 s2 in
    replace_at replaced_s1 t2 s1.

End Swapped.
