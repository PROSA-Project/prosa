Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(* In this file we construct a jitter-aware task set that contains the
   jitter-aware schedule generated in the reduction. *)
Module JitterTaskSetGeneration.

  Import UniprocessorScheduleWithJitter Suspension Priority
         JitterScheduleConstruction.

  Section GeneratingTaskset.

    Context {Task: eqType}.

    (** Analysis Setup *)
    
    (* Let ts be the original, suspension-aware task set. *)
    Variable ts: seq Task.

    (* Assume that tasks have cost and suspension bound. *)
    Variable original_task_cost: Task -> time.
    Variable task_suspension_bound: Task -> time.

    (* Consider any FP policy that is reflexive, transitive and total, i.e., that
       indicates "higher-or-equal priority". *)
    Variable higher_eq_priority: FP_policy Task.

    (* Let tsk_i be any task to be analyzed... *)
    Variable tsk_i: Task.

    (* ...and recall the definition of higher-or-equal-priority tasks (other than tsk_i). *)
    Let other_hep_task tsk_other := higher_eq_priority tsk_other tsk_i && (tsk_other != tsk_i).

    (** Definition of Jitter-Aware Task Parameters *)
    
    (* We are going to define next a jitter-aware task set that models the jitter-aware
       schedule that we constructed in the reduction. *)

    (* First, using the task suspension bounds, we inflate the cost of the analyzed task
       in a suspension-oblivious manner. *)
    Definition inflated_task_cost (tsk: Task) :=
      if tsk == tsk_i then
        original_task_cost tsk + task_suspension_bound tsk
      else original_task_cost tsk.

    (* Next, assuming that higher-priority tasks have a valid response-time bound R,... *)
    Variable R: Task -> time.

    (* ...we define the task jitter as follows. *)
    Definition task_jitter (tsk: Task) :=
      if other_hep_task tsk then
        R tsk - original_task_cost tsk
      else 0.

  End GeneratingTaskset.

End JitterTaskSetGeneration.