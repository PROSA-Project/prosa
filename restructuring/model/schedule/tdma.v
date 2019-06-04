From rt.restructuring.behavior Require Import task schedule.ideal.
From rt.util Require Export seqset list.
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.

(** In this section, we define the TDMA policy.*)
Section TDMAPolicy.

  (* The TDMA policy is based on two properties.
      (1) Each task has a fixed, reserved time slot for execution;
      (2) These time slots are ordered in sequence to form a TDMA cycle, which repeats along the timeline.
      An example of TDMA schedule is illustrated in the following.
      ______________________________
      | s1 |  s2  |s3| s1 |  s2  |s3|...
      --------------------------------------------->
      0                                            t
   *)

  Variable Task: eqType.
  (* With each task, we associate the duration of the corresponding TDMA slot. *)
  Definition TDMA_slot := Task -> duration.

  (* Moreover, within each TDMA cycle, task slots are ordered according to some relation.
  (i.e, slot_order slot1 slot2 means that slot1 comes before slot2 in a TDMA cycle) *)
  Definition TDMA_slot_order := rel Task.

End TDMAPolicy.

Class TDMAPolicy (T : TaskType) :=
  { task_time_slot : TDMA_slot T;
    slot_order : TDMA_slot_order T }.

(* First, we define the properties of a valid TDMA policy. *)
Section ValidTDMAPolicy.

  Context {Task : eqType}.

  (* Consider any task set ts... *)
  Variable ts : {set Task}.

  (* ...and a TDMA policy. *)
  Context `{TDMAPolicy Task}.

  (* Time slot order must be transitive... *)
  Definition transitive_slot_order := transitive slot_order.

  (* ..., totally ordered over the task set... *)
  Definition total_slot_order :=
    total_over_list slot_order ts.

  (* ... and antisymmetric over task set. *)
  Definition antisymmetric_slot_order :=
    antisymmetric_over_list slot_order ts.

  (* A valid time slot must be positive *)
  Definition valid_time_slot :=
    forall tsk, tsk \in ts -> task_time_slot tsk > 0.

  Definition valid_TDMAPolicy :=
    transitive_slot_order /\ total_slot_order /\ antisymmetric_slot_order /\ valid_time_slot.

End ValidTDMAPolicy.

(** In this section, we define functions on a TDMA policy *)
Section TDMADefinitions.

  Context {Task : eqType}.

  (* Consider any task set ts... *)
  Variable ts : {set Task}.

  (* ...and a TDMA policy. *)
  Context `{TDMAPolicy Task}.

  (* We define the TDMA cycle as the sum of all the tasks' time slots *)
  Definition TDMA_cycle:=
    \sum_(tsk <- ts) task_time_slot tsk.

  (* We define the function returning the slot offset for each task:
         i.e., the distance between the start of the TDMA cycle and
         the start of the task time slot *)
  Definition Task_slot_offset (tsk : Task) :=
    \sum_(prev_task <- ts | slot_order prev_task tsk && (prev_task != tsk)) task_time_slot prev_task.

  (* The following function tests whether a task is in its time slot at instant t *)
  Definition Task_in_time_slot (tsk : Task) (t:instant):=
    ((t + TDMA_cycle - (Task_slot_offset tsk)%% TDMA_cycle) %% TDMA_cycle)
    < (task_time_slot tsk).
End TDMADefinitions.
