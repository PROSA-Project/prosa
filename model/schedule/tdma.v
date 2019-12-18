Require Export prosa.model.task.concept.
Require Export prosa.util.seqset.
Require Export prosa.util.rel.
From mathcomp Require Import div.

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require prosa.model.processor.ideal.

(** * TDMA Scheduling *)

(** The TDMA scheduling policy is based on two properties.
    (1) Each task has a fixed, reserved time slot for execution;
    (2) These time slots are ordered in sequence to form a TDMA cycle, which
        repeats along the timeline.
    An example of TDMA schedule is illustrated in the following.
<<
    _______________________________
    | s1 |  s2  |s3| s1 |  s2  |s3|...
    --------------------------------------------->
    0                                            t
>> *)

(** ** Task Parameter for TDMA Scheduling *)

(** We define the TDMA policy as follows.*)
Section TDMAPolicy.

  Variable Task: eqType.
  (** With each task, we associate the duration of the corresponding TDMA slot. *)
  Definition TDMA_slot := Task -> duration.

  (** Moreover, within each TDMA cycle, task slots are ordered according to
      some relation (i.e, [slot_order slot1 slot2] means that [slot1] comes
      before [slot2] in a TDMA cycle). *)
  Definition TDMA_slot_order := rel Task.

End TDMAPolicy.

(** We introduce slots and the slot order as task parameters. *)
Class TDMAPolicy (T : TaskType) :=
  {
    task_time_slot : TDMA_slot T;
    slot_order : TDMA_slot_order T
  }.

(** ** TDMA Policy Validity *)

(** First, we define the properties of a valid TDMA policy. *)
Section ValidTDMAPolicy.

  Context {Task : eqType}.

  (** Consider any task set ts... *)
  Variable ts : {set Task}.

  (** ...and a TDMA policy. *)
  Context `{TDMAPolicy Task}.

  (** Time slot order must be transitive... *)
  Definition transitive_slot_order := transitive slot_order.

  (** ..., totally ordered over the task set... *)
  Definition total_slot_order :=
    total_over_list slot_order ts.

  (** ... and antisymmetric over task set. *)
  Definition antisymmetric_slot_order :=
    antisymmetric_over_list slot_order ts.

  (** A valid time slot must be positive *)
  Definition valid_time_slot :=
    forall tsk, tsk \in ts -> task_time_slot tsk > 0.

  Definition valid_TDMAPolicy :=
    transitive_slot_order /\ total_slot_order /\ antisymmetric_slot_order /\ valid_time_slot.

End ValidTDMAPolicy.

 (** ** TDMA Cycles, Sots, and Offsets *)

(** In this section, we define key TDMA concepts. *)
Section TDMADefinitions.

  Context {Task : eqType}.

  (** Consider any task set ts... *)
  Variable ts : {set Task}.

  (** ...and a TDMA policy. *)
  Context `{TDMAPolicy Task}.

  (** We define the TDMA cycle as the sum of all the tasks' time slots *)
  Definition TDMA_cycle:=
    \sum_(tsk <- ts) task_time_slot tsk.

  (** We define the function returning the slot offset for each task: i.e., the
      distance between the start of the TDMA cycle and the start of the task
      time slot. *)
  Definition task_slot_offset (tsk : Task) :=
    \sum_(prev_task <- ts | slot_order prev_task tsk && (prev_task != tsk)) task_time_slot prev_task.

  (** The following function tests whether a task is in its time slot at
      instant [t]. *)
  Definition task_in_time_slot (tsk : Task) (t:instant):=
    ((t + TDMA_cycle - (task_slot_offset tsk)%% TDMA_cycle) %% TDMA_cycle)
    < (task_time_slot tsk).

End TDMADefinitions.

(** ** TDMA Schedule Validity *)

Section TDMASchedule.

  Context {Task : TaskType} {Job : JobType}.

  Context `{JobArrival Job} `{JobCost Job} `{JobReady Job (option Job)} `{JobTask Job Task}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.

  (** ..., any uniprocessor ideal schedule ... *)
  Variable sched : schedule (ideal.processor_state Job).

  (** ... and any sporadic task set. *)
  Variable ts: {set Task}.

  Context `{TDMAPolicy Task}.

  (** In order to characterize a TDMA policy, we first define whether a job is executing its TDMA slot at time [t]. *)
  Definition job_in_time_slot (job:Job) (t:instant):=
    task_in_time_slot ts (job_task job) t.

  (** We say that a TDMA policy is respected by the schedule iff
       1. when a job is scheduled at time [t], then the corresponding task
          is also in its own time slot... *)
  Definition sched_implies_in_slot j t:=
    scheduled_at sched j t -> job_in_time_slot j t.

  (** 2. when a job is backlogged at time [t], the corresponding task
          isn't in its own time slot or another previous job of the same task is scheduled *)
  Definition backlogged_implies_not_in_slot_or_other_job_sched j t:=
    backlogged sched j t ->
    ~ job_in_time_slot j t \/
    exists j_other, arrives_in arr_seq j_other/\
                    job_arrival j_other < job_arrival j/\
                    job_task j = job_task j_other/\
                    scheduled_at sched j_other t.

  Definition respects_TDMA_policy:=
    forall (j:Job) (t:instant),
      arrives_in arr_seq j ->
      sched_implies_in_slot j t /\
      backlogged_implies_not_in_slot_or_other_job_sched j t.
End TDMASchedule.
