Require Export rt.restructuring.model.job.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** In this section we introduce the notion of a non-preemptive schedule. *)
Section NonpreemptiveSchedule.

  (** Consider any type of jobs ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state model. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.
  
  (** Consider any uniprocessor schedule. *)
  Variable sched : schedule PState.

  (** We define a schedule to be nonpreemptive iff every job remains scheduled until completion. *)
  Definition is_nonpreemptive_schedule := 
    forall (j : Job) (t t' : instant),
      t <= t' -> 
      scheduled_at sched j t ->
      ~~ completed_by sched j t' -> 
      scheduled_at sched j t'. 

End NonpreemptiveSchedule.