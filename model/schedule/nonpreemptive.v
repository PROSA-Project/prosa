Require Export prosa.behavior.all.

(** * Nonpreemptive Schedules  *)

(** In this module, we introduce a simple alternative definition of
    nonpreemptive schedules. Take also note of the fully nonpreemptive
    preemption model in model.preemption.fully_nonpreemptive. *)

Section NonpreemptiveSchedule.

  (** Consider any type of jobs with execution costs ... *)
  Context {Job : JobType}.
  Context `{JobCost Job}.

  (** ... and any kind of processor model. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.
  
  (** We say that a given schedule is _nonpreemptive_ if every job,
      once it is scheduled, remains scheduled until completion. *)
  Definition nonpreemptive_schedule (sched : schedule PState) := 
    forall (j : Job) (t t' : instant),
      t <= t' -> 
      scheduled_at sched j t ->
      ~~ completed_by sched j t' -> 
      scheduled_at sched j t'. 

End NonpreemptiveSchedule.
