Require Export prosa.behavior.all.

(** * Definition of Work Conservation *)

(** In this module, we introduce a restrictive definition of work-conserving
    schedules. The definition is restrictive because it does not yet cover
    multiprocessor scheduling (there are plans to address this in future
    work). The definition does however cover effects such as jitter or
    self-suspensions that affect whether a job can be scheduled at a given
    point in time because it is based on the general notion of a job being
    [backlogged] (i.e., ready and not executing), which is parametric in any
    given job readiness model. *)

Section WorkConserving.
  (** Consider any type of jobs... *)
  Context {Job: JobType}.

  (** ... with arrival times and costs ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor model. *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Further, allow for any notion of job readiness. *)
  Context `{JobReady Job PState}.

  (** Given an arrival sequence and a schedule ... *)
  Variable arr_seq : arrival_sequence Job.
  Variable sched: schedule PState.

  (** ... we say that a scheduler is _work-conserving_ iff whenever a job [j]
     is backlogged, the processor is always busy executing another job
     [j_other]. Note that this definition is intentionally silent on matters of
     priority. *)
  Definition work_conserving :=
    forall j t,
      arrives_in arr_seq j ->
      backlogged sched j t ->
      exists j_other, scheduled_at sched j_other t.

End WorkConserving.

