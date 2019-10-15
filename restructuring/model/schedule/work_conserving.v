From rt.restructuring.behavior Require Export all.

(** In this file, we introduce a restrictive definition of work conserving
   uniprocessor schedules. The definition is restrictive because it does not
   allow for effects such as jitter or self-suspensions that affect whether a
   job can be scheduled at a given point in time. A more general notion of work
   conservation that is "readiness-aware", as well as a variant that covers
   global scheduling, is TBD. *)

Section WorkConserving.
  (** Consider any type of job associated with any type of tasks... *)
  Context {Job: JobType}.

  (** ... with arrival times and costs ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state model. *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Further, allow for any notion of job readiness. *)
  Context `{JobReady Job PState}.

  (** Given an arrival sequence and a schedule ... *)
  Variable arr_seq : arrival_sequence Job.
  Variable sched: schedule PState.

  (** We say that a scheduler is work-conserving iff whenever a job j
     is backlogged, the processor is always busy with another job. *)
  Definition work_conserving :=
    forall j t,
      arrives_in arr_seq j ->
      backlogged sched j t ->
      exists j_other, scheduled_at sched j_other t.

End WorkConserving.
