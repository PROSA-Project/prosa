Require Export prosa.model.preemption.parameter.

(** * Preemption Times *)

(** The preemption framework defines a generic predicate [job_preemptable] as
    the interface to various preemption models. Crucially, [job_preemptable]
    does not depend on the current schedule or the current time, but only on
    the job's progress, i.e., it indicates the presence or absence of a
    preemption _point_ in the job's execution. In this section, we define the
    notion of a preemption _time_ in an ideal uniprocessor schedule base on the
    progress of the currently scheduled job.

    NB: For legacy reasons, the following definition are currently specific to
    ideal uniprocessor schedules. Lifting this assumption is future work. *)

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require prosa.model.processor.ideal.

Section PreemptionTime.

  (**  Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any preemption model, ... *)
  Context `{JobPreemptable Job}.

  (** ... and any ideal uniprocessor schedule of such jobs. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** We say that a time [t] is a preemption time iff the job that is currently
      scheduled at [t], if any, can be preempted according to the predicate
      [job_preemptable] (which encodes the preemption model). An idle instant
      is always a preemption time. *)
  Definition preemption_time (t : instant) :=
    if sched t is Some j then
      job_preemptable j (service sched j t)
    else true.

End PreemptionTime.
