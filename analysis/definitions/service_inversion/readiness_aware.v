Require Export prosa.analysis.abstract.definitions.
Require Export prosa.analysis.definitions.readiness_interference.
Require Export prosa.analysis.definitions.service_inversion.pred.

(** * Readiness-Aware Service Inversion *)

Section ServiceInversion.

  (** Consider any kind of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider any kind of uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uni : uniprocessor_model PState.

  (** Consider any notion of readiness. *)
  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume a JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** In this section, we define a readiness-aware notion of service inversion. *)
  Section Definitions.

    (** Consider a job [j]. *)
    Variable j : Job.

    (** Recall the existing notion of service inversion that does not
        take job readiness into account. *)
    Let readiness_oblivious_service_inversion := pred.service_inversion arr_seq sched.

    (** We say that readiness-aware service inversion is taking place at some instant [t] if a
        lower-priority job (w.r.t [j]) is being served in spite of a higher-or-equal-priority
        job (w.r.t [j]) being schedulable, ... *)
    Definition service_inversion (t : instant) :=
      some_hep_job_ready arr_seq sched j t
      && readiness_oblivious_service_inversion j t.

    (** ... with the obvious extension to intervals. *)
    Definition cumulative_service_inversion (t1 t2 : instant) :=
      \sum_(t1 <= t < t2) service_inversion t.

  End Definitions.

  (** In this section, we define the notion of a bound on readiness-aware service inversion
      in a busy-window prefix. *)
  Section ServiceInversionBound.

    (** Assume that we have some definition of interference and interfering workload. *)
    Context `{Interference Job}.
    Context `{InterferingWorkload Job}.

    (** We say that [B] is a bound on the _readiness-aware_ service inversion incurred by any job [j]
        inside its busy interval <<[t1, t2]>> if [B] bounds the readiness-aware cumulative service
        inversion within the interval <<[t1, t2]>>. *)
    Definition service_inversion_is_bounded (B : duration -> duration) :=
      forall j t1 t2,
        busy_interval_prefix sched j t1 t2 ->
        cumulative_service_inversion j t1 t2 <= B (job_arrival j - t1).

  End ServiceInversionBound.

End ServiceInversion.
