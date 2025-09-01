Require Export prosa.model.job.properties.
Require Export prosa.model.priority.definitions.
Require Export prosa.analysis.abstract.definitions.

(** * Readiness Interference *)


(** In this file, we define the "interference" (or delay) incurred by a job due to the
    fact that the job may become non-ready before its completion.

    We model this interference as an instant when there is no
    higher-or-equal priority ready jobs (w.r.t. the job under analysis).
    This can be due to self-suspension or other similar behavior.

    By design, the notion of interference defined here is mutually
    exclusive with "regular" interference, i.e., the execution of
    other higher-or-equal-priority jobs irrespective of whether the
    job under analysis is ready.

    The two notions being mutually exclusive will help us simplify
    proofs later on. Therefore, we model interference due to the job
    under analysis becoming non-ready as an instant when there is no
    higher-or-equal-priority ready job. *)

Section ReadinessInterference.
  (** Consider any tasks. *)
  Context {Task : TaskType}.

  (** Consider any kind of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobTask Job Task}.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any notion of readiness.
      Note that although any notion of readiness would work, it wouldn't make
      sense to have this kind of interference in case of a work-bearing notion of
      readiness, since this interference would always be false in that case. *)
  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence of jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Consider any JLFP priority policy. *)
  Context {JLFP : JLFP_policy Job}.

  Section Definitions.
    (** Now consider any job [j]. *)
    Variable j : Job.

    (** We are interested in instants at which at least one higher-or-equal-priority job is ready. *)
    Definition some_hep_job_ready (t : instant) :=
      has (fun j' => job_ready sched j' t)
        [seq j' <- arrivals_up_to arr_seq t | hep_job j' j].

    (** Based on the above definition, we introduce a notion of cumulative interference
        in a given interval due to the absence of higher-or-equal-priority ready jobs. *)
    Definition cumulative_readiness_interference (t1 t2 : instant) :=
      \sum_(t1 <= t < t2) ~~ some_hep_job_ready t.

  End Definitions.

  (** In this section, we define the notion of a bound on
      _readiness interference_. *)
  Section Bound.
    (** Assume that we have some definition of [Interference] and [InterferingWorkload]. *)
    Context `{Interference Job}.
    Context `{InterferingWorkload Job}.

    (** We say [B] is a bound on _readiness interference_ if for any job [j] and any
        interval <<[t1, t1 + Δ)>> that is inside the busy interval <<[t1, t2]>> of [j],
        [B] is a upper bounds the total interference due to the absence of higher-or-equal priority
        ready jobs in the interval <<[t1, t1 + Δ)>>. *)
    Definition readiness_interference_is_bounded (B : duration -> duration -> duration) :=
      forall j t1 t2 Δ,
        t1 + Δ <= t2 ->
        busy_interval_prefix sched j t1 t2 ->
        cumulative_readiness_interference j t1 (t1 + Δ) <= B (job_arrival j - t1) Δ.

  End Bound.

End ReadinessInterference.
