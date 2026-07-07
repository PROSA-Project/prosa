Require Export prosa.model.readiness.jitter.

(** * Readiness Model for Jobs with Release Jitter *)

(** In this module, we define the concrete readiness instance for jobs that
    exhibit release jitter, but no self-suspensions. *)

Section ReadinessOfJitteryJobs.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Suppose jobs have an arrival time, a cost, and exhibit release jitter. *)
  Context `{JobArrival Job} `{JobCost Job} `{JobJitter Job}.

  (** In the release-jitter model, a job is ready iff it has been released and
      is not yet complete. *)
  #[local,program] Instance jitter_ready_instance : JobReady Job PState :=
  {
    job_ready sched j t := is_released j t && ~~ completed_by sched j t
  }.
  Next Obligation.
    move=> sched j t /andP[REL UNFINISHED].
    rewrite /pending. apply /andP. split => //.
    move: REL. rewrite /is_released /has_arrived.
    by apply: leq_trans; rewrite leq_addr.
  Qed.

  (** The concrete release-jitter readiness instance satisfies the axiomatic
      specification of jitter readiness. *)
  Fact jitter_readiness_spec :
    jitter_readiness jitter_ready_instance.
  Proof. by []. Qed.

End ReadinessOfJitteryJobs.

(** We add the concrete model's specification to the basic facts database so
    implementation modules can use it automatically. *)
Global Hint Resolve jitter_readiness_spec : basic_rt_facts.
