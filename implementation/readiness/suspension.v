Require Export prosa.model.readiness.suspension.

(** * Readiness Model for Self-Suspending Jobs *)

(** In this module, we define the concrete readiness instance for jobs that
    exhibit self-suspensions. *)

Section ReadinessOfSelfSuspendingJobs.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Suppose jobs have an arrival time, a cost, and that they exhibit
      self-suspensions. *)
  Context `{JobArrival Job} `{JobCost Job} `{JobSuspension Job}.

  (** In the self-suspension model, a job is ready iff its current suspension
      has passed and it is not yet complete. *)
  #[local,program] Instance self_suspension_ready_instance : JobReady Job PState :=
  {
    job_ready sched j t := suspension_has_passed sched j t
                           && ~~ completed_by sched j t
  }.
  Next Obligation.
    move=> sched j t /andP[PASSED UNFINISHED].
    rewrite /pending. apply /andP. split => //.
    move: PASSED. rewrite /suspension_has_passed /has_arrived => /andP [ARR _].
    by apply: leq_trans ARR; rewrite leq_addr.
  Qed.

  (** The concrete self-suspension readiness instance satisfies the axiomatic
      specification of self-suspension readiness. *)
  Fact self_suspension_readiness_spec :
    self_suspension_readiness self_suspension_ready_instance.
  Proof. by []. Qed.

End ReadinessOfSelfSuspendingJobs.

(** We add the concrete model's specification to the basic facts database so
    implementation modules can use it automatically. *)
Global Hint Resolve self_suspension_readiness_spec : basic_rt_facts.
