Require Export prosa.model.readiness.basic.

(** * Liu & Layland Readiness Model *)

(** In this module, we define the concrete readiness instance for the classic
    Liu & Layland model without jitter or self-suspensions, where pending jobs
    are simply always ready. *)

Section LiuAndLaylandReadiness.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Suppose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** In the basic Liu & Layland model, a job is ready iff it is pending. *)
  #[local,program] Instance basic_ready_instance : JobReady Job PState :=
  {
    job_ready sched j t := pending sched j t
  }.
  Next Obligation. by done. Qed.

  (** The concrete basic readiness instance satisfies the axiomatic
      specification of basic readiness. *)
  Fact basic_readiness_spec :
    basic_readiness basic_ready_instance.
  Proof. by []. Qed.

End LiuAndLaylandReadiness.

(** We add the concrete model's specification to the basic facts database so
    implementation modules can use it automatically. *)
Global Hint Resolve basic_readiness_spec : basic_rt_facts.
