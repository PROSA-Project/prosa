Require Export prosa.behavior.all.

(** * Liu & Layland Readiness Model *)

(** In this module, we specify the notion of job readiness for the classic Liu
    & Layland model without jitter or self-suspensions, where pending jobs are
    simply always ready. *)

Section LiuAndLaylandReadiness.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Suppose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** A readiness model is basic iff a job is ready exactly when it is
      pending. *)
  Definition basic_readiness (RM : JobReady Job PState) :=
    forall sched j t,
      job_ready sched j t = pending sched j t.

End LiuAndLaylandReadiness.
