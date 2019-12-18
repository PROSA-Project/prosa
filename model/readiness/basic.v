Require Export prosa.behavior.all.

(** * Liu & Layland Readiness Model *)

(** In this module, we define the notion of job readiness for the classic Liu &
    Layland model without jitter or self-suspensions, where pending jobs are
    simply always ready. *)

Section LiuAndLaylandReadiness.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Suppose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** In the basic Liu & Layland model, a job is ready iff it is pending. *)
  Global Program Instance basic_ready_instance : JobReady Job PState :=
    {
      job_ready sched j t := pending sched j t
    }.

End LiuAndLaylandReadiness.

