Require Export rt.restructuring.behavior.all.

(** We define the readiness indicator function for the classic Liu & Layland
   model without jitter and no self-suspensions, where jobs are always
   ready. *)

Section LiuAndLaylandReadiness.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Supose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** In the basic Liu & Layland model, a job is ready iff it is pending. *)
  Global Program Instance basic_ready_instance : JobReady Job PState :=
    {
      job_ready sched j t := pending sched j t
    }.

End LiuAndLaylandReadiness.

