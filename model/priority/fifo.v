Require Export prosa.model.priority.classes.

(** * FIFO Priority Policy *)

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as FIFO. Concrete implementations may choose to implement various
    tie-breaking rules in addition to the core FIFO priority order. The
    definition here allows for any tie-breaking rule. *)
Section FIFOPolicy.

  (**  Consider jobs with arrival times. *)
  Context {Job : JobType} `{JobArrival Job}.

  (** A JLFP policy is FIFO if it assigns higher priority to
      earlier-arriving jobs. That is, job [j1] has higher or equal priority
      than job [j2] if and only if it arrives no later than [j2]. *)
  Definition policy_is_FIFO (JLFP : JLFP_policy Job) :=
    forall j1 j2,
      hep_job j1 j2 = (job_arrival j1 <= job_arrival j2).

End FIFOPolicy.
