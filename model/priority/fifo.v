Require Export prosa.model.priority.classes.

(** * FIFO Priority Policy *)

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as FIFO. Concrete implementations may choose to implement various
    tie-breaking rules in addition to the core FIFO priority order. The
    definition here allows for any tie-breaking rule. *)
Section FIFOPolicy.

  (**  Consider jobs with arrival times. *)
  Context {Job : JobType} `{JobArrival Job}.

  (** A JLFP policy is FIFO if it never assigns higher priority to a
      later-arriving job. Ties among jobs that arrive at the same time may be
      resolved by any reflexive, transitive, and total tie-breaking rule. *)
  Definition policy_is_FIFO (JLFP : JLFP_policy Job) :=
    (forall j1 j2, hep_job j1 j2 -> job_arrival j1 <= job_arrival j2)
    /\ reflexive_job_priorities JLFP
    /\ transitive_job_priorities JLFP
    /\ total_job_priorities JLFP.

End FIFOPolicy.
