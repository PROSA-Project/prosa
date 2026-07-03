Require Export prosa.model.priority.classes.

(** * EDF Priority Policy *)

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as EDF. *)
Section EDFPolicy.

  (** Consider jobs with absolute deadlines. *)
  Context {Job : JobType} `{JobDeadline Job}.

  (** A JLFP policy is EDF if it never assigns higher priority to a job with a
      later absolute deadline. Ties among jobs with equal deadlines may be
      resolved by any reflexive, transitive, and total tie-breaking rule. *)
  Definition policy_is_EDF (JLFP : JLFP_policy Job) :=
    (forall j1 j2, hep_job j1 j2 ->
                   job_deadline j1 <= job_deadline j2)
    /\ reflexive_job_priorities JLFP
    /\ transitive_job_priorities JLFP
    /\ total_job_priorities JLFP.

End EDFPolicy.
