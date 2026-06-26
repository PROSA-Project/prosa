Require Export prosa.model.priority.classes.

(** * EDF Priority Policy *)

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as EDF. *)
Section EDFPolicy.

  (** Consider jobs with absolute deadlines. *)
  Context {Job : JobType} `{JobDeadline Job}.

  (** A JLFP policy is EDF if it assigns higher priority to jobs with earlier
      absolute deadlines. That is, job [j1] has higher or equal priority than
      job [j2] if and only if [j1]'s deadline is no later than [j2]'s
      deadline. *)
  Definition policy_is_EDF (JLFP : JLFP_policy Job) :=
    forall j1 j2,
      hep_job j1 j2 = (job_deadline j1 <= job_deadline j2).

End EDFPolicy.
