Require Export prosa.model.priority.classes.

(** * Always Higher Priority *)
(** In this section, we define what it means for a job to always have
    a higher priority than another job. *)
Section AlwaysHigherPriority.

  (** Consider any type of jobs ... *)
  Context {Job : JobType}.

  (** ... and any JLDP policy. *)
  Context `{JLDP_policy Job}.

  (** We say that a job [j1] always has higher priority than job [j2]
      if, at any time [t], the priority of job [j1] is strictly higher than
      the priority of job [j2]. *)
  Definition always_higher_priority (j1 j2 : Job) :=
    forall t, hep_job_at t j1 j2 && ~~ hep_job_at t j2 j1.

End AlwaysHigherPriority.

(** We note that, under a job-level fixed-priority policy, the property is
    trivial since job priorities by definition do not change in this case. *)
Section UnderJLFP.
  (** Consider any type of jobs ... *)
  Context {Job : JobType}.

  (** ... and any JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** The property [always_higher_priority j j'] is equivalent to a statement
      about [hep_job]. *)
  Fact always_higher_priority_jlfp :
    forall j j',
      always_higher_priority j j' <-> (hep_job j j' && ~~ hep_job j' j).
  Proof.
    move=> j j'.
    rewrite /always_higher_priority/JLFP_to_JLDP/hep_job_at //; split => //.
    by apply; exact: 0.
  Qed.

End UnderJLFP.
