Require Export prosa.model.priority.classes.

(** * Fixed-Priority Policy *)

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as fixed-priority scheduling with respect to a task-level
    fixed-priority policy. *)
Section FPPolicy.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and jobs of these tasks. *)
  Context {Job : JobType} `{JobTask Job Task}.

  (** Given an underlying FP policy, a JLFP policy behaves as an FP policy if
      it never inverts task-level priority, and every strict task-priority
      relation is reflected at the job level. Jobs of equal-priority tasks may
      be ordered by any reflexive, transitive, and total tie-breaking rule. *)
  Definition policy_is_FP (FP : FP_policy Task) (JLFP : JLFP_policy Job) :=
    (forall j1 j2,
        hep_job j1 j2 ->
        hep_task (job_task j1) (job_task j2))
    /\ (forall j1 j2,
          hp_task (job_task j1) (job_task j2) ->
          hep_job j1 j2)
    /\ reflexive_job_priorities JLFP
    /\ transitive_job_priorities JLFP
    /\ total_job_priorities JLFP.

End FPPolicy.
