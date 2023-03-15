Require Export prosa.model.priority.classes.

(** We define properties linking JLFP and FP policies. *)
Section JLFP_FP.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Consider any pair of JLFP and FP policies. *)
  Context (JLFP : JLFP_policy Job) (FP : FP_policy Task).

  (** A JLFP policy is compatible with a FP policy if the priority
      of the first on jobs doesn't contradict the priority of the
      second on tasks. *)
  Definition JLFP_FP_compatible :=
    (forall j1 j2, hep_job j1 j2 -> hep_task (job_task j1) (job_task j2))
    /\ (forall j1 j2, hp_task (job_task j1) (job_task j2) -> hep_job j1 j2).

End JLFP_FP.
