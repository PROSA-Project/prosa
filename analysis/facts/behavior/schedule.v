Require Export prosa.util.all.
Require Export prosa.behavior.all.

(** * Schedules *)

(** In this file, we establish basic facts about the jobs scheduled in a given
    processor state, i.e., about the generic notions derived from [job_on]. *)

Section ScheduledJobs.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... and any type of processor state. *)
  Context {PState : ProcessorState Job}.

  (** We observe that a job is scheduled in a given processor state exactly if it
      occurs in the list of jobs scheduled in that state. That is, the predicate
      [scheduled_in] and the enumeration [jobs_scheduled_in] agree. *)
  Lemma jobs_scheduled_in_iff :
    forall (j : Job) (s : PState),
      scheduled_in j s = (j \in jobs_scheduled_in s).
  Proof.
    move=> j s; apply/idP/idP.
    - move=> /existsP[c /eqP ON].
      by rewrite /jobs_scheduled_in mem_pmap -ON map_f ?mem_enum.
    - rewrite /jobs_scheduled_in mem_pmap => /mapP[c _ EQ].
      by apply/existsP; exists c; rewrite /scheduled_on -EQ.
  Qed.

End ScheduledJobs.
