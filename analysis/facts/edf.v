Require Import prosa.model.priority.edf.
Require Import prosa.model.task.absolute_deadline.

(** In this section, we prove a few properties about EDF policy. *)
Section PropertiesOfEDF.

  (** Consider any type of tasks with relative deadlines ... *)
  Context {Task : TaskType}.
  Context `{TaskDeadline Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** EDF respects sequential tasks hypothesis. *)
  Lemma EDF_respects_sequential_tasks:
    policy_respects_sequential_tasks.
  Proof.
    intros j1 j2 TSK ARR.
    move: TSK => /eqP TSK.
    unfold hep_job, EDF, job_deadline, job_deadline_from_task_deadline; rewrite TSK.
      by rewrite leq_add2r.
  Qed.

End PropertiesOfEDF.

(** We add the above lemma into a "Hint Database" basic_facts, so Coq
    will be able to apply them automatically. *)
Hint Resolve EDF_respects_sequential_tasks : basic_facts.
