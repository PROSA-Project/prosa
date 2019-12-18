Require Export prosa.model.priority.classes.

(** * Deadline-Monotonic Fixed-Priority Policy *)

(** We define the notion of deadline-monotonic task priorities, i.e., the
    classic FP policy in which tasks are prioritized in order of their relative
    deadlines. *)
Instance DM (Task : TaskType) `{TaskDeadline Task} : FP_policy Task :=
{
  hep_task (tsk1 tsk2 : Task) := task_deadline tsk1 <= task_deadline tsk2
}.

(** In this section, we prove a few basic properties of the DM policy. *)
Section Properties.

  (**  Consider any kind of tasks with relative deadlines... *)
  Context {Task : TaskType}.
  Context `{TaskDeadline Task}.

  (** ...and jobs stemming from these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** DM is reflexive. *)
  Lemma DM_is_reflexive : reflexive_priorities.
  Proof. by move=> ?; rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /DM. Qed.

  (** DM is transitive. *)
  Lemma DM_is_transitive : transitive_priorities.
  Proof. by intros t y x z; apply leq_trans. Qed.

  (** DM is total. *)
  Lemma DM_is_total : total_priorities.
 Proof. by move=> t j1 j2; apply leq_total. Qed.

End Properties.

(** We add the above lemmas into a "Hint Database" basic_facts, so Coq
    will be able to apply them automatically. *)
Hint Resolve
     DM_is_reflexive
     DM_is_transitive
     DM_is_total
  : basic_facts.

