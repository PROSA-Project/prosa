Require Export prosa.model.priority.classes.

(** * Deadline-Monotonic Fixed-Priority Policy *)

(** We define the notion of deadline-monotonic task priorities, i.e., the
    classic FP policy in which tasks are prioritized in order of their relative
    deadlines. *)
#[export] Instance DM (Task : TaskType) `{TaskDeadline Task} : FP_policy Task :=
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
  Lemma DM_is_reflexive : reflexive_task_priorities (DM Task).
  Proof. by move=> ?; rewrite /hep_task /DM. Qed.

  (** DM is transitive. *)
  Lemma DM_is_transitive : transitive_task_priorities (DM Task).
  Proof. by move=> t y x z; apply: leq_trans. Qed.

  (** DM is total. *)
  Lemma DM_is_total : total_task_priorities (DM Task).
  Proof. by move=> ? ?; apply: leq_total. Qed.

End Properties.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve
     DM_is_reflexive
     DM_is_transitive
     DM_is_total
  : basic_rt_facts.

