Require Export prosa.model.priority.deadline_monotonic.

(** * Deadline-Monotonic Fixed-Priority Policy *)

(** We introduce the classic DM priority policy, under which tasks are
    prioritized in order of their relative deadlines. *)
#[local] Instance DM (Task : TaskType) `{TaskDeadline Task} : FP_policy Task :=
{
  hep_task (tsk1 tsk2 : Task) := task_deadline tsk1 <= task_deadline tsk2
}.

(** In this section, we prove a few basic properties of the concrete DM policy. *)
Section Properties.

  (** Consider any kind of tasks with relative deadlines. *)
  Context {Task : TaskType} `{TaskDeadline Task}.

  (** The concrete [DM] implementation is indeed a DM policy. *)
  Fact DM_is_DM_policy :
    policy_is_DM (DM Task).
  Proof. by []. Qed.

  (** DM is reflexive. *)
  Fact DM_is_reflexive :
    reflexive_task_priorities (DM Task).
  Proof. by move=> ?; rewrite /hep_task /DM. Qed.

  (** DM is transitive. *)
  Fact DM_is_transitive :
    transitive_task_priorities (DM Task).
  Proof. by move=> t y x z; apply: leq_trans. Qed.

  (** DM is total. *)
  Fact DM_is_total :
    total_task_priorities (DM Task).
  Proof. by move=> ? ?; apply: leq_total. Qed.

End Properties.

(** We add the above facts into the [basic_rt_facts] hint database so Coq can
    apply them automatically where needed. *)
Global Hint Resolve
  DM_is_DM_policy
  DM_is_reflexive
  DM_is_transitive
  DM_is_total
  : basic_rt_facts.
