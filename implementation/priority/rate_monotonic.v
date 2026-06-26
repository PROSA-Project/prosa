Require Export prosa.model.priority.rate_monotonic.

(** * Rate-Monotonic Fixed-Priority Policy *)

(** We introduce the classic RM priority policy, under which sporadic tasks are
    prioritized in order of their minimum inter-arrival times, or periods. *)
#[local] Instance RM (Task : TaskType) `{SporadicModel Task} : FP_policy Task :=
{
  hep_task (tsk1 tsk2 : Task) :=
    task_min_inter_arrival_time tsk1 <= task_min_inter_arrival_time tsk2
}.

(** In this section, we prove a few basic properties of the concrete RM policy. *)
Section Properties.

  (** Consider sporadic tasks. *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** The concrete [RM] implementation is indeed an RM policy. *)
  Fact RM_is_RM_policy :
    policy_is_RM (RM Task).
  Proof. by []. Qed.

  (** RM is reflexive. *)
  Fact RM_is_reflexive :
    reflexive_task_priorities (RM Task).
  Proof. by move=> ?; rewrite /hep_task /RM. Qed.

  (** RM is transitive. *)
  Fact RM_is_transitive :
    transitive_task_priorities (RM Task).
  Proof. by move=> ? ? ?; apply: leq_trans. Qed.

  (** RM is total. *)
  Fact RM_is_total :
    total_task_priorities (RM Task).
  Proof. by move=> ? ?; apply: leq_total. Qed.

End Properties.

(** We add the above facts into the [basic_rt_facts] hint database so Coq can
    apply them automatically where needed. *)
Global Hint Resolve
  RM_is_RM_policy
  RM_is_reflexive
  RM_is_transitive
  RM_is_total
  : basic_rt_facts.
