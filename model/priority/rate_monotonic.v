Require Export prosa.model.priority.classes.
Require Export prosa.model.task.arrival.sporadic.


(** * Rate-Monotonic Fixed-Priority Policy *)

(** We define the notion of rate-monotonic task priorities for sporadic tasks,
    i.e., the classic FP policy in which sporadic tasks are prioritized in
    order of their minimum inter-arrival times (or periods). *)
#[export] Instance RM (Task : TaskType) `{SporadicModel Task} : FP_policy Task :=
{
  hep_task (tsk1 tsk2 : Task) := task_min_inter_arrival_time tsk1 <= task_min_inter_arrival_time tsk2
}.

(** In this section, we prove a few basic properties of the RM policy. *)
Section Properties.

  (**  Consider sporadic tasks... *)
  Context {Task : TaskType}.
  Context `{SporadicModel Task}.

  (** ...and jobs stemming from these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** RM is reflexive. *)
  Lemma RM_is_reflexive : reflexive_task_priorities (RM Task).
  Proof. by move=> ?; rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /RM. Qed.

  (** RM is transitive. *)
  Lemma RM_is_transitive : transitive_task_priorities (RM Task).
  Proof. by move=> ? ? ?; apply: leq_trans. Qed.

  (** RM is total. *)
  Lemma RM_is_total : total_task_priorities (RM Task).
  Proof. by move=> ? ?; apply: leq_total. Qed.

End Properties.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve
     RM_is_reflexive
     RM_is_transitive
     RM_is_total
  : basic_rt_facts.

