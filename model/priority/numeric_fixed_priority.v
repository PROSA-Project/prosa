Require Export prosa.model.priority.classes.

(** * Numeric Fixed Task Priorities *)

(** We define the notion of arbitrary numeric fixed task priorities, i.e.,
    tasks are prioritized in order of user-provided numeric priority values,
    where numerically smaller values indicate lower priorities (as for instance
    it is the case in Linux). *)

(** First, we define a new task parameter [task_priority] that maps each task
    to a numeric priority value. *)
Class TaskPriority (Task : TaskType) := task_priority : Task -> nat.

(** Based on this parameter, we define the corresponding FP policy. *)
Instance NumericFP (Task : TaskType) `{TaskPriority Task} : FP_policy Task :=
{
  hep_task (tsk1 tsk2 : Task) := task_priority tsk1 >= task_priority tsk2
}.

(** In this section, we prove a few basic properties of numeric fixed priorities. *)
Section Properties.

  (**  Consider any kind of tasks with specified priorities... *)
  Context {Task : TaskType}.
  Context `{TaskPriority Task}.

  (** ...and jobs stemming from these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** The resulting priority policy is reflexive. *)
  Lemma NFP_is_reflexive : reflexive_priorities.
  Proof. by move=> ?; rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /NumericFP. Qed.

  (** The resulting priority policy is transitive. *)
  Lemma NFP_is_transitive : transitive_priorities.
  Proof.
    move=> t y x z.
    rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /NumericFP.
    by move=> PRIO_yx PRIO_zy; apply leq_trans with (n := task_priority (job_task y)).
  Qed.

  (** The resulting priority policy is total. *)
  Lemma NFP_is_total : total_priorities.
  Proof. by move=> t j1 j2; apply leq_total. Qed.

End Properties.

(** We add the above lemmas into a "Hint Database" basic_facts, so Coq
    will be able to apply them automatically. *)
Hint Resolve
     NFP_is_reflexive
     NFP_is_transitive
     NFP_is_total
  : basic_facts.

