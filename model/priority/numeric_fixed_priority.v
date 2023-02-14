Require Export prosa.model.priority.classes.

(** * Numeric Fixed Task Priorities *)

(** We define the notion of arbitrary numeric fixed task priorities, i.e.,
    tasks are prioritized in order of user-provided numeric priority values,
    where numerically smaller values indicate lower priorities (as for instance
    it is the case in Linux). *)

(** First, we define a new task parameter [task_priority] that maps each task
    to a numeric priority value. *)
Class TaskPriority (Task : TaskType) := task_priority : Task -> nat.

(** Based on this parameter, we define two corresponding FP policies. In one
    instance, a lower numeric value indicates lower priority, while in the other
    instance, a lower numeric value indicates higher priority. Both these
    interpretations can be found in practice and in the literature. For example,
    Linux uses "higher numeric value <-> higher priority", whereas many papers
    assume "lower numeric value <-> higher priority". *)

(** In this section, we define ascending numeric fixed priorities, where a
    larger numeric value indicates higher priority, and note some trivial facts
    about this interpretation of priority values. *)
Section PropertiesNFPA.

  (** The instance [NumericFPAscending] assigns higher priority to tasks with
      higher numeric [task_priority] value. *)
  #[local] Instance NumericFPAscending (Task : TaskType) `{TaskPriority Task} : FP_policy Task :=
    {
      hep_task (tsk1 tsk2 : Task) := task_priority tsk1 >= task_priority tsk2
    }.

  (**  Consider any kind of tasks with specified priorities... *)
  Context {Task : TaskType}.
  Context `{TaskPriority Task}.

  (** ...and jobs stemming from these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** The resulting priority policy is reflexive. *)
  Lemma NFPA_is_reflexive : reflexive_priorities.
  Proof.  by move=> ?; rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /NumericFPAscending. Qed.

  (** The resulting priority policy is transitive. *)
  Lemma NFPA_is_transitive : transitive_priorities.
  Proof.
    move=> t y x z.
    rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /NumericFPAscending.
    by move=> PRIO_yx PRIO_zy; apply leq_trans with (n := task_priority (job_task y)).
  Qed.

  (** The resulting priority policy is total. *)
  Lemma NFPA_is_total : total_priorities.
  Proof. by move=> t j1 j2; apply: leq_total. Qed.

End PropertiesNFPA.

(** Next, we define descending numeric fixed priorities, where a larger numeric
    value indicates lower priority, and again note some trivial facts about this
    alternate interpretation of priority values. *)
Section PropertiesNFPD.

  (** The instance [NumericFPDescending] assigns lower priority to tasks with
      higher numeric [task_priority] value. *)
  #[local] Instance NumericFPDescending (Task : TaskType) `{TaskPriority Task} : FP_policy Task :=
    {
      hep_task (tsk1 tsk2 : Task) := task_priority tsk1 <= task_priority tsk2
    }.

  (**  Consider any kind of tasks with specified priorities... *)
  Context {Task : TaskType}.
  Context `{TaskPriority Task}.

  (** ...and jobs stemming from these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** The resulting priority policy is reflexive. *)
  Lemma NFPD_is_reflexive : reflexive_priorities.
  Proof.  by  move=> ?; rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /NumericFPDescending. Qed.

  (** The resulting priority policy is transitive. *)
  Lemma NFPD_is_transitive : transitive_priorities.
  Proof.
    move=> t y x z.
    rewrite /hep_job_at /JLFP_to_JLDP /hep_job /FP_to_JLFP /hep_task /NumericFPDescending.
    by move=> PRIO_yx PRIO_zy; apply leq_trans with (n := task_priority (job_task y)).
  Qed.

  (** The resulting priority policy is total. *)
  Lemma NFPD_is_total : total_priorities.
  Proof. by move=> t j1 j2; apply: leq_total. Qed.

End PropertiesNFPD.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve
     NFPA_is_reflexive
     NFPA_is_transitive
     NFPA_is_total
     NFPD_is_reflexive
     NFPD_is_transitive
     NFPD_is_total
  : basic_rt_facts.

