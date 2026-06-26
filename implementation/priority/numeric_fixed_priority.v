Require Export prosa.model.priority.numeric_fixed_priority.

(** * Numeric Fixed Task Priorities *)

(** In this section, we define ascending numeric fixed priorities, where a
    larger numeric value indicates higher priority, and note some trivial facts
    about this interpretation of priority values. *)
Section PropertiesNFPA.

  (** The instance [numeric_fp_ascending] assigns higher priority to tasks with
      higher numeric [task_priority] value. *)
  #[local] Instance numeric_fp_ascending (Task : TaskType) `{TaskPriority Task} : FP_policy Task :=
  {
    hep_task (tsk1 tsk2 : Task) := task_priority tsk1 >= task_priority tsk2
  }.

  (** Consider any kind of tasks with specified priorities. *)
  Context {Task : TaskType} `{TaskPriority Task}.

  (** The concrete [numeric_fp_ascending] implementation is indeed an ascending
      numeric FP policy. *)
  Fact NFPA_is_numeric_FP_ascending_policy :
    policy_is_numeric_FP_ascending (numeric_fp_ascending Task).
  Proof. by []. Qed.

  (** The resulting priority policy is reflexive. *)
  Fact NFPA_is_reflexive :
    reflexive_task_priorities (numeric_fp_ascending Task).
  Proof. by move=> ?; rewrite /hep_task /numeric_fp_ascending. Qed.

  (** The resulting priority policy is transitive. *)
  Fact NFPA_is_transitive :
    transitive_task_priorities (numeric_fp_ascending Task).
  Proof.
    move=> y x z.
    by rewrite /hep_task /numeric_fp_ascending => PRIO_yx PRIO_xy; lia.
  Qed.

  (** The resulting priority policy is total. *)
  Fact NFPA_is_total :
    total_task_priorities (numeric_fp_ascending Task).
  Proof. by move=> j1 j2; apply: leq_total. Qed.

End PropertiesNFPA.

(** Next, we define descending numeric fixed priorities, where a larger numeric
    value indicates lower priority, and again note some trivial facts about this
    alternate interpretation of priority values. *)
Section PropertiesNFPD.

  (** The instance [numeric_fp_descending] assigns lower priority to tasks with
      higher numeric [task_priority] value. *)
  #[local] Instance numeric_fp_descending (Task : TaskType) `{TaskPriority Task} : FP_policy Task :=
  {
    hep_task (tsk1 tsk2 : Task) := task_priority tsk1 <= task_priority tsk2
  }.

  (** Consider any kind of tasks with specified priorities. *)
  Context {Task : TaskType} `{TaskPriority Task}.

  (** The concrete [numeric_fp_descending] implementation is indeed a
      descending numeric FP policy. *)
  Fact NFPD_is_numeric_FP_descending_policy :
    policy_is_numeric_FP_descending (numeric_fp_descending Task).
  Proof. by []. Qed.

  (** The resulting priority policy is reflexive. *)
  Fact NFPD_is_reflexive :
    reflexive_task_priorities (numeric_fp_descending Task).
  Proof. by move=> ?; rewrite /hep_task /numeric_fp_descending. Qed.

  (** The resulting priority policy is transitive. *)
  Fact NFPD_is_transitive :
    transitive_task_priorities (numeric_fp_descending Task).
  Proof.
    move=> y x z.
    by rewrite /hep_task /numeric_fp_descending => PRIO_yx PRIO_xy; lia.
  Qed.

  (** The resulting priority policy is total. *)
  Fact NFPD_is_total :
    total_task_priorities (numeric_fp_descending Task).
  Proof. by move=> j1 j2; apply: leq_total. Qed.

End PropertiesNFPD.

(** We add the above facts into the [basic_rt_facts] hint database so Coq can
    apply them automatically where needed. *)
Global Hint Resolve
  NFPA_is_numeric_FP_ascending_policy
  NFPA_is_reflexive
  NFPA_is_transitive
  NFPA_is_total
  NFPD_is_numeric_FP_descending_policy
  NFPD_is_reflexive
  NFPD_is_transitive
  NFPD_is_total
  : basic_rt_facts.
