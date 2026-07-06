Require Export prosa.model.priority.fp.
Require Export prosa.analysis.definitions.priority.classes.

(** In this section, we state and prove some basic facts about job-level
    policies that behave as fixed-priority policies. *)
Section FPPolicyFacts.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and jobs of these tasks. *)
  Context {Job : JobType} `{JobTask Job Task}.

  (** Consider any arbitrary FP policy ... *)
  Context {FP : FP_policy Task}.

  (** ... and a JLFP policy that behaves like it. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_policy_is_FP : policy_is_FP FP JLFP.

  (** Under such a policy, higher-or-equal job priority implies
      higher-or-equal priority of the corresponding tasks. *)
  Fact FP_policy_task_priority_order :
    forall j j',
      @hep_job _ JLFP j j' -> hep_task (job_task j) (job_task j').
  Proof. by move: H_policy_is_FP => [PRIO _] j j'; exact: PRIO. Qed.

  (** Conversely, strict task priority implies higher-or-equal job priority. *)
  Fact FP_policy_higher_priority_task :
    forall j j',
      hp_task (job_task j) (job_task j') -> @hep_job _ JLFP j j'.
  Proof. by move: H_policy_is_FP => [_ [PRIO _]] j j'; exact: PRIO. Qed.

  (** FP-like job priorities are reflexive by definition. *)
  Fact FP_policy_is_reflexive : reflexive_job_priorities JLFP.
  Proof. by move: H_policy_is_FP => [_ [_ [REFL _]]]. Qed.

  (** FP-like job priorities are transitive by definition. *)
  Fact FP_policy_is_transitive : transitive_job_priorities JLFP.
  Proof. by move: H_policy_is_FP => [_ [_ [_ [TRANS _]]]]. Qed.

  (** FP-like job priorities are total by definition. *)
  Fact FP_policy_is_total : total_job_priorities JLFP.
  Proof. by move: H_policy_is_FP => [_ [_ [_ [_ TOTAL]]]]. Qed.

End FPPolicyFacts.

(** We add the generally useful FP-policy facts into the [basic_rt_facts] hint
    database, so Coq can apply them automatically where needed. *)
Global Hint Resolve
    FP_policy_is_reflexive
    FP_policy_is_transitive
    FP_policy_is_total
 : basic_rt_facts.
