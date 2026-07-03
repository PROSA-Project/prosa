Require Export prosa.model.priority.elf.
Require Export prosa.model.aggregate.workload.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.facts.priority.sequential.

(** In this section, we state and prove some basic facts about ELF scheduling
    policies. *)
Section ELFBasicFacts.

  (** Consider any type of tasks with relative priority points ... *)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ... and jobs of these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} {AR : JobArrival Job}.

  (** Consider any arbitrary FP policy ... *)
  Context {FP : FP_policy Task}.

  (** ... that is reflexive, transitive, and total. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** Assume ELF scheduling. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_policy_is_ELF : policy_is_ELF FP JLFP.

  (** ** Basic properties of ELF policies *)

  (** Under ELF, higher-or-equal job priority implies higher-or-equal priority
      of the corresponding tasks. *)
  Fact ELF_policy_task_priority_order :
    forall j j',
      hep_job j j' -> hep_task (job_task j) (job_task j').
  Proof. by move: H_policy_is_ELF => [ELF _] j j'; exact: ELF. Qed.

  (** Among jobs of equal-priority tasks, higher-or-equal job priority implies
      no later absolute priority point. *)
  Fact ELF_policy_priority_point_order :
    forall j j',
      ep_task (job_task j) (job_task j') ->
      hep_job j j' -> (job_priority_point j <= job_priority_point j')%R.
  Proof.
    by move: H_policy_is_ELF => [_ [ELF _]] j j'; exact: ELF.
  Qed.

  (** ELF priorities are reflexive. *)
  Lemma ELF_policy_is_reflexive : reflexive_job_priorities JLFP.
  Proof. by move: H_policy_is_ELF => [_ [_ [REFL _]]]. Qed.

  (** ELF priorities are transitive. *)
  Lemma ELF_policy_is_transitive : transitive_job_priorities JLFP.
  Proof. by move: H_policy_is_ELF => [_ [_ [_ [TRANS _]]]]. Qed.

  (** ELF priorities are total. *)
  Lemma ELF_policy_is_total : total_job_priorities JLFP.
  Proof. by move: H_policy_is_ELF => [_ [_ [_ [_ TOTAL]]]]. Qed.

  (** A job whose task has strictly higher priority has higher-or-equal job
      priority. *)
  Fact ELF_policy_higher_priority_task :
    forall j j',
      hp_task (job_task j) (job_task j') -> hep_job j j'.
  Proof.
    move=> j j' HP.
    move: (ELF_policy_is_total j j') => /orP [//|HEP].
    exfalso; move: HP => /andP [_ /negP NHEP].
    by apply: NHEP; apply: ELF_policy_task_priority_order.
  Qed.

  (** Among jobs of equal-priority tasks, a strictly earlier priority point
      implies higher-or-equal job priority. *)
  Fact ELF_policy_earlier_priority_point :
    forall j j',
      ep_task (job_task j) (job_task j') ->
      (job_priority_point j < job_priority_point j')%R -> hep_job j j'.
  Proof.
    move=> j j' EP PP.
    move: (ELF_policy_is_total j j') => /orP [//|HEP].
    have EP' : ep_task (job_task j') (job_task j) by rewrite ep_task_sym.
    move: (ELF_policy_priority_point_order j' j EP' HEP).
    by lia.
  Qed.

  (** If a job does not have higher-or-equal priority, then totality gives the
      priority relation in the opposite direction. *)
  Fact ELF_policy_not_hep_job :
    forall j j',
      ~~ hep_job j j' -> hep_job j' j.
  Proof.
    move=> j j' NHEP.
    move: (ELF_policy_is_total j j').
    by rewrite (negbTE NHEP).
  Qed.

  (** Consequently, lack of higher-or-equal job priority reveals the opposite
      task-priority order. *)
  Fact ELF_policy_not_hep_task_priority_order :
    forall j j',
      ~~ hep_job j j' -> hep_task (job_task j') (job_task j).
  Proof.
    move=> j j' NHEP.
    by apply: ELF_policy_task_priority_order; apply: ELF_policy_not_hep_job.
  Qed.

  (** If two jobs stem from equal-priority tasks and the first does not have
      higher-or-equal priority, then the other job has no later priority point. *)
  Fact ELF_policy_not_hep_priority_point_order :
    forall j j',
      ep_task (job_task j) (job_task j') ->
      ~~ hep_job j j' -> (job_priority_point j' <= job_priority_point j)%R.
  Proof.
    move=> j j' EP NHEP.
    apply: ELF_policy_priority_point_order;
      first by rewrite ep_task_sym.
    by apply: ELF_policy_not_hep_job.
  Qed.

  (** For jobs of the same task, a strictly earlier arrival implies a strictly
      earlier priority point. *)
  Fact ELF_policy_earlier_arrival :
    forall j j',
      same_task j j' -> job_arrival j < job_arrival j' -> hep_job j j'.
  Proof.
    move=> j j' /eqP SAME LT.
    apply: ELF_policy_earlier_priority_point.
    - by rewrite SAME; exact: eq_reflexive.
    - by rewrite /job_priority_point SAME; lia.
  Qed.

  (** The ELF policy is [JLFP_FP_compatible]. *)
  Lemma ELF_policy_is_JLFP_FP_compatible :
    JLFP_FP_compatible JLFP FP.
  Proof.
    split => j1 j2.
    - exact: ELF_policy_task_priority_order.
    - exact: ELF_policy_higher_priority_task.
  Qed.

  (** ** Sequentiality under ELF *)

  (** ELF policies satisfy the sequential-tasks hypothesis. *)
  Lemma ELF_respects_sequential_tasks :
    policy_respects_sequential_tasks JLFP.
  Proof. by move => j1 j2; exact: ELF_policy_earlier_arrival. Qed.

  (** In this section, we prove that tasks always execute sequentially in a
      uniprocessor schedule following an ELF policy. *)
  Section ELFImpliesSequentialTasks.

    (** Consider any valid arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.
    Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

    (** Allow for any uniprocessor model. *)
    Context {PState : ProcessorState Job}.
    Hypothesis H_uniproc : uniprocessor_model PState.

    (** Next, consider any schedule of the arrival sequence, ... *)
    Variable sched : schedule PState.

    (** ... allow for any work-bearing notion of job readiness, ... *)
    Context `{@JobReady Job PState _ AR}.
    Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

    (** ... and assume that the schedule is valid. *)
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** Consider any valid preemption model. *)
    Context `{JobPreemptable Job}.
    Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

    (** Assume that the schedule respects the ELF policy. *)
    Hypothesis H_respects_policy :
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

    (** ELF implies the [sequential_tasks] property since earlier jobs of the
        same task have higher priority than later jobs. *)
    Lemma ELF_implies_sequential_tasks :
      sequential_tasks arr_seq sched.
    Proof.
      move => j1 j2 t ARR1 ARR2 SAME LT.
      apply: early_hep_job_is_scheduled => //;
        first exact: ELF_policy_is_transitive.
      rewrite always_higher_priority_jlfp.
      apply/andP; split; first exact: ELF_policy_earlier_arrival.
      apply/negP => HEP; move: SAME => /eqP SAME.
      have: (job_priority_point j2 <= job_priority_point j1)%R;
        last by rewrite /job_priority_point SAME; lia.
      apply: ELF_policy_priority_point_order => //.
      by rewrite SAME; exact: eq_reflexive.
    Qed.

  End ELFImpliesSequentialTasks.

End ELFBasicFacts.

(** We add the generally useful ELF facts into the [basic_rt_facts] hint
    database, so Coq can apply them automatically where needed. *)
Global Hint Resolve
    ELF_policy_is_reflexive
    ELF_policy_is_transitive
    ELF_policy_is_total
    ELF_policy_is_JLFP_FP_compatible
    ELF_policy_not_hep_job
    ELF_policy_not_hep_task_priority_order
    ELF_policy_not_hep_priority_point_order
    ELF_respects_sequential_tasks
    ELF_implies_sequential_tasks
 : basic_rt_facts.
