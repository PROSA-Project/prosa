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

  (** We first note that ELF reduces to priority-point order for equal-priority
      tasks. *)
  Remark hep_job_elf_priority_point :
    forall j j',
      ep_task (job_task j) (job_task j') ->
      hep_job j j' = (job_priority_point j <= job_priority_point j')%R.
  Proof.
    move=> j j' EP.
    rewrite H_policy_is_ELF.
    have -> : hep_task (job_task j) (job_task j') = true by apply: ep_hep_task.
    have -> : hp_task (job_task j) (job_task j') = false by apply/negbTE/ep_not_hp_task.
    by rewrite andTb orFb.
  Qed.

  (** We then show that if we are looking at two jobs of the same task, then
      [hep_job] is a statement about their respective arrival times. *)
  Fact hep_job_arrival_elf :
    forall j j',
      same_task j j' ->
      hep_job j j' = (job_arrival j <= job_arrival j').
  Proof.
    move=> j j' SAME.
    rewrite hep_job_elf_priority_point.
    - move: SAME => /eqP SAME; rewrite /job_priority_point SAME; lia.
    - by move: SAME => /eqP ->; exact: eq_reflexive.
  Qed.

  (** ELF priorities are reflexive. *)
  Lemma ELF_policy_is_reflexive : reflexive_job_priorities JLFP.
  Proof.
    move=> j.
    rewrite H_policy_is_ELF.
    apply/orP; right; apply/andP; split=> //.
  Qed.

  (** ELF priorities are transitive. *)
  Lemma ELF_policy_is_transitive : transitive_job_priorities JLFP.
  Proof.
    move=> y x z.
    rewrite !H_policy_is_ELF.
    move=> /orP [hpxy| /andP[hepxy ppxy]] => /orP[hpyz| /andP [hepyz ppyz]].
    { apply/orP; left; exact: hp_trans hpyz. }
    { apply/orP; left; exact: hp_hep_trans hepyz. }
    { apply/orP; left; exact: hep_hp_trans hpyz. }
    { apply/orP; right; apply /andP; split.
      - exact: H_transitive_priorities hepyz.
      - exact: le_trans ppxy ppyz. }
  Qed.

  (** ELF priorities are total. *)
  Lemma ELF_policy_is_total : total_job_priorities JLFP.
  Proof.
    move=> x y.
    rewrite !H_policy_is_ELF.
    rewrite -implyNb; apply/implyP => /norP [Nhpxy /nandP [Nhpxy'|Njpxy] ].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { move: Nhpxy => /nandP [Nhepxy| NNhepyx].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { apply /orP; right. move: NNhepyx => /negbNE -> /=.
      move: Njpxy; lia. }}
  Qed.

  (** The ELF policy is [JLFP_FP_compatible]. *)
  Lemma ELF_policy_is_JLFP_FP_compatible :
    JLFP_FP_compatible JLFP FP.
  Proof.
    split => j1 j2.
    - rewrite H_policy_is_ELF.
      by move => /orP [/andP [HPTASK1 HPTASK2] | /andP [HEPTASK HEPJOB]].
    - move => HP_TASK.
      rewrite H_policy_is_ELF.
      by apply /orP; left.
  Qed.

  (** ** Sequentiality under ELF *)

  (** ELF policies satisfy the sequential-tasks hypothesis. *)
  Lemma ELF_respects_sequential_tasks :
    policy_respects_sequential_tasks JLFP.
  Proof. by move => j1 j2 TSK ARR; rewrite hep_job_arrival_elf. Qed.

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
      rewrite always_higher_priority_jlfp !hep_job_arrival_elf //.
      - by rewrite -ltnNge; apply/andP; split => //.
      - by rewrite same_task_sym.
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
    ELF_respects_sequential_tasks
    ELF_implies_sequential_tasks
 : basic_rt_facts.
