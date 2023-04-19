Require Export prosa.model.priority.elf.
Require Export prosa.model.aggregate.workload.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.definitions.priority.classes.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.facts.priority.sequential.
Require Export prosa.analysis.facts.priority.gel.

(** In this section, we state and prove some basic facts about the ELF scheduling policy. *)
Section ELFBasicFacts.

  (** Consider any type of tasks with relative priority points...*)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ...and jobs of these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} {AR : JobArrival Job}.

  (** Consider any arbitrary FP policy ...*)
  Variable FP : FP_policy Task.

  (** ... that is reflexive, transitive, and total. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** ** Basic properties of the ELF policy *)

  (** ELF is reflexive. *)
  Lemma ELF_is_reflexive : reflexive_job_priorities (ELF FP).
  Proof. by move=> j; apply /orP; right; apply/andP; split=> //; exact: GEL_is_reflexive. Qed.

  (** ELF is transitive. *)
  Lemma ELF_is_transitive : transitive_job_priorities (ELF FP).
  Proof.
    move=> y x z.
    move=> /orP [hpxy| /andP[hepxy jpxy]] => /orP[hpyz| /andP [hepyz jpyz]].
    { apply/orP; left; exact: hp_trans hpyz. }
    { apply/orP; left; exact: hp_hep_trans hepyz. }
    { apply/orP; left; exact: hep_hp_trans hpyz. }
    { apply/orP; right; apply /andP; split.
      - exact: H_transitive_priorities hepyz.
      - by apply: (GEL_is_transitive y). }
  Qed.

  (** ELF is total. *)
  Lemma ELF_is_total : total_job_priorities (ELF FP).
  Proof.
    move=> x y.
    rewrite -implyNb; apply/implyP => /norP [Nhpxy /nandP [Nhpxy'|Njpxy] ].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { move: Nhpxy => /nandP [Nhepxy| NNhepyx].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { apply /orP; right. move: NNhepyx => /negbNE -> /=.
      move: Njpxy; unfold hep_job, GEL; lia. }}
  Qed.

  (** The ELF policy is [JLFP_FP_compatible]. *)
  Lemma ELF_is_JLFP_FP_compatible :
    JLFP_FP_compatible (ELF FP) FP.
  Proof.
    split; move => j1 j2.
    - rewrite /hep_job /ELF.
      by move => /orP [/andP [HPTASK1 HPTASK2] | /andP [HEPTASK HEPJOB]].
    - move => HP_TASK.
      by apply /orP; left.
  Qed.

  (** ** ELF policy respects sequential tasks. *)

  (** We first show that if we are looking at two jobs of the same task,
      then [hep_job] is a statement about their respective arrival times. *)
  Lemma hep_job_arrival_elf :
    forall j j',
      same_task j j' ->
      hep_job j j' = (job_arrival j <= job_arrival j').
  Proof.
    move=> j j' SAME.
    rewrite /hep_job/ELF.
    move: (SAME) => /eqP ->; rewrite hp_task_irrefl orFb.
    by rewrite hep_job_arrival_gel // H_reflexive_priorities andTb.
  Qed.

  (** The above fact helps us prove that the ELF policy respects sequential tasks. *)
  Lemma ELF_respects_sequential_tasks :
    policy_respects_sequential_tasks (ELF FP).
  Proof. by move => j1 j2 TSK ARR; rewrite hep_job_arrival_elf. Qed.

  (** In this section, we prove that tasks always execute sequentially in a schedule following the ELF policy. *)
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

    (** In addition, we assume that jobs have preemption points specified by the following attribute... *)
    Context `{JobPreemptable Job}.

    (** ... and that it defines a valid preemption model. *)
    Hypothesis H_valid_preemption_model :
      valid_preemption_model arr_seq sched.

    (** Next, we assume that the schedule respects the scheduling policy at every preemption point. *)
    Hypothesis H_respects_policy :
      respects_JLFP_policy_at_preemption_point arr_seq sched (ELF FP).

    (** To prove sequentiality, we use the lemma [early_hep_job_is_scheduled]. Clearly, under the
        ELF priority policy, jobs satisfy the conditions described by the lemma (i.e., given two
        jobs [j1] and [j2] from the same task, if [j1] arrives earlier than [j2], then [j1] always
        has a higher priority than job [j2], and hence completes before [j2]); therefore, ELF implies
        the [sequential_tasks] property. *)
    Lemma ELF_implies_sequential_tasks :
      sequential_tasks arr_seq sched.
    Proof.
      move => j1 j2 t ARR1 ARR2 SAME LT.
      apply: early_hep_job_is_scheduled => // t';
        first by apply ELF_is_transitive.
      rewrite /hep_job_at  /JLFP_to_JLDP !hep_job_arrival_elf //.
      - by lia.
      - by rewrite same_task_sym.
    Qed.

  End ELFImpliesSequentialTasks.

End ELFBasicFacts.

(** We add the above facts into a "Hint Database" basic_rt_facts, so Coq will
    be able to apply them automatically where needed. *)
Global Hint Resolve
    ELF_is_reflexive
    ELF_is_transitive
    ELF_is_total
    ELF_is_JLFP_FP_compatible
    ELF_respects_sequential_tasks
    ELF_implies_sequential_tasks
 : basic_rt_facts.
