Require Export prosa.model.priority.edf.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.model.task.preemption.parameters.

(** We first make some trivial observations about EDF priorities to avoid
    repeating these steps in subsequent proofs. *)
Section PriorityFacts.
  (** Consider any type of jobs with arrival times. *)
  Context `{Job : JobType} `{JobArrival Job}.

  (** First, consider the general case where jobs have arbitrary deadlines. *)
  Section JobDeadline.

    (** Assume EDF priorities based on (arbitrary) [job_deadline] parameters. *)
    Context `{JobDeadline Job} {JLFP : JLFP_policy Job}.
    Hypothesis H_policy_is_EDF : policy_is_EDF JLFP.

    (** Under EDF, higher-or-equal priority implies no later absolute
        deadline. *)
    Fact EDF_policy_deadline_order :
      forall j j',
        hep_job j j' -> job_deadline j <= job_deadline j'.
    Proof. by move: H_policy_is_EDF => [EDF _] j j'; exact: EDF. Qed.

    (** The EDF policy is reflexive by assumption. *)
    Fact EDF_policy_is_reflexive :
      reflexive_job_priorities JLFP.
    Proof.
      by move: H_policy_is_EDF => [_ [REFL _]].
    Qed.

    (** The EDF policy is transitive by assumption. *)
    Fact EDF_policy_is_transitive :
      transitive_job_priorities JLFP.
    Proof.
      by move: H_policy_is_EDF => [_ [_ [TRANS _]]].
    Qed.

    (** The EDF policy is total by assumption. *)
    Fact EDF_policy_is_total :
      total_job_priorities JLFP.
    Proof.
      by move: H_policy_is_EDF => [_ [_ [_ TOTAL]]].
    Qed.

    (** A job with a strictly earlier deadline has higher-or-equal
        priority. *)
    Fact EDF_policy_earlier_deadline :
      forall j j',
        job_deadline j < job_deadline j' -> hep_job j j'.
    Proof.
      move=> j j' DL.
      move: (EDF_policy_is_total j j') => /orP [//|HEP].
      move: (EDF_policy_deadline_order _ _ HEP).
      by move=> LE; move: DL; rewrite ltnNge LE.
    Qed.

    (** Conversely, if a job does not have higher-or-equal priority, then the
        other job has no later deadline. *)
    Fact EDF_policy_not_hep_deadline_order :
      forall j j',
        ~~ hep_job j j' -> job_deadline j' <= job_deadline j.
    Proof.
      move=> j j' NHEP.
      apply: EDF_policy_deadline_order.
      move: (EDF_policy_is_total j j').
      by rewrite (negbTE NHEP).
    Qed.

  End JobDeadline.

  (** Second, consider the case where job (absolute) deadlines are derived from
      task (relative) deadlines. *)
  Section TaskDeadline.

    (** If the jobs stem from tasks with relative deadlines ... *)
    Context {Task : TaskType}.
    Context `{TaskDeadline Task}.
    Context `{JobTask Job Task}.

    (** If EDF priorities are derived from [task_deadline], ... *)
    Context {JLFP : JLFP_policy Job}.
    Hypothesis H_policy_is_EDF : policy_is_EDF JLFP.

    (** ... then a higher-or-equal priority job's arrival time is constrained. *)
    Fact EDF_policy_task_deadline_order :
      forall j j',
        hep_job j j' ->
        job_arrival j + task_deadline (job_task j)
        <= job_arrival j' + task_deadline (job_task j').
    Proof.
      move=> j j' HEP.
      by move: (EDF_policy_deadline_order H_policy_is_EDF j j' HEP)
         ; rewrite /job_deadline/job_deadline_from_task_deadline.
    Qed.

    (** Conversely, a strictly earlier arrival time plus relative deadline
        implies higher-or-equal priority. *)
    Fact EDF_policy_earlier_task_deadline :
      forall j j',
        job_arrival j + task_deadline (job_task j)
        < job_arrival j' + task_deadline (job_task j') ->
        hep_job j j'.
    Proof.
      move=> j j' DL.
      apply: (EDF_policy_earlier_deadline H_policy_is_EDF).
      by rewrite /job_deadline/job_deadline_from_task_deadline.
    Qed.

    (** For jobs of the same task, a strictly earlier arrival implies an
        earlier absolute deadline. *)
    Fact EDF_policy_earlier_arrival :
      forall j j',
        same_task j j' ->
        job_arrival j < job_arrival j' ->
        hep_job j j'.
    Proof.
      move=> j j' /eqP SAME LT.
      apply: EDF_policy_earlier_task_deadline.
      by rewrite SAME ltn_add2r.
    Qed.

    (** EDF scheduling respects the sequential-tasks hypothesis. *)
    Fact EDF_policy_respects_sequential_tasks :
      policy_respects_sequential_tasks JLFP.
    Proof.
      by move=> j j' SAME; exact: EDF_policy_earlier_arrival.
    Qed.
  End TaskDeadline.

End PriorityFacts.

(** We add the above lemma into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply it automatically. *)
Global Hint Resolve
  EDF_policy_is_reflexive
  EDF_policy_is_transitive
  EDF_policy_is_total
  EDF_policy_not_hep_deadline_order
  EDF_policy_respects_sequential_tasks
  : basic_rt_facts.

Require Export prosa.model.task.sequentiality.
Require Export prosa.analysis.facts.priority.sequential.
Require Export prosa.analysis.facts.model.sequential.

(** In this section, we prove that EDF scheduling implies that tasks
    are executed sequentially. *)
Section SequentialEDF.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.

  (** ... with a bound on the maximum non-preemptive segment length.
      The bound is needed to ensure that, at any instant, it always
      exists a subsequent preemption time in which the scheduler can,
      if needed, switch to another higher-priority job. *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** Further, consider any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Allow for any uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Next, consider any schedule of this arrival sequence, ... *)
  Variable sched : schedule PState.

  (** Assume EDF scheduling. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_policy_is_EDF : policy_is_EDF JLFP.

  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context `{@JobReady Job PState Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Assume an EDF schedule. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** To prove sequentiality, we use lemma
      [early_hep_job_is_scheduled]. Clearly, under the EDF priority
      policy, jobs satisfy the conditions described by the lemma
      (i.e., given two jobs [j1] and [j2] from the same task, if [j1]
      arrives earlier than [j2], then [j1] always has a higher
      priority than job [j2], and hence completes before [j2]);
      therefore EDF implies sequential tasks. *)
  Lemma EDF_policy_implies_sequential_tasks :
    sequential_tasks arr_seq sched.
  Proof.
    move => j1 j2 t ARR1 ARR2 SAME LT.
    apply: early_hep_job_is_scheduled => //.
    rewrite always_higher_priority_jlfp.
    apply/andP; split; first exact: EDF_policy_earlier_arrival.
    apply/negP => HEP.
    apply EDF_policy_task_deadline_order in HEP => //.
    move: HEP; rewrite -(eqP SAME) leq_add2r => LE.
    by move: LT; rewrite ltnNge LE.
  Qed.

End SequentialEDF.
