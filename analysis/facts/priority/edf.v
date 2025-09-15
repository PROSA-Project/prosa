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

    (** If jobs have arbitrary deadlines ... *)
    Context `{JobDeadline Job}.

    (** ... then [hep_job] is a statement about these deadlines. *)
    Fact hep_job_deadline :
      forall j j',
        hep_job j j' = (job_deadline j <= job_deadline j').
    Proof. by move=> j j'; rewrite /hep_job /EDF. Qed.

  End JobDeadline.

  (** Second, consider the case where job (absolute) deadlines are derived from
      task (relative) deadlines. *)
  Section TaskDeadline.

    (** If the jobs stem from tasks with relative deadlines ... *)
    Context {Task : TaskType}.
    Context `{TaskDeadline Task}.
    Context `{JobTask Job Task}.

    (** ... then [hep_job] is a statement about job arrival times and relative
        deadlines. *)
    Fact hep_job_task_deadline :
      forall j j',
        hep_job j j' = (job_arrival j + task_deadline (job_task j)
                        <= job_arrival j' + task_deadline (job_task j')).
    Proof.
      move=> j j'.
      by rewrite hep_job_deadline /job_deadline/job_deadline_from_task_deadline.
    Qed.

      (** Furthermore, if we are looking at two jobs of the same task, then
          [hep_job] is a statement about their respective arrival times. *)
    Fact hep_job_arrival_edf :
      forall j j',
        same_task j j' ->
        hep_job j j' = (job_arrival j <= job_arrival j').
    Proof.
      by move=> j j' /eqP SAME; rewrite hep_job_task_deadline SAME leq_add2r.
    Qed.

    (** EDF respects the sequential-tasks hypothesis. *)
    Lemma EDF_respects_sequential_tasks :
      policy_respects_sequential_tasks (EDF Job).
    Proof.
      by move => j j' /eqP TSK ?; rewrite hep_job_arrival_edf // /same_task TSK.
    Qed.
  End TaskDeadline.

End PriorityFacts.

(** We add the above lemma into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply it automatically. *)
Global Hint Resolve EDF_respects_sequential_tasks : basic_rt_facts.

Require Export prosa.model.task.sequentiality.
Require Export prosa.analysis.facts.priority.inversion.
Require Export prosa.analysis.facts.priority.sequential.
Require Export prosa.analysis.facts.model.sequential.

(** In this section, we prove that the EDF priority policy implies that tasks
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
    respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).

  (** To prove sequentiality, we use lemma
      [early_hep_job_is_scheduled]. Clearly, under the EDF priority
      policy, jobs satisfy the conditions described by the lemma
      (i.e., given two jobs [j1] and [j2] from the same task, if [j1]
      arrives earlier than [j2], then [j1] always has a higher
      priority than job [j2], and hence completes before [j2]);
      therefore EDF implies sequential tasks. *)
  Lemma EDF_implies_sequential_tasks :
    sequential_tasks arr_seq sched.
  Proof.
    move => j1 j2 t ARR1 ARR2 SAME LT.
    apply: early_hep_job_is_scheduled => //.
    rewrite always_higher_priority_jlfp !hep_job_arrival_edf //.
    - by rewrite -ltnNge; apply/andP; split => //.
    - by rewrite same_task_sym.
  Qed.

End SequentialEDF.
