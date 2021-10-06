Require Export prosa.analysis.definitions.always_higher_priority.
Require Export prosa.analysis.facts.busy_interval.priority_inversion.

(** In this section, we prove that, given two jobs [j1] and [j2], if
    job [j1] arrives earlier than job [j2] and [j1] always has higher
    priority than [j2], then [j2] is scheduled only after [j1] is
    completed. *) 
Section SequentialJLFP.  

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

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is transitive. *)             
  Context `{JLFP_policy Job}.
  Hypothesis H_priority_is_transitive : transitive_priorities.
  
  (** Next, consider any ideal uni-processor schedule of this arrival sequence, ... *)
  Variable sched : schedule (ideal.processor_state Job).
  
  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context `{@JobReady Job (ideal.processor_state Job) _ Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  
  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Next, we assume that the schedule respects the policy defined by
     the [job_preemptable] function (i.e., jobs have bounded
     non-preemptive segments). *)
  Hypothesis H_respects_policy : respects_policy_at_preemption_point arr_seq sched.
  
  (** We show that, given two jobs [j1] and [j2], if job [j1] arrives
      earlier than job [j2] and [j1] always has higher priority than
      [j2], then [j2] is scheduled only after [j1] is completed. *) 
  Lemma early_hep_job_is_scheduled : 
    forall j1 j2,
      arrives_in arr_seq j1 -> 
      job_arrival j1 < job_arrival j2 -> 
      always_higher_priority j1 j2 ->
      forall t,
        scheduled_at sched j2 t ->
        completed_by sched j1 t.
  Proof.
    move=> j1 j2 ARR LE AHP t SCHED; apply/negPn/negP; intros NCOMPL.
    move: H_sched_valid => [COARR MBR].
    have ARR_EXEC := jobs_must_arrive_to_be_ready sched MBR. 
    edestruct scheduling_of_any_segment_starts_with_preemption_time
      as [pt [LET [PT ALL_SCHED]]]; try eauto 2.
    move: LET => /andP [LE1 LE2].
    specialize (ALL_SCHED pt); feed ALL_SCHED; first by apply/andP; split.
    have PEND1: pending sched j1 pt.
    { apply/andP; split.
      - by rewrite /has_arrived; ssrlia.
      - by move: NCOMPL; apply contra, completion_monotonic.
    }
    apply H_job_ready in PEND1 => //; destruct PEND1 as [j3 [ARR3 [READY3 HEP3]]].
    move: (AHP pt) => /andP[HEP /negP NHEP]; eapply NHEP.
    eapply H_priority_is_transitive; last by apply HEP3.
    eapply H_respects_policy; eauto 2.
    apply/andP; split; first by done.
    apply/negP; intros SCHED2.
    have EQ := ideal_proc_model_is_a_uniprocessor_model _ _ _ pt SCHED2 ALL_SCHED.
    subst j2; rename j3 into j.
    by specialize (AHP 0); destruct AHP; auto.
  Qed.

End SequentialJLFP.
