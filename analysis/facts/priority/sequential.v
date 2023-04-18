Require Export prosa.analysis.definitions.always_higher_priority.
Require Export prosa.analysis.definitions.work_bearing_readiness.
Require Export prosa.analysis.facts.model.preemption.

(** In this section, we prove that, given two jobs [j1] and [j2], if
    job [j1] arrives earlier than job [j2] and [j1] always has higher
    priority than [j2], then [j2] is scheduled only after [j1] is
    completed. *)
Section SequentialJLFP.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Consider any arrival sequence with consistent arrival times. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Allow for any uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** Next, consider any schedule of the arrival sequence, ... *)
  Variable sched : schedule PState.

  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context `{@JobReady Job PState Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** Next, we assume that the schedule respects the scheduling policy at every preemption point.... *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** ... and that jobs must arrive to execute. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

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
    move=> j1 j2 ARR LE AHP t SCHED.
    apply/negPn/negP; intros NCOMPL.
    edestruct scheduling_of_any_segment_starts_with_preemption_time
      as [pt [LET [PT ALL_SCHED]]] => //.
    move: LET => /andP [LE1 LE2].
    specialize (ALL_SCHED pt); feed ALL_SCHED; first by apply/andP; split.
    have PEND1: pending sched j1 pt.
    { apply/andP; split.
      - by rewrite /has_arrived; lia.
      - by move: NCOMPL; apply contra, completion_monotonic. }
    have [j3 [ARR3 [READY3 HEP3]]] :=  (H_job_ready _ _ ARR PEND1).
    move: (AHP pt) => /andP[HEP /negP NHEP]; eapply NHEP.
    apply: H_priority_is_transitive; last exact: HEP3.
    apply: H_respects_policy => //.
    apply/andP; split => //.
    apply/negP => SCHED2.
    have EQ: j2 = j3 by apply: H_uniproc; eauto.
    by subst j2.
  Qed.

End SequentialJLFP.
