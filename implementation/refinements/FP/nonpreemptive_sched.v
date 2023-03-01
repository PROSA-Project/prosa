Require Export prosa.analysis.facts.preemption.task.nonpreemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.
Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.definitions.tardiness.
Require Export prosa.implementation.facts.ideal_uni.prio_aware.
Require Export prosa.implementation.definitions.task.

(** ** Fully-Nonpreemptive Fixed-Priority Schedules  *)

(** In this section, we prove some facts about the fully-nonpreemptive
    preemption policy under fixed-priority schedules.

    Some lemmas in this file are not novel facts; they are used to uniform
    POET's certificates and minimize their verbosity. *)
Section Schedule.

  (** In this file, we adopt the Prosa standard implementation of jobs and tasks. *)
  Definition Task := [eqType of concrete_task].
  Definition Job := [eqType of concrete_job].

  (** Consider any arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... assume sequential readiness, ... *)
  Instance sequential_ready_instance : JobReady Job (ideal.processor_state Job) :=
    sequential_ready_instance arr_seq.

  (** ... and consider any fully-nonpreemptive, fixed-priority schedule. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.
  #[local] Existing Instance NumericFPAscending.
  Definition sched := uni_schedule arr_seq.

  (** First, we show that only ready jobs execute. *)
  Lemma sched_jobs_must_be_ready_to_execute :
    jobs_must_be_ready_to_execute sched.
  Proof.
    move=> j t SCHED.
    apply jobs_must_be_ready => //.
    - move=> tt ss jj IN.
      rewrite  /choose_highest_prio_job in IN.
      by apply supremum_in in IN.
    - by apply sequential_readiness_nonclairvoyance.
  Qed.

  (** Next, we remark that such a schedule is valid. *)
  Remark sched_valid :
    valid_schedule sched arr_seq.
  Proof.
    split.
    - apply np_schedule_jobs_from_arrival_sequence.
      by move=> t ???; eapply (supremum_in (hep_job_at t)).
    - by apply sched_jobs_must_be_ready_to_execute.
  Qed.

  (** Next, we show that an unfinished job scheduled at time [t] is
      always scheduled at time [t+1] as well. Note that the validity of
      this fact also depends on which readiness model is used. *)
  Lemma sched_nonpreemptive_next:
    forall j t,
      scheduled_at sched j t ->
      ~~ completed_by sched j t.+1 ->
      scheduled_at sched j t.+1.
  Proof.
    move=> j t SCHED NCOMP.
    have READY: job_ready sched j t by apply sched_jobs_must_be_ready_to_execute.
    move: READY => /andP[/andP[ARR NC] /allP PRIOR].
    have SZ: 0 < service sched j t.+1.
    { apply scheduled_implies_nonzero_service; last  by simpl; exists t; split.
      by apply ideal_proc_model_ensures_ideal_progress. }
    have SC: service sched j t.+1 < job_cost j by apply less_service_than_cost_is_incomplete.
    move: SCHED NCOMP; rewrite !scheduled_at_def /sched /uni_schedule /pmc_uni_schedule
                               /generic_schedule => /eqP SCHED NCOMP.
    rewrite schedule_up_to_def {1}/allocation_at ifT; first by rewrite SCHED.
    rewrite /prev_job_nonpreemptive SCHED /job_preemptable /fully_nonpreemptive_job_model.
    move: SC SZ; rewrite /uni_schedule /pmc_uni_schedule /generic_schedule.
    set chp:= choose_highest_prio_job; set sut:= schedule_up_to.
    replace (_ (_ (_ _ _) _ t) j t.+1) with (service sched j t.+1); last first.
    { rewrite /uni_schedule /pmc_uni_schedule /generic_schedule /service
              /service_during /service_at; apply eq_big_nat => i H.
      replace (_ (_ _ _) _ t i) with (sut (allocation_at arr_seq chp) None i i) => //.
      by apply schedule_up_to_prefix_inclusion. }
    move=> SC SZ; apply /andP.
    split; last by apply /norP; split; [rewrite -lt0n|move:SC; rewrite ltn_neqAle=> /andP[??]].
    apply /andP; split; [apply /andP; split; [by unfold has_arrived in *; lia|]|].
    { unfold completed_by in *; rewrite <- ltnNge in *.
      replace (_ _ j _) with (service (fun t=> sut (allocation_at arr_seq chp) None t t) j t.+1)=> //.
      rewrite /service /service_during //=; apply eq_big_nat.
      move=> t' /andP[GEQ0 LEQt]; rewrite /service_at.
      replace (_ _  _ _ _) with (sut (allocation_at arr_seq chp) None t t')=> //.
      by symmetry; apply schedule_up_to_prefix_inclusion; lia. }
    { apply /allP => j' IN; apply (leq_trans (PRIOR j' IN)).
      rewrite /service /service_during big_nat_recr //= -(addn0  (\sum_(0 <= _ < t) _)).
      apply leq_add => //; apply eq_leq, eq_big_nat.
      move=> t' /andP[GEQ0 LEQt].
      rewrite /service_at /sched /uni_schedule /pmc_uni_schedule /generic_schedule.
      replace (_ (_ _ _) _ t' t') with (sut (allocation_at arr_seq chp) None t t') => //.
      by symmetry; apply schedule_up_to_prefix_inclusion; lia. }
  Qed.

  (** Using the lemma above, we show that the schedule is nonpreemptive. *)
  Lemma sched_nonpreemptive :
    nonpreemptive_schedule (uni_schedule arr_seq).
  Proof.
    rewrite /nonpreemptive_schedule.
    move=> j t; elim=> [|t' IHt']; first by move=> t'; have->: t = 0 by lia.
    move=> LEQ SCHED NCOMP.
    destruct (ltngtP t t'.+1) as [LT | _ | EQ] => //; last by rewrite -EQ.
    feed_n 3 IHt'=> //.
    { specialize (completion_monotonic sched j t' t'.+1) => MONO.
      feed MONO; first by lia.
      by apply contra in MONO. }
    by apply sched_nonpreemptive_next.
  Qed.

  (** Finally, we show that the fixed-priority policy is respected at each preemption point. *)
  Lemma respects_policy_at_preemption_point_np :
    respects_FP_policy_at_preemption_point arr_seq sched (NumericFPAscending Task).
  Proof.
    apply schedule_respects_policy; rt_eauto.
    by apply sequential_readiness_nonclairvoyance.
  Qed.

End Schedule.
