Require Export prosa.model.task.preemption.parameters.
Require Export prosa.analysis.facts.model.preemption.
Require Export prosa.analysis.facts.busy_interval.hep_at_pt.

(** * Priority Inversion in a Busy Interval *)
(** In this module, we reason about priority inversion that occurs during a busy
    interval due to non-preemptive sections. *)
Section PriorityInversionIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and any uniprocessor schedule of this arrival sequence. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uni : uniprocessor_model PState.
  Variable sched : schedule PState.

  (** Consider a JLFP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Consider a valid preemption model with known maximum non-preemptive
      segment lengths. *)
  Context `{TaskMaxNonpreemptiveSegment Task} `{JobPreemptable Job}.
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** Further, allow for any work-bearing notion of job readiness. *)
  Context `{!JobReady Job PState}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** We assume that the schedule is valid ... *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** ... and that the schedule respects the scheduling policy at every
      preemption point. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Consider any job [j] of [tsk] with positive job cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval_prefix :
    busy_interval_prefix arr_seq sched j t1 t2.

  (** ** Lower Priority In Busy Intervals *)
  (** First, we state some basic properties about a lower priority job executing
      in the busy interval of the job under consideration. From the definition
      of the busy interval it follows that a lower priority job can only be
      executing inside the busy interval as a result of priority inversion. *)
  Section LowerPriorityJobScheduled.

    (** Consider a lower-priority job. *)
    Variable jlp : Job.
    Hypothesis H_jlp_lp : ~~hep_job jlp j.

    (** Consider an instant [t] within the busy window of the job such that
        [jlp] is scheduled at [t]. *)
    Variable t : instant.
    Hypothesis H_t_in_busy : t1 <= t < t2.
    Hypothesis H_jlp_scheduled_at_t : scheduled_at sched jlp t.

    (** First, we prove that no time from [t1] up to the instant [t] can
        be a preemption point. *)
    Lemma lower_priority_job_scheduled_implies_no_preemption_time :
      forall t',
        t1 <= t' <= t ->
        ~~ preemption_time arr_seq sched t'.
    Proof.
      move => t' /andP[LE1 GT1].
      apply /negP => PT.
      move: H_jlp_lp => /negP LP; apply: LP.
      have [ptst [IN1 [PTT STT]]] :
        exists ptst : nat,
          t' <= ptst <= t /\ preemption_time arr_seq sched ptst /\ scheduled_at sched jlp ptst.
      { by apply: scheduling_of_any_segment_starts_with_preemption_time_continuously_sched => //=. }
      apply: (scheduled_at_preemption_time_implies_higher_or_equal_priority arr_seq _ sched _ _ _ _ j _ _ t1 t2 _ ptst)  => //.
      by lia.
    Qed.

    (** Then it follows that the job must have been continuously scheduled from
        [t1] up to [t]. *)
    Lemma lower_priority_job_continuously_scheduled :
      forall t',
        t1 <= t' <= t ->
        scheduled_at sched jlp t'.
    Proof.
      move => t' IN.
      move : IN => /andP [IN1' IN2'].
      apply: neg_pt_scheduled_continuously_after => //.
      move => ??.
      apply lower_priority_job_scheduled_implies_no_preemption_time.
      by lia.
    Qed.

    (** Any lower-priority jobs that are scheduled inside the
        busy-interval prefix <<[t1,t2)>> must arrive before that interval. *)
    Lemma low_priority_job_arrives_before_busy_interval_prefix :
      job_arrival jlp < t1.
    Proof.
      have SCHED1 : scheduled_at sched jlp t1.
      { apply lower_priority_job_continuously_scheduled => //. lia. }
      have ARR1: job_arrival jlp <= t1 by apply: (has_arrived_scheduled sched jlp _ t1 SCHED1).
      rewrite /has_arrived leq_eqVlt in ARR1.
      move : ARR1 => /orP[/eqP EQ| ?]; last by done.
      exfalso.
      have PP := scheduling_of_any_segment_starts_with_preemption_time _
                   arr_seq H_valid_arrivals
                   sched H_sched_valid
                   H_valid_preemption_model jlp t H_jlp_scheduled_at_t.
      feed PP => //.
      move: PP => [pt [/andP [NEQ1 NEQ2] [PT FA]]].
      contradict PT.
      apply /negP.
      by apply (lower_priority_job_scheduled_implies_no_preemption_time ) => //=; lia.
    Qed.

    (** Finally, we show that lower-priority jobs that are scheduled
        inside the busy-interval prefix <<[t1,t2)>> must also be scheduled
        before the interval. *)
    Lemma low_priority_job_scheduled_before_busy_interval_prefix :
      exists t', t' < t1 /\ scheduled_at sched jlp t'.
    Proof.
      move: H_t_in_busy => /andP [GE LT].
      have ARR := low_priority_job_arrives_before_busy_interval_prefix .
      exists t1.-1; split.
      { by rewrite prednK; last apply leq_ltn_trans with (job_arrival jlp). }
      eapply neg_pt_scheduled_at => //.
      - rewrite prednK; last by apply leq_ltn_trans with (job_arrival jlp).
        apply lower_priority_job_continuously_scheduled => //. lia.
      - rewrite prednK; last by apply leq_ltn_trans with (job_arrival jlp).
        apply lower_priority_job_scheduled_implies_no_preemption_time.
        by lia.
    Qed.

  End LowerPriorityJobScheduled.

  (** In this section, we identify sufficient conditions under which
      lower-priority jobs are not scheduled during the busy interval
      prefix of job [j]. *)
  Section LowerPriorityJobNotScheduled.

    (** Consider a lower-priority job [jlp]. *)
    Variable jlp : Job.
    Hypothesis H_jlp_lower_priority : ~~ hep_job jlp j.

    (** If a lower-priority job [jlp] arrives during the busy interval
        prefix <<[t1, t2)>>, then it is not scheduled at any earlier
        time [t] within the prefix. *)
    Corollary lp_job_should_arrive_early_for_pi :
      forall t t_arr,
        (jlp \in arrivals_between arr_seq t1 t_arr) ->
        t_arr <= t2 ->
        t1 <= t < t_arr ->
        ~~ scheduled_at sched jlp t.
    Proof.
      move=> t t_arr IN LE NEQ.
      apply/negP => SCHED.
      eapply low_priority_job_arrives_before_busy_interval_prefix in SCHED => //; last lia.
      apply in_arrivals_implies_arrived_between in IN => //.
      move: IN => /andP [IN1 IN2].
      by lia.
    Qed.

    (** If there is no priority inversion at the beginning of the busy
        interval prefix, then no lower-priority job [jlp] is scheduled
        at any time in <<[t1, t2)>>. *)
    Corollary lower_priority_jobs_never_scheduled_if_no_inversion :
      forall t,
        t1 <= t < t2 ->
        ~~ priority_inversion arr_seq sched j t1 ->
        ~~ scheduled_at sched jlp t.
    Proof.
      move=> t NEQ NPI; apply/negP => SCHED; move: (SCHED) => SCHEDt1.
      eapply lower_priority_job_continuously_scheduled with (t' := t1) in SCHEDt1 ; eauto 1; last by lia.
      move: SCHED SCHEDt1 => _ SCHED; move: NPI => /negP NPI; apply: NPI.
      apply/andP; split.
      { rewrite mem_filter negb_and; apply/orP; left; apply/negP => SCHEDj.
        have EQ: j = jlp by apply: H_uni => //.
        by subst; move: H_jlp_lower_priority => /negP LP; apply LP, H_priority_is_reflexive.
      }
      apply/hasP; exists jlp; last by done.
      by rewrite mem_filter SCHED //=; apply: arrivals_up_to_scheduled_at.
    Qed.

  End LowerPriorityJobNotScheduled.

  (** In this section, we prove that priority inversion only
      occurs at the start of the busy window and occurs due to only
      one job. *)
  Section SingleJob.

    (** Suppose job [j] incurs priority inversion at a time [t_pi] in its busy window. *)
    Variable t_pi : instant.
    Hypothesis H_from_t1_before_t2 : t1 <= t_pi < t2.
    Hypothesis H_PI_occurs : priority_inversion arr_seq sched j t_pi.

    (** First, we show that there is no preemption time in the interval <<[t1,t_pi]>>. *)
    Lemma no_preemption_time_before_pi :
      forall t,
        t1 <= t <= t_pi ->
        ~~ preemption_time arr_seq sched t.
    Proof.
      move => ppt intl.
      move : H_PI_occurs => /uni_priority_inversion_P PI.
      feed_n 5 PI => //=.
      move : PI => [jlp SCHED NHEP].
      by apply (lower_priority_job_scheduled_implies_no_preemption_time jlp NHEP t_pi).
    Qed.

    (** Next, we show that the same job will be scheduled from the start of the
        busy interval to the priority inversion time [t_pi]. *)
    Lemma pi_job_remains_scheduled :
      forall jlp,
        scheduled_at sched jlp t_pi ->
        forall t,
          t1 <= t <= t_pi -> scheduled_at sched jlp t.
    Proof.
      move : H_PI_occurs => /uni_priority_inversion_P PI.
      feed_n 5 PI => //=.
      move : PI => [jlp SCHED NHEP].
      move => jlp1 SCHED3 t IN.
      apply: lower_priority_job_continuously_scheduled => //.
      by have -> : jlp1 = jlp.
    Qed.

    (** Thus, priority inversion takes place from the start of the busy interval
        to the instant [t_pi], i.e., priority inversion takes place
        continuously. *)
    Lemma pi_continuous :
      forall t,
        t1 <= t <= t_pi ->
        priority_inversion arr_seq sched j t.
    Proof.
      move: (H_PI_occurs) => /andP[j_nsched_pi /hasP[jlp jlp_sched_pi nHEPj]] t INTL.
      apply /uni_priority_inversion_P => // ; exists jlp => //.
      apply: pi_job_remains_scheduled => //.
      by rewrite -(scheduled_jobs_at_iff arr_seq).
    Qed.

  End SingleJob.

  (** As a simple corollary to the lemmas proved in the previous
      section, we show that for any two jobs [j1] and [j2] that cause
      priority inversion to job [j], it is the case that [j1 = j2]. *)
  Section SingleJobEq.

    (** Consider a time instant [ts1] in <<[t1, t2)>> ... *)
    Variable ts1 : instant.
    Hypothesis H_ts1_in_busy_prefix : t1 <= ts1 < t2.

    (** ... and a lower-priority (w.r.t. job [j]) job [j1] that is
        scheduled at time [ts1]. *)
    Variable j1 : Job.
    Hypothesis H_j1_sched : scheduled_at sched j1 ts1.
    Hypothesis H_j1_lower_prio : ~~ hep_job j1 j.

    (** Similarly, consider a time instant [ts2] in <<[t1, t2)>> ... *)
    Variable ts2 : instant.
    Hypothesis H_ts2_in_busy_prefix : t1 <= ts2 < t2.

    (** ... and a lower-priority job [j2] that is scheduled at time [ts2]. *)
    Variable j2 : Job.
    Hypothesis H_j2_sched : scheduled_at sched j2 ts2.
    Hypothesis H_j2_lower_prio : ~~ hep_job j2 j.

    (** Then, [j1] is equal to [j2]. *)
    Corollary only_one_pi_job :
      j1 = j2.
    Proof.
      have [NEQ|NEQ] := leqP ts1 ts2.
      { apply: H_uni; first by apply H_j1_sched.
        apply: pi_job_remains_scheduled; try apply H_j2_sched; try lia.
        by erewrite priority_inversion_hep_job.
      }
      { apply: H_uni; last by apply H_j2_sched.
        apply: pi_job_remains_scheduled; try apply H_j1_sched; try lia.
        by erewrite priority_inversion_hep_job; try apply H_j1_sched.
      }
    Qed.

  End SingleJobEq.

  (** From the above lemmas, it follows that either job [j] incurs no priority
      inversion at all or certainly at time [t1], i.e., the beginning of its
      busy interval. *)
  Lemma busy_interval_pi_cases :
    cumulative_priority_inversion arr_seq sched j t1 t2 = 0
    \/ priority_inversion arr_seq sched j t1.
  Proof.
    case: (posnP (cumulative_priority_inversion arr_seq sched j t1 t2)); first by left.
    rewrite sum_nat_gt0 // => /hasP[pi].
    rewrite mem_filter /= mem_index_iota lt0b => INTL PI_pi.
    by right; apply: pi_continuous =>//; lia.
  Qed.

  (** Next, we use the above facts to establish bounds on the maximum priority
      inversion that can be incurred in a busy interval. *)

  (** * Priority Inversion due to Non-Preemptive Sections *)

  (** First, we introduce the notion of the maximum length of a
      nonpreemptive segment among all lower priority jobs (w.r.t. a
      given job [j]) arrived so far. *)
  Definition max_lp_nonpreemptive_segment (j : Job) (t : instant) :=
    \max_(j_lp <- arrivals_before arr_seq t | (~~ hep_job j_lp j) && (job_cost j_lp > 0))
      (job_max_nonpreemptive_segment j_lp - ε).

  (** Note that any bound on the [max_lp_nonpreemptive_segment]
      function is also be a bound on the maximum priority inversion
      (assuming there are no other mechanisms that could cause
      priority inversion). This bound may be different for different
      scheduler and/or task models. Thus, we don't define such a bound
      in this module. *)

  Section TaskMaxNPS.

    (** First, assuming proper non-preemptive sections, ... *)
    Hypothesis H_valid_nps :
      valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

    (** ... we observe that the maximum non-preemptive segment length
        of any task that releases a job with lower priority (w.r.t. a
        given job [j]) and non-zero execution cost upper-bounds the
        maximum possible non-preemptive segment length of any
        lower-priority job. *)
    Lemma max_np_job_segment_bounded_by_max_np_task_segment :
      max_lp_nonpreemptive_segment j t1
      <= \max_(j_lp <- arrivals_between arr_seq 0 t1 | (~~ hep_job j_lp j)
                                                     && (job_cost j_lp > 0))
          (task_max_nonpreemptive_segment (job_task j_lp) - ε).
    Proof.
      rewrite /max_lp_nonpreemptive_segment.
      apply: leq_big_max => j' JINB NOTHEP.
      rewrite leq_sub2r //.
      apply in_arrivals_implies_arrived in JINB.
      by apply H_valid_nps.
    Qed.

  End TaskMaxNPS.

  (** Next, we prove that the function [max_lp_nonpreemptive_segment]
      indeed upper-bounds the priority inversion length. *)
  Section PreemptionTimeExists.

    (** In this section, we require the jobs to have valid bounded
        non-preemptive segments. *)
    Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
      valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

    (** First, we prove that, if a job with higher-or-equal priority is scheduled at
        a quiet time [t+1], then this is the first time when this job is scheduled. *)
    Lemma hp_job_not_scheduled_before_quiet_time :
      forall jhp t,
        quiet_time arr_seq sched j t.+1 ->
        scheduled_at sched jhp t.+1 ->
        hep_job jhp j ->
        ~~ scheduled_at sched jhp t.
    Proof.
      intros jhp t QT SCHED1 HP.
      apply/negP; intros SCHED2.
      specialize (QT jhp).
      feed_n 3 QT => //.
      - have MATE: jobs_must_arrive_to_execute sched by [].
        by have HA: has_arrived jhp t by exact: MATE.
      - apply completed_implies_not_scheduled in QT => //.
        by move: QT => /negP NSCHED; apply: NSCHED.
    Qed.

    (** Thus, there must be a preemption time in the interval [t1, t1
        + max_lp_nonpreemptive_segment j t1]. That is, if a job with
        higher-or-equal priority is scheduled at time instant [t1],
        then [t1] is a preemption time. Otherwise, if a job with lower
        priority is scheduled at time [t1], then this job also should
        be scheduled before the beginning of the busy interval. So,
        the next preemption time will be no more than
        [max_lp_nonpreemptive_segment j t1] time units later. *)

    (** We proceed by doing a case analysis. *)
    Section CaseAnalysis.

      (** (1) Case when the schedule is idle at time [t1]. *)
      Section Case1.

        (** Assume that the schedule is idle at time [t1]. *)
        Hypothesis H_is_idle : is_idle arr_seq sched t1.

        (** Then time instant [t1] is a preemption time. *)
        Lemma preemption_time_exists_case1 :
          exists pr_t,
            preemption_time arr_seq sched pr_t
            /\ t1 <= pr_t <= t1 + max_lp_nonpreemptive_segment j t1.
        Proof.
          set (service := service sched).
          move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
          move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
          exists t1; split.
          - exact: idle_time_is_pt.
          - by apply/andP; split; last rewrite leq_addr.
        Qed.

      End Case1.

      (** (2) Case when a job with higher-or-equal priority is scheduled at time [t1]. *)
      Section Case2.

        (** Assume that a job [jhp] with higher-or-equal priority is scheduled at time [t1]. *)
        Variable jhp : Job.
        Hypothesis H_jhp_is_scheduled : scheduled_at sched jhp t1.
        Hypothesis H_jhp_hep_priority : hep_job jhp j.

        (** Then time instant [t1] is a preemption time. *)
        Lemma preemption_time_exists_case2 :
          exists pr_t,
            preemption_time arr_seq sched pr_t
            /\ t1 <= pr_t <= t1 + max_lp_nonpreemptive_segment j t1.
        Proof.
          set (service := service sched).
          move :  (H_valid_model_with_bounded_nonpreemptive_segments) =>  [VALID BOUNDED].
          move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
          move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
          exists t1; split; last by apply/andP; split; [|rewrite leq_addr].
          destruct t1.
          - exact: zero_is_pt.
          - apply: first_moment_is_pt H_jhp_is_scheduled => //.
            exact: hp_job_not_scheduled_before_quiet_time.
        Qed.

      End Case2.

      (** The following argument requires a unit-service assumption. *)
      Hypothesis H_unit : unit_service_proc_model PState.

      (** (3) Case when a job with lower priority is scheduled at time [t1]. *)
      Section Case3.

        (** Assume that a job [jhp] with lower priority is scheduled at time [t1]. *)
        Variable jlp : Job.
        Hypothesis H_jlp_is_scheduled : scheduled_at sched jlp t1.
        Hypothesis H_jlp_low_priority : ~~ hep_job jlp j.

        (** To prove the lemma in this case we need a few auxiliary
            facts about the first preemption point of job [jlp]. *)
        Section FirstPreemptionPointOfjlp.

          (** Let's denote the progress of job [jlp] at time [t1] as [progr_t1]. *)
          Let progr_t1 := service sched jlp t1.

          (** Consider the first preemption point of job [jlp] after [progr_t1]. *)
          Variable fpt : instant.
          Hypothesis H_fpt_is_preemption_point : job_preemptable jlp (progr_t1 + fpt).
          Hypothesis H_fpt_is_first_preemption_point :
            forall ρ,
              progr_t1 <= ρ <= progr_t1 + (job_max_nonpreemptive_segment jlp - ε) ->
              job_preemptable jlp ρ ->
              service sched jlp t1 + fpt <= ρ.

          (** For correctness, we also assume that [fpt] does not
              exceed the length of the maximum non-preemptive
              segment. *)
          Hypothesis H_progr_le_max_nonp_segment :
            fpt <= job_max_nonpreemptive_segment jlp - ε.

          (** First we show that [fpt] is indeed the first preemption point after [progr_t1]. *)
          Lemma no_intermediate_preemption_point :
            forall ρ,
              progr_t1 <= ρ < progr_t1 + fpt ->
              ~~ job_preemptable jlp ρ.
          Proof.
            move => prog /andP [GE LT].
            apply/negP; intros PPJ.
            move: H_fpt_is_first_preemption_point => K; specialize (K prog).
            feed_n 2 K => [|//|]; first (apply/andP; split=> //).
            { apply leq_trans with (service sched jlp t1 + fpt).
              + exact: ltnW.
              + by rewrite leq_add2l; apply H_progr_le_max_nonp_segment.
            }
            by move: K; rewrite leqNgt => /negP NLT; apply: NLT.
          Qed.

          (** Thanks to the fact that the scheduler respects the notion of preemption points
              we show that [jlp] is continuously scheduled in time interval <<[t1, t1 + fpt)>>. *)
          Lemma continuously_scheduled_between_preemption_points :
            forall t',
              t1 <= t' < t1 + fpt ->
              scheduled_at sched jlp t'.
          Proof.
            move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
            have ARRs : arrives_in arr_seq jlp by [].
            move => t' /andP [GE LT].
            have Fact: exists Δ, t' = t1 + Δ.
            { by exists (t' - t1); apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC. }
            move: Fact => [Δ EQ]; subst t'.
            have NPPJ := @no_intermediate_preemption_point (@service _ _ sched jlp (t1 + Δ)).
            apply proj1 in CORR; specialize (CORR jlp ARRs).
            move: CORR => [_ [_ [T _] ]].
            apply T; apply: NPPJ; apply/andP; split.
            { by apply service_monotonic; rewrite leq_addr. }
            rewrite /service  -(service_during_cat _ _ _ t1).
            { rewrite ltn_add2l; rewrite ltn_add2l in LT.
              apply leq_ltn_trans with Δ => [|//].
              rewrite -{2}(sum_of_ones t1 Δ).
              by rewrite leq_sum. }
            { by apply/andP; split; [|rewrite leq_addr]. }
          Qed.

          (** Thus, assuming an ideal-progress processor model, job [jlp]
              reaches its preemption point at time instant [t1 + fpt], which
              implies that time instant [t1 + fpt] is a preemption time. *)
          Lemma first_preemption_time :
            ideal_progress_proc_model PState ->
            preemption_time arr_seq sched (t1 + fpt).
          Proof.
            move=> H_progress.
            have [IDLE|[j' SCHED']] :=
              scheduled_at_cases _ H_valid_arrivals sched ltac:(by []) ltac:(by []) (t1 + fpt);
              first exact: idle_time_is_pt.
            have [EQ|NEQ] := (eqVneq jlp j').
            { move: (SCHED'); rewrite -(scheduled_job_at_scheduled_at arr_seq) // -EQ /preemption_time => /eqP ->.
              rewrite  /service -(service_during_cat _ _ _ t1); last first.
              { by apply/andP; split; last rewrite leq_addr. }
              have ->: service_during sched jlp t1 (t1 + fpt) = fpt => //.
              { rewrite -{2}(sum_of_ones t1 fpt) /service_during.
                apply/eqP; rewrite eqn_leq //; apply/andP; split.
                + by rewrite leq_sum.
                + rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
                  rewrite leq_sum //.
                  move => x /andP [HYP _].
                  exact/H_progress/continuously_scheduled_between_preemption_points. } }
            { case: (posnP fpt) => [ZERO|POS].
              { subst fpt; rewrite addn0 in SCHED'.
                exfalso; move: NEQ => /negP; apply; apply/eqP.
                exact: H_uni. }
              { have [sm EQ2]: exists sm, sm.+1 = fpt by exists fpt.-1; rewrite prednK.
                move: SCHED'; rewrite -EQ2 addnS => SCHED'.
                apply:  first_moment_is_pt (SCHED') => //.
                apply: scheduled_job_at_neq => //.
                apply: (continuously_scheduled_between_preemption_points (t1 + sm)).
                by apply/andP; split; [rewrite leq_addr | rewrite -EQ2 addnS]. } }
          Qed.

          (** And since [fpt <= max_lp_nonpreemptive_segment j t1],
              [t1 <= t1 + fpt <= t1 + max_lp_nonpreemptive_segment j t1]. *)
          Lemma preemption_time_le_max_len_of_np_segment :
            t1 <= t1 + fpt <= t1 + max_lp_nonpreemptive_segment j t1.
          Proof.
            have ARRs : arrives_in arr_seq jlp by [].
            apply/andP; split; first by rewrite leq_addr.
            rewrite leq_add2l.
            unfold max_lp_nonpreemptive_segment.
            rewrite (big_rem jlp) //=.
            { rewrite H_jlp_low_priority //=.
              have NZ: service sched jlp t1 < job_cost jlp by exact: service_lt_cost.
              rewrite ifT; last lia.
              apply leq_trans with (job_max_nonpreemptive_segment jlp - ε).
              - by apply H_progr_le_max_nonp_segment.
              - by rewrite leq_maxl.
            }
            apply: arrived_between_implies_in_arrivals => [//|//|].
            apply/andP; split=> [//|].
            eapply low_priority_job_arrives_before_busy_interval_prefix with t1; eauto 2.
            by move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]]; apply/andP.
          Qed.

        End FirstPreemptionPointOfjlp.

        (** For the next step, we assume an ideal-progress processor. *)
        Hypothesis H_progress : ideal_progress_proc_model PState.

        (** Next, we combine the above facts to conclude the lemma. *)
        Lemma preemption_time_exists_case3 :
          exists pr_t,
            preemption_time arr_seq sched pr_t
            /\ t1 <= pr_t <= t1 + max_lp_nonpreemptive_segment j t1.
        Proof.
          set (service := service sched).
          have EX:
            exists pt,
              ((service jlp t1) <= pt <= (service jlp t1) + (job_max_nonpreemptive_segment jlp - 1))
              && job_preemptable jlp pt.
          { have ARRs: arrives_in arr_seq jlp by [].
            move: (proj2 (H_valid_model_with_bounded_nonpreemptive_segments) jlp ARRs) =>[_ EXPP].
            destruct H_sched_valid as [A B].
            specialize (EXPP (service jlp t1)).
            feed EXPP.
            { apply/andP; split=> [//|].
              exact: service_at_most_cost.
            }
            move: EXPP => [pt [NEQ PP]].
            by exists pt; apply/andP.
          }
          move: (ex_minnP EX) => [sm_pt /andP [NEQ PP] MIN]; clear EX.
          have Fact: exists Δ, sm_pt = service jlp t1 + Δ.
          { exists (sm_pt - service jlp t1).
            apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC //.
            by move: NEQ => /andP [T _]. }
          move: Fact => [Δ EQ]; subst sm_pt; rename Δ into sm_pt.
          exists (t1 + sm_pt); split.
          { apply first_preemption_time; rewrite /service.service//.
            + by intros; apply MIN; apply/andP; split.
            + by lia.
          }
          apply: preemption_time_le_max_len_of_np_segment => //.
          by lia.
        Qed.

      End Case3.

    End CaseAnalysis.

    (** As Case 3 depends on unit-service and ideal-progress assumptions, we
        require the same here. *)
    Hypothesis H_unit : unit_service_proc_model PState.
    Hypothesis H_progress : ideal_progress_proc_model PState.

    (** By doing the case analysis, we show that indeed there is a
        preemption time in the time interval [[t1, t1 +
        max_lp_nonpreemptive_segment j t1]]. *)
    Lemma preemption_time_exists :
      exists pr_t,
        preemption_time arr_seq sched pr_t
        /\ t1 <= pr_t <= t1 + max_lp_nonpreemptive_segment j t1.
    Proof.
      have [Idle|[s Sched_s]] :=
        scheduled_at_cases _ H_valid_arrivals sched ltac:(by []) ltac:(by []) t1.
      - by apply preemption_time_exists_case1.
      - destruct (hep_job s j) eqn:PRIO.
        + exact: preemption_time_exists_case2.
        + apply: preemption_time_exists_case3 => //.
          by rewrite -eqbF_neg; apply /eqP.
    Qed.

  End PreemptionTimeExists.

  (** In this section we prove that if a preemption point [ppt] exists in a job's busy window,
      it suffers no priority inversion after [ppt]. Equivalently the [cumulative_priority_inversion]
      of the job in the busy window <<[t1,t2]>> is bounded by the [cumulative_priority_inversion]
      of the job in the time window <<[t1, ppt)>>. *)
  Section NoPriorityInversionAfterPreemptionPoint.

    (** Consider the preemption point [ppt]. *)
    Variable ppt : instant.
    Hypothesis H_preemption_point : preemption_time arr_seq sched ppt.
    Hypothesis H_after_t1 : t1 <= ppt.

    (** We first establish the aforementioned result by showing that [j] cannot
        suffer priority inversion after the preemption time [ppt] ... *)
    Lemma no_priority_inversion_after_preemption_point :
      forall t,
        ppt <= t < t2 ->
        ~~ priority_inversion arr_seq sched j t.
    Proof.
      move=> t /andP [pptt tt2].
      apply /negP => PI.
      move: PI => /andP[j_nsched_pi /hasP[jlp jlp_sched_pi nHEPj]].
      have [/eqP SCHED1 //|[j' /eqP SCHED2 //=]] :=
        scheduled_jobs_at_uni_cases arr_seq ltac:(done) sched ltac:(done)
                                                                     ltac:(done) ltac:(done) t; first by rewrite SCHED1 in jlp_sched_pi.
      rewrite SCHED2 mem_seq1 in jlp_sched_pi.
      move : jlp_sched_pi => /eqP HJLP.
      replace j' with jlp in *; clear HJLP.
      move : SCHED2 => /eqP SCHED2.
      rewrite scheduled_jobs_at_scheduled_at in SCHED2 => //=.
      have [ptst [IN1 [PTT STT]]] :
        exists ptst : nat,
          ppt <= ptst <= t /\ preemption_time arr_seq sched ptst /\ scheduled_at sched jlp ptst.
      { by apply: scheduling_of_any_segment_starts_with_preemption_time_continuously_sched. }
       contradict nHEPj.
       apply /negP /negPn.
       apply: scheduled_at_preemption_time_implies_higher_or_equal_priority => //.
       by lia.
    Qed.

    (** ... and then lift this fact to cumulative priority inversion. *)
    Lemma priority_inversion_occurs_only_till_preemption_point :
      cumulative_priority_inversion arr_seq sched j t1 t2 <=
      cumulative_priority_inversion arr_seq sched j t1 ppt.
    Proof.
      have [LEQ|LT_t1t2] := leqP t1 t2;
        last by rewrite /cumulative_priority_inversion big_geq //; exact: ltnW.
      have [LEQ_t2ppt|LT] := leqP t2 ppt;
        first by rewrite (cumulative_priority_inversion_cat _ _ _ t2 t1 ppt) //
                 ; exact: leq_addr.
      move: (H_busy_interval_prefix) => [_ [_ [_ /andP [T _]]]].
      rewrite /cumulative_priority_inversion (@big_cat_nat _ _ _ ppt) //=.
      rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
      rewrite big_nat_cond big1 // => t /andP[/andP[GEt LEt] _].
      apply/eqP; rewrite eqb0.
      by apply/no_priority_inversion_after_preemption_point/andP.
    Qed.

  End NoPriorityInversionAfterPreemptionPoint.

End PriorityInversionIsBounded.
