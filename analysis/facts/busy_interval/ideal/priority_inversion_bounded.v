Require Export prosa.model.task.preemption.parameters.
Require Export prosa.analysis.facts.model.preemption.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.
Require Export prosa.analysis.facts.busy_interval.ideal.hep_job_scheduled.

(** * Priority inversion is bounded *)
(** In this file, we prove that any priority inversion that occurs in
    the model with bounded nonpreemptive segments is bounded. *)
Section PriorityInversionIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** Consider a JLFP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive: reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive: transitive_job_priorities JLFP.

  (** In addition, we assume the existence of a function mapping a
      task to its maximal non-preemptive segment ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and the existence of a function mapping a job and its
      progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.

  (** And assume that they define a valid preemption model with
     bounded nonpreemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Further, allow for any work-bearing notion of job readiness. *)
  Context `{@JobReady Job (ideal.processor_state Job) Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** We assume that the schedule is valid and that all jobs come from the arrival sequence. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and the schedule respects the scheduling policy at every preemption point. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Finally, we introduce the notion of the maximal length of
      (potential) priority inversion at a time instant [t], which is
      defined as the maximum length of nonpreemptive segments among
      all jobs that arrived so far. *)
  Definition max_length_of_priority_inversion (j : Job) (t : instant) :=
    \max_(j_lp <- arrivals_before arr_seq t | (~~ hep_job j_lp j) && (job_cost j_lp > 0))
     (job_max_nonpreemptive_segment j_lp - ε).

  (** Next we prove that a priority inversion of a job is bounded by
      function [max_length_of_priority_inversion]. *)

  (** Note that any bound on function
      [max_length_of_priority_inversion] will also be a bound on the
      maximal priority inversion. This bound may be different for
      different scheduler and/or task models. Thus, we don't define
      such a bound in this module. *)

  (** Consider any job [j] of [tsk] with positive job cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job j. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval_prefix:
    busy_interval_prefix arr_seq sched j t1 t2.

  (** * Processor Executes HEP jobs after Preemption Point *)
  (** In this section, we prove that at any time instant after any
      preemption point (inside the busy interval), the processor is
      always busy scheduling a job with higher or equal priority. *)
  Section PreemptionTimeAndPriorityInversion.

    (** First, recall from file [busy_interval/ideal/hep_job_scheduled]
        we already know that the processor at any preemptive point is always
        busy scheduling a job with higher or equal priority. *)

    (** We show that at any time instant after a preemption point the
        processor is always busy with a job with higher or equal
        priority. *)
    Lemma not_quiet_implies_exists_scheduled_hp_job_after_preemption_point:
      forall tp t,
        preemption_time arr_seq sched tp ->
        t1 <= tp < t2 ->
        tp <= t < t2 ->
        exists j_hp,
          arrived_between j_hp t1 t.+1 /\
          hep_job j_hp j /\
          scheduled_at sched j_hp t.
    Proof.
      move => tp t PRPOINT /andP [GEtp LTtp] /andP [LEtp LTt].
      have [Idle|[jhp Sched_jhp]] := ideal_proc_model_sched_case_analysis sched t.
      { by eapply instant_t_is_not_idle in Idle; rt_eauto;
        [ | apply/andP; split; first apply leq_trans with tp]. }
      exists jhp.
      have HP: hep_job jhp j.
      { intros.
        move:(H_valid_model_with_bounded_nonpreemptive_segments) => [PREE _].
        have PP := scheduling_of_any_segment_starts_with_preemption_time _
                     arr_seq  H_valid_arrivals
                     sched H_sched_valid PREE jhp t Sched_jhp.
        feed PP; rt_auto.
        move: PP => [prt [/andP [_ LE] [PR SCH]]].
        case E:(t1 <= prt).
        - move: E => /eqP /eqP E; rewrite subn_eq0 in E.
          edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point as [jlp [_ [HEP SCHEDjhp]]]; rt_eauto.
          { by apply /andP; split; last by apply leq_ltn_trans with t. }
          enough (EQ : jhp = jlp); first by subst.
          apply: (ideal_proc_model_is_a_uniprocessor_model _ _ _ prt); eauto;
            by apply SCH; apply/andP; split.
        - move: E => /eqP /neqP E; rewrite -lt0n subn_gt0 in E.
          apply negbNE; apply/negP; intros LP; rename jhp into jlp.
          edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
            as [jhp [_ [HEP SCHEDjhp]]]; try  apply PRPOINT; rt_eauto; first by apply/andP; split.
          move: LP => /negP LP; apply: LP.
          enough (EQ : jhp = jlp); first by subst.
          apply: (ideal_proc_model_is_a_uniprocessor_model jhp _ _ tp); eauto.
            by apply SCH; apply/andP; split; first apply leq_trans with t1; auto.
      }
      repeat split; try done.
      move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET EXj]]]; move: (Sched_jhp) => PENDING.
      eapply scheduled_implies_pending in PENDING; rt_eauto.
      apply/andP; split; last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _].
      apply contraT; rewrite -ltnNge; intro LT; exfalso.
      feed (QUIET jhp); first by eapply H_jobs_come_from_arrival_sequence, Sched_jhp.
      specialize (QUIET HP LT).
      have COMP: completed_by sched jhp t.
      { apply: completion_monotonic QUIET; exact: leq_trans LEtp. }
      apply completed_implies_not_scheduled in COMP; rt_eauto.
      by move : COMP => /negP COMP; apply : COMP.
    Qed.

    (** Now, suppose there exists some constant K that bounds the
        distance to a preemption time from the beginning of the busy
        interval. *)
    Variable K : duration.
    Hypothesis H_preemption_time_exists :
      exists pr_t, preemption_time arr_seq sched pr_t /\ t1 <= pr_t <= t1 + K.

    (** Then we prove that the processor is always busy with a job
        with higher-or-equal priority after time instant [t1 + K]. *)
    Lemma not_quiet_implies_exists_scheduled_hp_job:
      forall t,
        t1 + K <= t < t2 ->
        exists j_hp,
          arrived_between j_hp t1 t.+1 /\
          hep_job j_hp j /\
          scheduled_at sched j_hp t.
    Proof.
      move => t /andP [GE LT].
      move: H_preemption_time_exists => [prt [PR /andP [GEprt LEprt]]].
      apply not_quiet_implies_exists_scheduled_hp_job_after_preemption_point with (tp := prt); eauto 2.
      - apply/andP; split; first by done.
        apply leq_ltn_trans with (t1 + K); first by done.
        by apply leq_ltn_trans with t.
      - apply/andP; split; last by done.
        by apply leq_trans with (t1 + K).
    Qed.

  End PreemptionTimeAndPriorityInversion.

  (** * Preemption Time Exists *)
  (** In this section we prove that the function [max_length_of_priority_inversion]
      indeed upper-bounds the priority inversion length. *)
  Section PreemptionTimeExists.

    (** First, we prove that, if a job with higher-or-equal priority is scheduled at
        a quiet time [t+1], then this is the first time when this job is scheduled. *)
    Lemma hp_job_not_scheduled_before_quiet_time:
      forall jhp t,
        quiet_time arr_seq sched j t.+1 ->
        scheduled_at sched jhp t.+1 ->
        hep_job jhp j ->
        ~~ scheduled_at sched jhp t.
    Proof.
      intros jhp t QT SCHED1 HP.
      apply/negP; intros SCHED2.
      specialize (QT jhp).
      feed_n 3 QT; eauto.
      - have MATE: jobs_must_arrive_to_execute sched by rt_eauto.
        have HA: has_arrived jhp t by apply MATE.
        by done.
      apply completed_implies_not_scheduled in QT; rt_eauto.
      by move: QT => /negP NSCHED; apply: NSCHED.
    Qed.

    (** Also, we show that lower-priority jobs that are scheduled inside the
        busy-interval prefix <<[t1,t2)>> must arrive before that interval. *)
    Lemma low_priority_job_arrives_before_busy_interval_prefix:
      forall jlp t,
        t1 <= t < t2 ->
        scheduled_at sched jlp t ->
        ~~ hep_job jlp j ->
        job_arrival jlp < t1.
    Proof.
      move => jlp t /andP [GE LT] SCHED LP.
      move: (H_busy_interval_prefix) => [NEM [QT [NQT HPJ]]].
      apply negbNE; apply/negP; intros ARR; rewrite -leqNgt in ARR.
      move: (H_valid_model_with_bounded_nonpreemptive_segments) => [PREE ?].
      have PP := scheduling_of_any_segment_starts_with_preemption_time _
                   arr_seq H_valid_arrivals
                   sched H_sched_valid
                   PREE jlp t SCHED.
      feed PP; rt_auto.
      move: PP => [pt [/andP [NEQ1 NEQ2] [PT FA]]].
      have NEQ: t1 <= pt < t2.
      { apply/andP; split.
        - by apply leq_trans with (job_arrival jlp).
        - by apply leq_ltn_trans with t. }
      edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point as [jhp [_ [HEP SCHEDjhp]]]; rt_eauto.
      feed (FA pt); first (by apply/andP; split).
      move: LP => /negP LP; apply: LP.
      by have ->: jlp = jhp by eapply ideal_proc_model_is_a_uniprocessor_model; eauto.
    Qed.

    (** Moreover, we show that lower-priority jobs that are scheduled
        inside the busy-interval prefix <<[t1,t2)>> must be scheduled
        before that interval. *)
    Lemma low_priority_job_scheduled_before_busy_interval_prefix:
      forall jlp t,
        t1 <= t < t2 ->
        scheduled_at sched jlp t ->
        ~~ hep_job jlp j ->
        exists t', t' < t1 /\ scheduled_at sched jlp t'.
    Proof.
      move => jlp t NEQ SCHED LP; move: (NEQ) => /andP [GE LT].
      have ARR := low_priority_job_arrives_before_busy_interval_prefix _ _ NEQ SCHED LP.
      exists t1.-1; split.
      { by rewrite prednK; last apply leq_ltn_trans with (job_arrival jlp). }
      move: (H_busy_interval_prefix) => [NEM [QT [NQT HPJ]]].
      move: (H_valid_model_with_bounded_nonpreemptive_segments) => [PREE _].
      have PP := scheduling_of_any_segment_starts_with_preemption_time _
                   arr_seq H_valid_arrivals
                   sched H_sched_valid
                   PREE jlp t SCHED.
      feed PP; rt_auto.
      move: PP => [pt [NEQpt [PT SCHEDc]]].
      have LT2: pt < t1.
      { rewrite ltnNge; apply/negP; intros CONTR.
        edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
          as [jhp [_ [HEP SCHEDjhp]]]; try apply PT; rt_eauto; first lia.
        specialize (SCHEDc pt).
        feed SCHEDc; first by apply/andP; split; last move: NEQpt => /andP [_ T].
        move: LP => /negP LP; apply: LP.
        by have ->: jlp = jhp by eapply ideal_proc_model_is_a_uniprocessor_model; eauto.
      }
      apply SCHEDc; apply/andP; split.
      - by rewrite -add1n in LT2; apply leq_subRL_impl in LT2; rewrite subn1 in LT2.
      - by apply leq_trans with t1; first apply leq_pred.
    Qed.

    (** Thus, there must be a preemption time in the interval [t1, t1
        + max_priority_inversion t1]. That is, if a job with
        higher-or-equal priority is scheduled at time instant [t1], then
        [t1] is a preemption time. Otherwise, if a job with lower
        priority is scheduled at time [t1], then this job also should
        be scheduled before the beginning of the busy interval. So,
        the next preemption time will be no more than
        [max_priority_inversion t1] time units later. *)

    (** We proceed by doing a case analysis. *)
    Section CaseAnalysis.

      (** (1) Case when the schedule is idle at time [t1]. *)
      Section Case1.

        (** Assume that the schedule is idle at time [t1]. *)
        Hypothesis H_ideal_is_idle : ideal_is_idle sched t1.

        (** Then time instant [t1] is a preemption time. *)
        Lemma preemption_time_exists_case1:
          exists pr_t,
            preemption_time arr_seq sched pr_t /\
            t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
        Proof.
          set (service := service sched).
          move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
          move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
          exists t1; split.
          - by rewrite /preemption_time scheduled_job_at_def; rt_eauto; move: H_ideal_is_idle => /eqP ->.
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
        Lemma preemption_time_exists_case2:
          exists pr_t,
            preemption_time arr_seq sched pr_t /\
            t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
        Proof.
          set (service := service sched).
          move :  (H_valid_model_with_bounded_nonpreemptive_segments) =>  [VALID BOUNDED].
          move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
          move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
          exists t1; split; last first.
          apply/andP; split; [by done | by rewrite leq_addr].
          destruct t1.
          - by eapply zero_is_pt; rt_eauto.
          - apply: first_moment_is_pt H_jhp_is_scheduled; rt_eauto.
            by eapply hp_job_not_scheduled_before_quiet_time; rt_eauto.
        Qed.

      End Case2.

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
          Hypothesis H_fpt_is_preemptio_point : job_preemptable jlp (progr_t1 + fpt).
          Hypothesis H_fpt_is_first_preemption_point:
            forall ρ,
              progr_t1 <= ρ <= progr_t1 + (job_max_nonpreemptive_segment jlp - ε) ->
              job_preemptable jlp ρ ->
              service sched jlp t1 + fpt <= ρ.

          (** For correctness, we also assume that [fpt] does not
              exceed the length of the maximum non-preemptive
              segment. *)
          Hypothesis H_progr_le_max_nonp_segment:
            fpt <= job_max_nonpreemptive_segment jlp - ε.

          (** First we show that [fpt] is indeed the first preemption point after [progr_t1]. *)
          Lemma no_intermediate_preemption_point:
            forall ρ,
              progr_t1 <= ρ < progr_t1 + fpt ->
              ~~ job_preemptable jlp ρ.
          Proof.
            move => prog /andP [GE LT].
            apply/negP; intros PPJ.
            move: H_fpt_is_first_preemption_point => K; specialize (K prog).
            feed_n 2 K; first (apply/andP; split); try done.
            { apply leq_trans with (service sched jlp t1 + fpt).
              + by apply ltnW.
              + by rewrite leq_add2l; apply H_progr_le_max_nonp_segment.
            }
            by move: K; rewrite leqNgt; move => /negP NLT; apply: NLT.
          Qed.

          (** Thanks to the fact that the scheduler respects the notion of preemption points
              we show that [jlp] is continuously scheduled in time interval <<[t1, t1 + fpt)>>. *)
          Lemma continuously_scheduled_between_preemption_points:
            forall t',
              t1 <= t' < t1 + fpt ->
              scheduled_at sched jlp t'.
          Proof.
            move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
            move: (H_jlp_is_scheduled) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.
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
              apply leq_ltn_trans with Δ; last by done.
              rewrite -{2}(sum_of_ones t1 Δ).
              rewrite leq_sum //; intros t _.
              apply service_at_most_one.
              by apply ideal_proc_model_provides_unit_service.
            }
            { by apply/andP; split; [done | rewrite leq_addr]. }
          Qed.

          (** Thus, job [jlp] reaches its preemption point at time instant [t1 + fpt],
              which implies that time instant [t1 + fpt] is a preemption time. *)
          Lemma first_preemption_time:
            preemption_time arr_seq sched (t1 + fpt).
          Proof.
            rewrite /preemption_time scheduled_job_at_def; rt_eauto.
            have [Idle|[s' Sched_s']] :=
              ideal_proc_model_sched_case_analysis sched (t1 + fpt);
              first by rewrite (eqP Idle).
            move: (Sched_s'); rewrite scheduled_at_def => /eqP EqSched_s'.
            rewrite EqSched_s'; destruct (jlp == s') eqn: EQ.
            - move: EQ => /eqP EQ; subst s'.
              rewrite /service -(service_during_cat _ _ _ t1); last first.
              { by apply/andP; split; last rewrite leq_addr. }
              have ->: service_during sched jlp t1 (t1 + fpt) = fpt => //.
              { rewrite -{2}(sum_of_ones t1 fpt) /service_during.
                apply/eqP; rewrite eqn_leq //; apply/andP; split.
                + rewrite leq_sum //; intros t _.
                  apply service_at_most_one.
                    by apply ideal_proc_model_provides_unit_service.
                + rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
                  rewrite leq_sum //.
                  move => x /andP [HYP _].
                  rewrite service_at_def lt0b -scheduled_at_def.
                    by apply continuously_scheduled_between_preemption_points. }
            - case: (posnP fpt) => [ZERO|POS].
              { subst fpt.
                exfalso; move: EQ => /negP EQ; apply: EQ.
                move: H_jlp_is_scheduled; rewrite scheduled_at_def; move => /eqP SCHED2.
                rewrite addn0 in EqSched_s'; rewrite EqSched_s' in SCHED2.
                  by inversion SCHED2. }
              { have [sm EQ2]: exists sm, sm.+1 = fpt by exists fpt.-1; lia.
                rewrite -EQ2 addnS.
                move: ((proj1 H_valid_model_with_bounded_nonpreemptive_segments) s' (H_jobs_come_from_arrival_sequence _ _ Sched_s')) => T.
                apply T. clear T. apply /negP => CONTR.
                move: EQ => /negP; apply.
                move: (continuously_scheduled_between_preemption_points (t1 + sm)) => SCHEDs0.
                feed SCHEDs0; first by apply/andP; split; [rewrite leq_addr | rewrite -EQ2 addnS].
                apply/eqP; eapply ideal_proc_model_is_a_uniprocessor_model; eauto 2.
                by rewrite -addnS EQ2.
              }
          Qed.

          (** And since [fpt <= max_length_of_priority_inversion j t1],
              [t1 <= t1 + fpt <= t1 + max_length_of_priority_inversion j t1]. *)
          Lemma preemption_time_le_max_len_of_priority_inversion:
            t1 <= t1 + fpt <= t1 + max_length_of_priority_inversion j t1.
          Proof.
            move: (H_jlp_is_scheduled) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.
            apply/andP; split; first by rewrite leq_addr.
            rewrite leq_add2l.
            unfold max_length_of_priority_inversion.
            rewrite (big_rem jlp) //=.
            { rewrite H_jlp_low_priority //=.
              have NZ: service sched jlp t1 < job_cost jlp
                by apply: service_lt_cost; rt_eauto.
              rewrite ifT; last by lia.
              apply leq_trans with (job_max_nonpreemptive_segment jlp - ε).
              - by apply H_progr_le_max_nonp_segment.
              - by rewrite leq_maxl.
            }
            eapply arrived_between_implies_in_arrivals; rt_eauto.
            apply/andP; split; first by done.
            eapply low_priority_job_arrives_before_busy_interval_prefix with t1; eauto 2.
            by move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]]; apply/andP; split.
          Qed.

        End FirstPreemptionPointOfjlp.

        (** Next, we combine the above facts to conclude the lemma. *)
        Lemma preemption_time_exists_case3:
          exists pr_t,
            preemption_time arr_seq sched pr_t /\
            t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
        Proof.
          set (service := service sched).
          have EX: exists pt,
              ((service jlp t1) <= pt <= (service jlp t1) + (job_max_nonpreemptive_segment jlp - 1)) && job_preemptable jlp pt.
          { move: (H_jlp_is_scheduled) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.
            move: (proj2 (H_valid_model_with_bounded_nonpreemptive_segments) jlp ARRs) =>[_ EXPP].
            destruct H_sched_valid as [A B].
            specialize (EXPP (service jlp t1)).
            feed EXPP.
            { apply/andP; split; first by done.
              apply service_at_most_cost; rt_eauto.
            }
            move: EXPP => [pt [NEQ PP]].
            exists pt; apply/andP; split; by done.
          }
          move: (ex_minnP EX) => [sm_pt /andP [NEQ PP] MIN]; clear EX.
          have Fact: exists Δ, sm_pt = service jlp t1 + Δ.
          { exists (sm_pt - service jlp t1).
            apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC //.
            by move: NEQ => /andP [T _]. }
          move: Fact => [Δ EQ]; subst sm_pt; rename Δ into sm_pt.
          exists (t1 + sm_pt); split.
          { apply first_preemption_time; rewrite /service.service; try done.
            + by intros; apply MIN; apply/andP; split.
            + by rewrite /ε; lia.
          }
          by apply preemption_time_le_max_len_of_priority_inversion;
            [ done | by rewrite /ε; lia].
        Qed.

      End Case3.

    End CaseAnalysis.

    (** By doing the case analysis, we show that indeed there is a
        preemption time in the time interval [[t1, t1 +
        max_length_of_priority_inversion j t1]]. *)
    Lemma preemption_time_exists:
      exists pr_t,
        preemption_time arr_seq sched pr_t /\
        t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
    Proof.
      set (service := service sched).
      move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
      move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
      ideal_proc_model_sched_case_analysis sched t1 s.
      - by apply preemption_time_exists_case1.
      - destruct (hep_job s j) eqn:PRIO.
        + by eapply preemption_time_exists_case2; eauto.
        + eapply preemption_time_exists_case3 with s; eauto.
          by rewrite -eqbF_neg; apply /eqP.
    Qed.

  End PreemptionTimeExists.

  (** In this section we prove that if a preemption point [ppt] exists in a job's busy window,
      it suffers no priority inversion after [ppt]. Equivalently the [cumulative_priority_inversion]
      of the job in the busy window [t1,t2] is bounded by the [cumulative_priority_inversion]
      of the job in the time window [t1,[ppt]). *)
  Section NoPriorityInversionAfterPreemptionPoint.

    (** Consider the preemption point [ppt]. *)
    Variable ppt: instant.
    Hypothesis H_preemption_point : preemption_time arr_seq sched ppt.
    Hypothesis H_after_t1 : t1 <= ppt.

    (** We establish the aforementioned result by showing that [j] cannot suffer
        priority inversion after the preemption time [ppt]. *)
    Lemma priority_inversion_occurs_only_till_preemption_point:
      cumulative_priority_inversion arr_seq sched j t1 t2 <=
      cumulative_priority_inversion arr_seq sched j t1 ppt.
    Proof.
      have [LEQ|LT_t1t2] := leqP t1 t2;
        last by rewrite /cumulative_priority_inversion big_geq //; exact: ltnW.
      have [LEQ_t2ppt|LT] := leqP t2 ppt;
        first by rewrite (cumulative_priority_inversion_cat _ _ _ t2 t1 ppt) //
                 ; exact: leq_addr.
      move: (H_busy_interval_prefix) => [_ [_ [_ /andP [T _]]]].
      rewrite /cumulative_priority_inversion (@big_cat_nat _ _ _ ppt) //=;
        last by lia.
      rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
      rewrite big_nat_cond big1 //; move => t /andP[/andP[GEt LEt] _].
      have [j_hp [ARRB [HP SCHEDHP]]]:
        exists j_hp : Job, arrived_between j_hp t1 t.+1
                           /\ hep_job j_hp j
                           /\ scheduled_at sched j_hp t.
      { apply: not_quiet_implies_exists_scheduled_hp_job (ppt-t1) _ (t) _; rt_eauto.
        by exists ppt; split; [done | rewrite subnKC //; apply /andP;split].
        by rewrite subnKC //; apply/andP; split. }
      apply /eqP; rewrite eqb0; apply/negP; move => /priority_inversion_P INV.
      feed_n 3 INV; rt_eauto; last move: INV => [_ [j_lp /andP[SCHED PRIO]]].
      enough (EQ : j_lp = j_hp); first by subst; rewrite HP in PRIO.
      by apply: (ideal_proc_model_is_a_uniprocessor_model j_lp j_hp sched t); rt_eauto.
    Qed.

  End NoPriorityInversionAfterPreemptionPoint.

End PriorityInversionIsBounded.
