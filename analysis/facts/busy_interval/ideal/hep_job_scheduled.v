Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.busy_interval.busy_interval.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** * Processor Executes HEP jobs at Preemption Point *)

(** In this file, we show that, given a busy interval of a job [j],
    the processor is always busy scheduling a higher-or-equal-priority
    job at any preemptive point inside the busy interval. *)
Section ProcessorBusyWithHEPJobAtPreemptionPoints.

  (** Consider any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** Consider a JLFP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive: reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive: transitive_job_priorities JLFP.

  (** In addition, we assume the existence of a function mapping a job
      and its progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.

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

  (** Consider any job [j] with positive job cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval_prefix :
    busy_interval_prefix arr_seq sched j t1 t2.

  (** Consider an arbitrary preemption time t ∈ <<[t1,t2)>>. *)
  Variable t : instant.
  Hypothesis H_t_in_busy_interval : t1 <= t < t2.
  Hypothesis H_t_preemption_time : preemption_time arr_seq sched t.

  (** First note since [t] lies inside the busy interval,
      the processor cannot be idle at time [t]. *)
  Lemma instant_t_is_not_idle:
    ~ ideal_is_idle sched t.
  Proof.
    by move => IDLE; exfalso; apply: not_quiet_implies_not_idle; rt_eauto.
  Qed.

  (** Next we consider two cases:
        (1) [t] is less than [t2 - 1] and
        (2) [t] is equal to [t2 - 1]. *)

  (** In case when [t < t2 - 1], we use the fact that time instant
      [t+1] is not a quiet time. The later implies that there is a
      pending higher-or-equal priority job at time [t]. Thus, the
      assumption that the schedule respects priority policy at
      preemption points implies that the scheduled job must have a
      higher-or-equal priority. *)
  Lemma scheduled_at_preemption_time_implies_higher_or_equal_priority_lt:
    t < t2.-1 ->
    forall jhp,
      scheduled_at sched jhp t ->
      hep_job jhp j.
  Proof.
    intros LTt2m1 jlp Sched_jlp; apply contraT; move => /negP NOTHP; exfalso.
    move: (H_t_in_busy_interval) (H_busy_interval_prefix) => /andP [GEt LEt] [SL [QUIET [NOTQUIET INBI]]].
    apply NOTQUIET with (t := t.+1).
    { apply/andP; split.
      - by apply leq_ltn_trans with t1.
      - rewrite -subn1 ltn_subRL addnC in LTt2m1.
        by rewrite -[t.+1]addn1.
    }
    intros j_hp ARR HP BEF.
    apply contraT => NCOMP'; exfalso.
    have PEND : pending sched j_hp t.
    { apply/andP; split.
      - by rewrite /has_arrived.
      - by move: NCOMP'; apply contra, completion_monotonic.
    }
    apply H_job_ready in PEND => //; destruct PEND as [j' [ARR' [READY' HEP']]].
    have HEP : hep_job j' j by apply (H_priority_is_transitive j_hp).
    clear HEP' NCOMP' BEF HP ARR j_hp.
    have BACK: backlogged sched j' t.
    { apply/andP; split; first by done.
      apply/negP; intro SCHED'.
      move: (ideal_proc_model_is_a_uniprocessor_model jlp j' sched t Sched_jlp SCHED') => EQ.
      by subst; apply: NOTHP.
    }
    apply NOTHP, (H_priority_is_transitive j'); last by eapply HEP.
    by eapply H_respects_policy; eauto .
  Qed.

  (** In the case when [t = t2 - 1], we cannot use the same proof
      since [t+1 = t2], but [t2] is a quiet time. So we do a similar
      case analysis on the fact that [t1 = t ∨ t1 < t]. *)
  Lemma scheduled_at_preemption_time_implies_higher_or_equal_priority_eq:
    t = t2.-1 ->
    forall jhp,
      scheduled_at sched jhp t ->
      hep_job jhp j.
  Proof.
    intros EQUALt2m1 jlp Sched_jlp; apply contraT; move => /negP NOTHP; exfalso.
    move: (H_t_in_busy_interval) (H_busy_interval_prefix) => /andP [GEt LEt] [SL [QUIET [NOTQUIET INBI]]].
    rewrite leq_eqVlt in GEt; first move: GEt => /orP [/eqP EQUALt1 | LARGERt1].
    { subst t t1; clear LEt SL.
      have ARR : job_arrival j = t2.-1.
      { apply/eqP; rewrite eq_sym eqn_leq.
        destruct t2; first by done.
        rewrite ltnS -pred_Sn in INBI.
        now rewrite -pred_Sn.
      }
      have PEND: pending sched j t2.-1
        by rewrite -ARR; apply job_pending_at_arrival => //; rt_eauto.
      apply H_job_ready in PEND => //; destruct PEND as [jhp [ARRhp [PENDhp HEPhp]]].
      eapply NOTHP, H_priority_is_transitive; last by apply HEPhp.
      apply (H_respects_policy _ _ t2.-1); auto.
      apply/andP; split; first by done.
      apply/negP; intros SCHED.
      move: (ideal_proc_model_is_a_uniprocessor_model _ _ sched _ SCHED Sched_jlp) => EQ.
      by subst; apply: NOTHP.
    }
    { feed (NOTQUIET t); first by apply/andP; split.
      apply NOTQUIET; intros j_hp' IN HP ARR.
      apply contraT => NOTCOMP'; exfalso.
      have PEND : pending sched j_hp' t.
      { apply/andP; split.
        - by rewrite /has_arrived ltnW.
        - by move: NOTCOMP'; apply contra, completion_monotonic.
      }
      apply H_job_ready in PEND => //; destruct PEND as [j' [ARR' [READY' HEP']]].
      have HEP : hep_job j' j by apply (H_priority_is_transitive j_hp').
      clear ARR HP IN HEP' NOTCOMP' j_hp'.
      have BACK: backlogged sched j' t.
      { apply/andP; split; first by done.
        apply/negP; intro SCHED'.
        move: (ideal_proc_model_is_a_uniprocessor_model jlp j' sched t Sched_jlp SCHED') => EQ.
        by subst; apply: NOTHP.
      }
      apply NOTHP, (H_priority_is_transitive j'); last by eapply HEP.
      by eapply H_respects_policy; eauto .
    }
  Qed.

  (** By combining the above facts we conclude that a job that is
      scheduled at time [t] has higher-or-equal priority. *)
  Corollary scheduled_at_preemption_time_implies_higher_or_equal_priority:
    forall jhp,
      scheduled_at sched jhp t ->
      hep_job jhp j.
  Proof.
    move: (H_t_in_busy_interval) (H_busy_interval_prefix) => /andP [GEt LEt] [SL [QUIET [NOTQUIET INBI]]].
    have: t <= t2.-1 by rewrite -subn1 leq_subRL_impl // addn1.
    rewrite leq_eqVlt => /orP [/eqP EQUALt2m1 | LTt2m1].
    - by apply scheduled_at_preemption_time_implies_higher_or_equal_priority_eq.
    - by apply scheduled_at_preemption_time_implies_higher_or_equal_priority_lt.
  Qed.

  (** Since a job that is scheduled at time [t] has higher-or-equal
      priority, by properties of a busy interval it cannot arrive
      before time instant [t1]. *)
  Lemma scheduled_at_preemption_time_implies_arrived_between_within_busy_interval:
    forall jhp,
      scheduled_at sched jhp t ->
      arrived_between jhp t1 t2.
  Proof.
    intros jhp Sched_jhp.
    rename H_work_conserving into WORK, H_jobs_come_from_arrival_sequence into CONS.
    move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET INBI]]].
    move: (H_t_in_busy_interval) => /andP [GEt LEt].
    have HP := scheduled_at_preemption_time_implies_higher_or_equal_priority _ Sched_jhp.
    move: (Sched_jhp) => PENDING.
    eapply scheduled_implies_pending in PENDING; rt_eauto.
    apply/andP; split; last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _].
    apply contraT; rewrite -ltnNge; intro LT; exfalso.
    feed (QUIET jhp); first by eapply CONS, Sched_jhp.
    specialize (QUIET HP LT).
    have COMP: completed_by sched jhp t by apply: completion_monotonic QUIET.
    apply completed_implies_not_scheduled in COMP; rt_eauto.
    by move: COMP => /negP COMP; apply COMP.
  Qed.

  (** From the above lemmas we prove that there is a job [jhp] that is
      (1) scheduled at time [t], (2) has higher-or-equal priority, and
      (3) arrived between [t1] and [t2].  *)
  Corollary not_quiet_implies_exists_scheduled_hp_job_at_preemption_point:
    exists j_hp,
      arrived_between j_hp t1 t2
      /\ hep_job j_hp j
      /\ scheduled_at sched j_hp t.
  Proof.
    move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET INBI]]].
    move: (H_t_in_busy_interval) => /andP [GEt LEt].
    ideal_proc_model_sched_case_analysis sched t jhp.
    { by exfalso; apply instant_t_is_not_idle. }
    exists jhp.
    repeat split.
    - by apply scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.
    - by apply scheduled_at_preemption_time_implies_higher_or_equal_priority.
    - by done.
  Qed.

End ProcessorBusyWithHEPJobAtPreemptionPoints.
