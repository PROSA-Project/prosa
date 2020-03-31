Require Export prosa.implementation.facts.generic_schedule.
Require Export prosa.implementation.definitions.ideal_uni_scheduler.
Require Export prosa.analysis.facts.model.ideal_schedule.

(** * Properties of the Preemption-Aware Ideal Uniprocessor Scheduler *)

(** This file establishes facts about the reference model of a
    preemption-model-aware ideal uniprocessor scheduler. *)

(** The following results assume ideal uniprocessor schedules. *)
Require Import prosa.model.processor.ideal.

Section NPUniprocessorScheduler.

  (** Consider any type of jobs with costs and arrival times, ... *)
  Context {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job}.

  (** ... in the context of an ideal uniprocessor model. *)
  Let PState := ideal.processor_state Job.
  Let idle_state : PState := None.

  (** Suppose we are given a consistent arrival sequence of such jobs, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrival_times: consistent_arrival_times arr_seq.

  (** ... a non-clairvoyant readiness model, ... *)
  Context {RM: JobReady Job (ideal.processor_state Job)}.
  Hypothesis H_nonclairvoyant_job_readiness: nonclairvoyant_readiness RM.

  (** ... and a preemption model. *)
  Context `{JobPreemptable Job}.

  (** For any given job selection policy ... *)
  Variable choose_job : instant -> seq Job -> option Job.

  (** ... consider the schedule produced by the preemption-aware scheduler for
      the policy induced by [choose_job]. *)
  Let schedule := np_uni_schedule arr_seq choose_job.
  Let policy := allocation_at arr_seq choose_job.

  (** To begin with, we establish that the preemption-aware scheduler does not
      induce non-work-conserving behavior. *)
  Section WorkConservation.

    (** If [choose_job] does not voluntarily idle the processor, ... *)
    Hypothesis H_non_idling:
      forall t s,
        choose_job t s = idle_state <-> s = [::].

    (** ... then we can establish work-conservation. *)

    (** First, we observe that [allocation_at] yields [idle_state] only if there are
        no backlogged jobs. *)
    Lemma allocation_at_idle:
      forall sched t,
        allocation_at arr_seq choose_job sched t = idle_state ->
        jobs_backlogged_at arr_seq sched t = [::].
    Proof.
      move=> sched t.
      elim: t => [|t _]; first by apply H_non_idling.
      rewrite /allocation_at /prev_job_nonpreemptive.
      elim: (sched t) => [j'|]; last by apply H_non_idling.
      rewrite if_neg.
      elim: (job_preemptable j' (service sched j' t.+1)); first by apply H_non_idling.
      now discriminate.
    Qed.

    (** As a stepping stone, we observe that the generated schedule is idle at
        a time [t] only if there are no backlogged jobs. *)
    Lemma idle_schedule_no_backlogged_jobs:
      forall t,
        is_idle schedule t ->
        jobs_backlogged_at arr_seq schedule t = [::].
    Proof.
      move=> t.
      rewrite /is_idle /schedule /np_uni_schedule /generic_schedule => /eqP.
      move=> NONE. move: (NONE).
      rewrite schedule_up_to_def => IDLE.
      apply allocation_at_idle in IDLE.
      rewrite -IDLE.
      apply backlogged_jobs_prefix_invariance with (h := t.+1) => //.
      rewrite /identical_prefix => x.
      rewrite ltnS leq_eqVlt => /orP [/eqP ->|LT]; last first.
      { elim: t LT IDLE NONE => // => h IH LT_x IDLE NONE.
        now apply schedule_up_to_prefix_inclusion. }
      { elim: t IDLE NONE => [IDLE _| t' _ _ ->]; last by rewrite schedule_up_to_empty.
        rewrite /schedule_up_to replace_at_def.
        rewrite /allocation_at /prev_job_nonpreemptive IDLE H_non_idling //. }
    Qed.

    (** From the preceding fact, we conclude that the generated schedule is
        indeed work-conserving. *)
    Theorem np_schedule_work_conserving:
      work_conserving arr_seq schedule.
    Proof.
      move=> j t ARRIVES BACKLOGGED.
      move: (@ideal_proc_model_sched_case_analysis Job schedule t) => [IDLE|SCHED]; last by exact.
      exfalso.
      have NON_EMPTY: j \in jobs_backlogged_at arr_seq schedule t by apply mem_backlogged_jobs => //.
      clear BACKLOGGED.
      move: (idle_schedule_no_backlogged_jobs t IDLE) => EMPTY.
      now rewrite EMPTY in NON_EMPTY.
    Qed.

  End WorkConservation.

  (** The next result establishes that the generated preemption-model-aware
      schedule is structurally valid, meaning all jobs stem from the arrival
      sequence and only ready jobs are scheduled. *)
  Section Validity.

    (** Any reasonable job selection policy will not create jobs "out of thin
        air," i.e., if a job is selected, it was among those given to choose
        from. *)
    Hypothesis H_chooses_from_set:
      forall t s j, choose_job t s = Some j -> j \in s.

    (** For the schedule to be valid, we require the notion of readiness to be
        consistent with the preemption model: a non-preemptive job remains
        ready until (at least) the end of its current non-preemptive
        section. *)
    Hypothesis H_valid_preemption_behavior:
      valid_nonpreemptive_readiness RM.

    (** Under this natural assumption, the generated schedule is valid. *)
    Theorem np_schedule_valid:
      valid_schedule schedule arr_seq.
    Proof.
      rewrite /valid_schedule; split; move=> j t; rewrite scheduled_at_def /schedule /np_uni_schedule /generic_schedule.
      { elim: t => [/eqP | t'  IH /eqP].
        - rewrite schedule_up_to_def  /allocation_at  /prev_job_nonpreemptive => IN.
          move: (H_chooses_from_set _ _ _ IN).
          now apply backlogged_job_arrives_in.
        - rewrite schedule_up_to_def  /allocation_at.
          case: (prev_job_nonpreemptive  (schedule_up_to _ _ t') t'.+1) => [|IN];
                first by rewrite -pred_Sn => SCHED; apply IH; apply /eqP.
          move: (H_chooses_from_set _ _ _ IN).
          now apply backlogged_job_arrives_in. }
      { elim: t => [/eqP |t'  IH /eqP].
        - rewrite schedule_up_to_def  /allocation_at  /prev_job_nonpreemptive => IN.
          move: (H_chooses_from_set _ _ _ IN).
          rewrite mem_filter /backlogged => /andP [/andP [READY _]  _].
          now rewrite -(H_nonclairvoyant_job_readiness (empty_schedule idle_state) schedule j 0).
        - rewrite schedule_up_to_def  /allocation_at /prev_job_nonpreemptive.
          have JOB: choose_job t'.+1 (jobs_backlogged_at arr_seq (schedule_up_to policy idle_state  t') t'.+1)
                    = Some j
                    -> job_ready schedule j t'.+1.
          { move=> IN.
            move: (H_chooses_from_set _ _ _ IN).
            rewrite mem_filter /backlogged => /andP [/andP [READY _]  _].
            rewrite -(H_nonclairvoyant_job_readiness (schedule_up_to policy idle_state t') schedule j t'.+1) //.
            rewrite /identical_prefix /schedule /np_uni_schedule /generic_schedule => t'' LT.
            now rewrite (schedule_up_to_prefix_inclusion _  _  t'' t') //. }
          case: (schedule_up_to _ _ t' t') => [j' | IN]; last by apply JOB.
          destruct (~~ job_preemptable j' _) eqn:NP => [EQ|IN]; last by apply JOB.
          apply H_valid_preemption_behavior.
          injection EQ => <-.
          move: NP.
          have <-: (service (schedule_up_to policy idle_state t') j' t'.+1
                    = service (fun t : instant => schedule_up_to policy idle_state t t) j' t'.+1) => //.
          rewrite /service.
          apply equal_prefix_implies_same_service_during => t /andP [_ BOUND].
          now rewrite (schedule_up_to_prefix_inclusion _  _ t t'). }
    Qed.

  End Validity.

  (** Next, we observe that the resulting schedule is consistent with the
      definition of "preemption times". *)
  Section PreemptionTimes.

    (** For notational convenience, recall the definition of a prefix of the
        schedule based on which the next decision is made. *)
    Let prefix t := if t is t'.+1 then schedule_up_to policy idle_state t' else empty_schedule idle_state.

    (** First, we observe that non-preemptive jobs remain scheduled as long as
        they are non-preemptive. *)
    Lemma np_job_remains_scheduled:
      forall t,
        prev_job_nonpreemptive (prefix t) t ->
        schedule_up_to policy idle_state t t = schedule_up_to policy idle_state t t.-1.
    Proof.
      elim => [|t _] //  NP.
      rewrite schedule_up_to_def /allocation_at /policy /allocation_at.
      rewrite ifT // -pred_Sn.
      now rewrite schedule_up_to_widen.
    Qed.

    (** From this, we conclude that the predicate used to determine whether the
        previously scheduled job is nonpreemptive in the computation of
        [np_uni_schedule] is consistent with the existing notion of a
        [preemption_time]. *)
    Lemma np_consistent:
      forall t,
        prev_job_nonpreemptive (prefix t) t ->
        ~~ preemption_time schedule t.
    Proof.
      elim => [|t _]; first by rewrite /prev_job_nonpreemptive.
      rewrite /schedule /np_uni_schedule /generic_schedule /preemption_time schedule_up_to_def /prefix /allocation_at => NP.
      rewrite ifT //.
      rewrite -pred_Sn.
      move: NP. rewrite /prev_job_nonpreemptive.
      elim: (schedule_up_to policy idle_state t t) => // j.
      have <-: service (schedule_up_to policy idle_state t) j t.+1
               = service (fun t0 : instant => schedule_up_to policy idle_state t0 t0) j t.+1 => //.
      rewrite /service.
      apply equal_prefix_implies_same_service_during => t' /andP [_ BOUND].
      now rewrite (schedule_up_to_prefix_inclusion _ _ t' t).
    Qed.

  End PreemptionTimes.

End NPUniprocessorScheduler.


