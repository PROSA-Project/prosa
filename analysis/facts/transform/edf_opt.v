From mathcomp Require Import ssrnat ssrbool fintype.
Require Export prosa.model.schedule.edf.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.transform.edf_trans.
Require Export prosa.analysis.facts.transform.swaps.
Require Export prosa.analysis.facts.readiness.basic.

(** This file contains the main argument of the EDF optimality proof,
    starting with an analysis of the individual functions that drive
    the piece-wise transformation of a given reference schedule in an
    EDF schedule, and ending with proofs of individual properties of
    the obtained EDF schedule. *)

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require Import prosa.model.processor.ideal.
(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

(** We start by analyzing the helper function [find_swap_candidate],
    which is a problem-specific wrapper around [search_arg]. *)
Section FindSwapCandidateFacts.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved (i.e., in which jobs execute only after
     having arrived and only if they are not yet complete). *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** Suppose we are given a job [j1]... *)
  Variable j1: Job.

  (** ...and a point in time [t1]... *)
  Variable t1: instant.

  (** ...at which [j1] is scheduled... *)
  Hypothesis H_not_idle: scheduled_at sched j1 t1.

  (** ...and that is before its deadline. *)
  Hypothesis H_deadline_not_missed: t1 < job_deadline j1.

  (** First, we observe that under these assumptions the processor
     state at time [t1] is "relevant" according to the notion of
     relevance underlying the EDF transformation, namely
     [relevant_pstate]. *)
  Lemma t1_relevant: relevant_pstate t1 (sched t1).
  Proof.
    move: H_not_idle. rewrite scheduled_at_def => /eqP ->.
    rewrite /relevant_pstate -/(has_arrived j1 t1).
    move: (H_jobs_must_arrive_to_execute j1 t1) => SCHED_ARR.
      by apply SCHED_ARR.
  Qed.

  (** Since [t1] is relevant, we conclude that a search for a relevant
     state succeeds (if nothing else, it finds [t1]). *)
  Lemma fsc_search_successful:
    exists t, search_arg sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1) = Some t.
  Proof.
    apply search_arg_not_none.
    exists t1. split.
    - by apply /andP; split.
    - by apply t1_relevant.
  Qed.

  (** For rewriting purposes, we observe that the [search_arg]
     operation within [find_swap_candidate] yields the final result of
     [find_swap_candidate]. *)
  Corollary fsc_search_result:
    search_arg sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1) = Some (find_swap_candidate sched t1 j1).
  Proof.
    move: fsc_search_successful => [t FOUND].
    by rewrite /find_swap_candidate FOUND.
  Qed.

  (** There is a job that is scheduled at the time that
     [find_swap_candidate] returns, and that job arrives no later than
     at time [t1]. *)
  Lemma fsc_not_idle:
    exists j', (scheduled_at sched j' (find_swap_candidate sched t1 j1))
               /\ job_arrival j' <= t1.
  Proof.
    move: fsc_search_successful => [t FOUND].
    move: (search_arg_pred _ _ _ _ _ _ FOUND).
    rewrite /relevant_pstate.
    destruct (sched t) as [j'|] eqn:SCHED_t => // ARR_j'.
    exists j'. split => //.
    rewrite /find_swap_candidate FOUND.
    rewrite scheduled_at_def //.
      by apply /eqP.
  Qed.

  (** Since we are considering a uniprocessor model, only one job is
     scheduled at a time. Hence once we know that a job is scheduled
     at the time that [find_swap_candidate] returns, we can conclude
     that it arrives not later than at time t1. *)
  Corollary fsc_found_job_arrival:
    forall j2,
      scheduled_at sched j2 (find_swap_candidate sched t1 j1) ->
      job_arrival j2 <= t1.
  Proof.
    move=> j2 SCHED_j2.
    move: fsc_not_idle => [j' [SCHED_j' ARR]].
    by rewrite -(ideal_proc_model_is_a_uniprocessor_model _ _ _ _ SCHED_j' SCHED_j2).
  Qed.

  (** We observe that [find_swap_candidate] returns a value within a
     known finite interval. *)
  Lemma fsc_range:
    t1 <= find_swap_candidate sched t1 j1 < job_deadline j1.
  Proof. move: fsc_search_result. by apply search_arg_in_range. Qed.

  (** For convenience, since we often only require the lower bound on
     the interval, we re-state it as a corollary. *)
  Corollary fsc_range1:
    t1 <= find_swap_candidate sched t1 j1.
  Proof. by move: fsc_range => /andP [LE _]. Qed.

  (** The following lemma is a key step of the overall proof: the job
     scheduled at the time found by [find_swap_candidate] has the
     property that it has a deadline that is no later than that of any
     other job in the window given by time [t1] and the deadline of
     the job scheduled at time [t1]. *)
  Lemma fsc_found_job_deadline:
    forall j2,
      scheduled_at sched j2 (find_swap_candidate sched t1 j1) ->
      forall j t,
        t1 <= t < job_deadline j1 ->
        scheduled_at sched j t ->
        job_arrival j <= t1 ->
        job_deadline j2 <= job_deadline j.
  Proof.
    move=> j2 SCHED_j2 j t /andP [t1_le_t t_lt_dl1] SCHED_j ARR_j.
    have TOTAL: total earlier_deadline
      by rewrite /earlier_deadline => s1 s2; apply leq_total.
    have TRANS: transitive earlier_deadline
      by rewrite /earlier_deadline => s1 s2 s3; apply leq_trans.
    have REFL: reflexive earlier_deadline
      by rewrite /earlier_deadline => s; apply leqnn.
    move: SCHED_j SCHED_j2. rewrite !scheduled_at_def => /eqP SCHED_j /eqP SCHED_j2.
    have ED: earlier_deadline (sched (find_swap_candidate sched t1 j1)) (sched t).
    {
      move: (search_arg_extremum _ _ _ REFL TRANS TOTAL _ _ _ fsc_search_result) => MIN.
      apply (MIN t).
      - by apply /andP; split.
      - by rewrite /relevant_pstate SCHED_j.
    }
    by move: ED; rewrite /earlier_deadline /oapp SCHED_j SCHED_j2.
  Qed.

  (** As a special case of the above lemma, we observe that the job
     scheduled at the time given by [find_swap_candidate] in
     particular has a deadline no later than the job scheduled at time
     [t1]. *)
  Corollary fsc_no_later_deadline:
    forall j2,
      scheduled_at sched j2 (find_swap_candidate sched t1 j1) ->
      job_deadline j2 <= job_deadline j1.
  Proof.
    move=> j2 SCHED_j2.
    apply fsc_found_job_deadline with (t := t1) => //.
    - by apply /andP; split.
    - by apply H_jobs_must_arrive_to_execute.
  Qed.

End FindSwapCandidateFacts.


(** In the next section, we analyze properties of [make_edf_at], which
    we abbreviate as "[mea]" in the following. *)
Section MakeEDFAtFacts.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved...  *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...and in which no scheduled job misses a deadline. *)
  Hypothesis H_no_deadline_misses: all_deadlines_met sched.

  (** Since we will require this fact repeatedly, we briefly observe
     that, since no scheduled job misses its deadline, if a job is
     scheduled at some time [t], then its deadline is later than
     [t]. *)
  Fact scheduled_job_in_sched_has_later_deadline:
    forall j t,
      scheduled_at sched j t ->
      job_deadline j > t.
  Proof.
    move=> j t SCHED.
    apply (scheduled_at_implies_later_deadline sched) => //.
    - by apply ideal_proc_model_ensures_ideal_progress.
    - by apply (H_no_deadline_misses _ t).
  Qed.

  (** We analyze [make_edf_at] applied to an arbitrary point in time,
     which we denote [t_edf] in the following. *)
  Variable t_edf: instant.

  (** For brevity, let [sched'] denote the schedule obtained from
     [make_edf_at] applied to [sched] at time [t_edf]. *)
  Let sched' := make_edf_at sched t_edf.

  (** First, we observe that in [sched'] jobs still don't execute past
     completion. *)
  Lemma mea_completed_jobs:
    completed_jobs_dont_execute sched'.
  Proof.
    have IDEAL := @ideal_proc_model_ensures_ideal_progress Job.
    have UNIT := @ideal_proc_model_provides_unit_service Job.
    rewrite /sched' /make_edf_at.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED; last by done.
    have SCHED': scheduled_at sched j_orig t_edf
      by rewrite scheduled_at_def; apply /eqP.
    apply swapped_completed_jobs_dont_execute => //.
    apply fsc_range1 => //.
    by apply scheduled_job_in_sched_has_later_deadline.
  Qed.

  (** Importantly, [make_edf_at] does not introduce any deadline
     misses, which is a crucial step in the EDF optimality
     argument. *)
  Lemma mea_no_deadline_misses:
    all_deadlines_met sched'.
  Proof.
    move=> j t SCHED.
    rewrite /sched' /make_edf_at.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED_orig; last first.
    {
      apply (H_no_deadline_misses _ t).
      move: SCHED.
      by rewrite /sched' /make_edf_at SCHED_orig.
    }
    {
      have SCHED': scheduled_at sched j_orig t_edf
        by rewrite scheduled_at_def; apply /eqP.
      move: (scheduled_job_in_sched_has_later_deadline _ _ SCHED') => DL_orig.
      apply edf_swap_no_deadline_misses_introduced => //.
      - by apply ideal_proc_model_ensures_ideal_progress.
      - by apply fsc_range1 => //.
      - move=> j1 j2 SCHED_j1 SCHED_j2.
        apply: (fsc_found_job_deadline sched _ j_orig t_edf _ _ _ _ _ t_edf) => //.
        + by apply /andP; split.
        + by apply H_jobs_must_arrive_to_execute.
      - move=> j1 SCHED_j1.
        move: (fsc_not_idle sched H_jobs_must_arrive_to_execute j_orig t_edf SCHED' DL_orig) => [j' [SCHED_j' ARR_j']].
        exists j'. split => //.
        by apply scheduled_job_in_sched_has_later_deadline.
      - have EX: (exists t', scheduled_at sched j t').
        {
          apply swap_job_scheduled with (t1 := t_edf) (t2 := find_swap_candidate sched t_edf j_orig) (t0 := t).
          by move: SCHED; rewrite /sched' /make_edf_at SCHED_orig.
        }
        move: EX => [t' SCHED_t'].
        by apply H_no_deadline_misses with (t := t').
    }
  Qed.

  (** As a result, we may conclude that any job scheduled at a time t has a deadline later than t. *)
  Corollary mea_scheduled_job_has_later_deadline:
    forall j t,
      scheduled_at sched' j t ->
      job_deadline j > t.
  Proof.
    move=> j t SCHED.
    apply (scheduled_at_implies_later_deadline sched') => //.
    - by apply mea_completed_jobs.
    - by apply ideal_proc_model_ensures_ideal_progress.
    - by apply mea_no_deadline_misses with (t := t).
  Qed.

  (** Next comes a big step in the optimality proof: we observe that
     [make_edf_at] indeed ensures that [EDF_at] holds at time [t_edf] in
     [sched']. As this is a larger argument, we proceed by case analysis and
     first establish a couple of helper lemmas in the following section. *)
  Section GuaranteeCaseAnalysis.

    (** Let [j_orig] denote the job scheduled in [sched] at time
        [t_edf], let [j_edf] denote the job scheduled in [sched'] at
        time [t_edf], and let [j'] denote any job scheduled in
        [sched'] at some time [t'] after [t_edf]...  *)
    Variable j_orig j_edf j': Job.

    Variable t': instant.
    Hypothesis H_t_edf_le_t' : t_edf <= t'.

    Hypothesis H_sched_orig: scheduled_at sched  j_orig t_edf.
    Hypothesis H_sched_edf: scheduled_at sched' j_edf t_edf.
    Hypothesis H_sched': scheduled_at sched' j' t'.

    (** ... and that arrives before time [t_edf]. *)
    Hypothesis H_arrival_j' : job_arrival j' <= t_edf.

    (** We begin by observing three simple facts that will be used repeatedly in
        the case analysis. *)

    (** First, the deadline of [j_orig] is later than [t_edf]. *)
    Fact mea_guarantee_dl_orig: t_edf < job_deadline j_orig.
    Proof. by apply (scheduled_job_in_sched_has_later_deadline j_orig t_edf H_sched_orig). Qed.

    (** Second, by the definition of [sched'], [j_edf] is scheduled in
        [sched] at the time returned by [find_swap_candidate]. *)
    Fact mea_guarantee_fsc_is_j_edf: sched (find_swap_candidate sched t_edf j_orig) = Some j_edf.
    Proof.
      move: (H_sched_orig). rewrite scheduled_at_def => /eqP SCHED.
      move: (H_sched_edf). rewrite /sched' /make_edf_at /swapped /replace_at {1}SCHED //=.
      rewrite scheduled_at_def.
      destruct (find_swap_candidate sched t_edf j_orig == t_edf) eqn:FSC.
      - by move: FSC => /eqP -> /eqP.
      - by rewrite ifT // => /eqP.
    Qed.

    (** Third, the deadline of [j_edf] is no later than the deadline
        of [j_orig]. *)
    Fact mea_guarantee_deadlines: job_deadline j_edf <= job_deadline j_orig.
    Proof.
      apply: (fsc_no_later_deadline sched _ _ t_edf) => //.
      - by exact mea_guarantee_dl_orig.
      - by rewrite scheduled_at_def mea_guarantee_fsc_is_j_edf //=.
    Qed.

    (** With the setup in place, we are now ready to begin the case analysis. *)

    (** First, we consider the simpler case where [t'] is no earlier
        than the deadline of [j_orig]. This case is simpler because
        [t'] being no earlier than [j_orig]'s deadline implies that
        [j'] has deadline no earlier than [j_orig] (since no scheduled
        job in [sched] misses a deadline), which in turn has a
        deadline no earlier than [j_edf].  *)
    Lemma mea_guarantee_case_t'_past_deadline:
      job_deadline j_orig <= t' ->
      job_deadline j_edf <= job_deadline j'.
    Proof.
      move: (mea_scheduled_job_has_later_deadline j' t' H_sched') => DL_j' BOUND_t'.
      apply leq_trans with (n := job_deadline j_orig) => // ;
        first by exact mea_guarantee_deadlines.
      apply leq_trans with (n := t') => //.
      by apply ltnW.
    Qed.

    (** Next, we consider the more difficult case, where [t'] is
        before the deadline of [j_orig]. *)
    Lemma mea_guarantee_case_t'_before_deadline:
      t' < job_deadline j_orig ->
      job_deadline j_edf <= job_deadline j'.
    Proof.
      move: (H_sched_orig). rewrite scheduled_at_def => /eqP SCHED BOUND_t'.
      move: (mea_guarantee_fsc_is_j_edf) => FSC.
      have EX: (exists x, scheduled_at sched j' x /\ t_edf <= x < job_deadline j_orig).
      {
        case: (boolP(t_edf == t')) => [/eqP EQ| /eqP NEQ].
        - exists (find_swap_candidate sched t_edf j_orig).
          split; last by apply fsc_range => //; exact mea_guarantee_dl_orig.
          subst. rewrite -(ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_sched_edf H_sched').
          by rewrite scheduled_at_def FSC //=.
        - case: (boolP(find_swap_candidate sched t_edf j_orig == t')) => [/eqP EQ' | /eqP NEQ'].
          + exists t_edf.
            split; last by apply /andP; split => //; exact mea_guarantee_dl_orig.
            rewrite -(swap_job_scheduled_t2 _  _ (find_swap_candidate sched t_edf j_orig) _).
            move: H_sched'. rewrite /sched' /make_edf_at SCHED.
            by rewrite EQ'.
          + move: NEQ NEQ' => /eqP NEQ /eqP NEQ'. exists t'.
            split; last by  apply /andP; split.
            rewrite -(swap_job_scheduled_other_times _ t_edf (find_swap_candidate sched t_edf j_orig)) //.
            move: H_sched'.
            by rewrite /sched' /make_edf_at SCHED.
      }
      move: EX => [t'' [SCHED'' RANGE]].
      apply: (fsc_found_job_deadline sched _ j_orig t_edf _ _ _ _ _ t'') => // ;
        first by exact mea_guarantee_dl_orig.
      by rewrite scheduled_at_def FSC //=.
    Qed.

  End GuaranteeCaseAnalysis.

  (** Finally, putting the preceding cases together, we obtain the
      result that [make_edf_at] establishes [EDF_at] at time
      [t_edf]. *)
  Lemma make_edf_at_guarantee:
    EDF_at sched' t_edf.
  Proof.
    move=> j_edf H_sched_edf t' j' t_edf_le_t' H_sched' H_arrival_j'.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED;
      last by move: (H_sched_edf); rewrite /sched' /make_edf_at scheduled_at_def => /eqP; rewrite !SCHED.
    have H_sched: scheduled_at sched j_orig t_edf
      by rewrite scheduled_at_def; apply /eqP.
    case: (boolP (t' < job_deadline j_orig)).
    - by apply mea_guarantee_case_t'_before_deadline.
    - rewrite -leqNgt => BOUND_t'.
      by apply: (mea_guarantee_case_t'_past_deadline j_orig j_edf j' t').
  Qed.

  (** We observe that [make_edf_at] maintains the property that jobs
      must arrive to execute. *)
  Lemma mea_jobs_must_arrive:
    jobs_must_arrive_to_execute sched'.
  Proof.
    move=> j t.
    rewrite /has_arrived /sched' /make_edf_at.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED_orig;
      last by move=> SCHED; by apply H_jobs_must_arrive_to_execute.
    have SCHED': scheduled_at sched j_orig t_edf
      by rewrite scheduled_at_def; apply /eqP.
    move: (scheduled_job_in_sched_has_later_deadline j_orig t_edf SCHED') => DL_orig.
    rewrite scheduled_at_def /swapped /replace_at.
    case: (boolP((find_swap_candidate sched t_edf j_orig) == t)) => [/eqP EQ| /eqP NEQ].
    - rewrite SCHED_orig => /eqP j_is_orig.
      injection j_is_orig => <-.
      apply leq_trans with (n := t_edf).
      + by apply H_jobs_must_arrive_to_execute.
      + by rewrite -EQ; apply fsc_range1.
    - case (boolP(t_edf == t)) => [/eqP EQ'| /eqP NEQ'].
      + move=> SCHED_j.
        have ARR_j: job_arrival j <= t_edf by apply fsc_found_job_arrival with (sched0 := sched) (j1 := j_orig) => //; rewrite scheduled_at_def.
        by rewrite -EQ'.
      + move=> SCHED_j.
        apply H_jobs_must_arrive_to_execute.
        by rewrite scheduled_at_def /scheduled_in /pstate_instance.
  Qed.

  (** We connect the fact that a job is scheduled in [sched'] to the
     fact that it must be scheduled somewhere in [sched], too, since
     [make_edf_at] does not introduce any new jobs.  *)
  Lemma mea_job_scheduled:
    forall j t,
      scheduled_at sched' j t ->
      exists t', scheduled_at sched j t'.
  Proof.
    rewrite /sched' /make_edf_at.
    move=> j t SCHED_j.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED_orig; last by exists t.
    eapply swap_job_scheduled.
    by exact SCHED_j.
  Qed.

  (** Conversely, if a job is scheduled in [sched], it is also
     scheduled somewhere in [sched'] since [make_edf_at] does not lose
     any jobs. *)
  Lemma mea_job_scheduled':
    forall j t,
      scheduled_at sched j t ->
      exists t', scheduled_at sched' j t'.
  Proof.
    move=> j t SCHED_j.
    rewrite /sched' /make_edf_at.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED_orig;
      last by exists t.
    eapply swap_job_scheduled_original.
    by exact SCHED_j.
  Qed.

  (** Next, we observe that if all jobs in [sched] come from a given
     arrival sequence, then that's still the case in [sched'], too. *)
  Section ArrivalSequence.

    (** For given arrival sequence,... *)
    Variable arr_seq: arrival_sequence Job.

    (** ...if all jobs in [sched] come from the arrival sequence,... *)
    Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

    (** ...then all jobs in [sched'] do, too. *)
    Lemma mea_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched' arr_seq.
    Proof.
      rewrite /sched' /make_edf_at.
      destruct (sched t_edf) as [j_orig|] eqn:SCHED_orig;
        last by done.
      by apply swapped_jobs_come_from_arrival_sequence.
    Qed.

  End ArrivalSequence.

  (** For the final claim, assume that [EDF_at] already holds
     everywhere prior to time [t_edf], i.e., that [sched] consists of
     an EDF prefix. *)
  Hypothesis H_EDF_prefix: forall t, t < t_edf -> EDF_at sched t.

  (** We establish a key property of [make_edf_at]: not only does it
     ensure [EDF_at] at time [t_edf], it also maintains the fact that
     the schedule has an EDF prefix prior to time [t_edf]. In other
     words, it grows the EDF prefix by one time unit. *)
  Lemma mea_EDF_widen:
    forall t, t <= t_edf -> EDF_at sched' t.
  Proof.
    move=> t.
    rewrite leq_eqVlt => /orP [/eqP EQ|LT] ;
      first by rewrite EQ; apply make_edf_at_guarantee.
    rewrite /sched' /make_edf_at.
    destruct (sched t_edf) as [j_orig|] eqn:SCHED_edf; last by apply H_EDF_prefix.
    move=> j SCHED_j t' j' LE_t_t' SCHED_j' ARR_j'.
    have SCHED_edf': scheduled_at sched j_orig t_edf
      by rewrite scheduled_at_def; apply /eqP.
    have LT_t_fsc:  t < find_swap_candidate sched t_edf j_orig.
    {
      apply ltn_leq_trans with (n := t_edf) => //.
      apply fsc_range1 => //.
      by apply scheduled_job_in_sched_has_later_deadline.
    }
    move: SCHED_j.
    have ->: scheduled_at (swapped sched t_edf (find_swap_candidate sched t_edf j_orig)) j t = scheduled_at sched j t
      by apply swap_job_scheduled_other_times; [move: LT | move: LT_t_fsc]; rewrite ltn_neqAle => /andP [NEQ _]; rewrite eq_sym.
    move => SCHED_j.
    move: (H_EDF_prefix t LT). rewrite /EDF_at => EDF.
    move: (SCHED_j').
    move: (swap_job_scheduled_cases _ _ _ _ _ SCHED_j') => [->|[[EQ ->]|[EQ ->]]] SCHED_j'_orig.
    - by apply EDF with (t' := t').
    - by apply EDF with (t' := (find_swap_candidate sched t_edf j_orig)) => //; apply ltnW.
    - by apply EDF with (t' := t_edf) => //; apply ltnW.
  Qed.

End MakeEDFAtFacts.


(** In the following section, we establish properties of [edf_transform_prefix]. *)
Section EDFPrefixFacts.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved...  *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...and in which no scheduled job misses a deadline. *)
  Hypothesis H_no_deadline_misses: all_deadlines_met sched.

  (** Consider any point in time, denoted [horizon], and... *)
  Variable horizon: instant.

  (** ...let [sched'] denote the schedule obtained by transforming
     [sched] up to the horizon. *)
  Let sched' := edf_transform_prefix sched horizon.

  (** To start, we observe that [sched'] is still well-behaved and
     without deadline misses. *)
  Lemma edf_prefix_well_formedness:
    completed_jobs_dont_execute sched'
    /\
    jobs_must_arrive_to_execute sched'
    /\
    all_deadlines_met sched'.
  Proof.
    rewrite /sched' /edf_transform_prefix.
    apply prefix_map_property_invariance; last by split.
    move=> sched'' t [COMP [ARR DL_MET]].
    split; last split.
    - apply mea_completed_jobs => //.
    - apply mea_jobs_must_arrive => //.
    - apply mea_no_deadline_misses => //.
  Qed.

  (** Because it is needed frequently, we extract the second clause of
     the above conjunction as a corollary. *)
  Corollary edf_prefix_jobs_must_arrive:
    jobs_must_arrive_to_execute sched'.
  Proof. by move: edf_prefix_well_formedness => [_ [ARR _]]. Qed.

  (** We similarly observe that the absence of deadline misses implies
     that any scheduled job must have a deadline at a time later then
     when it is scheduled. *)
  Corollary edf_prefix_scheduled_job_has_later_deadline:
    forall j t,
      scheduled_at sched' j t ->
      job_deadline j > t.
  Proof.
    move=> j t SCHED.
    move: edf_prefix_well_formedness => [COMP [ARR DL_MET]].
    apply (scheduled_at_implies_later_deadline sched') => //.
    - by apply ideal_proc_model_ensures_ideal_progress.
    - by apply (DL_MET j t).
  Qed.

  (** Since no jobs are lost or added to the schedule by
     [edf_transform_prefix], we if a job is scheduled in the
     transformed schedule, then it is also scheduled at some point in
     the original schedule. *)
  Lemma edf_prefix_job_scheduled:
    forall j t,
      scheduled_at sched' j t ->
      exists t', scheduled_at sched j t'.
  Proof.
    rewrite /sched' /edf_transform_prefix.
    move=> j.
    apply prefix_map_property_invariance;
      last by move=> t SCHED; exists t.
    move=> sched'' t'' EX t''' SCHED_mea.
    move: (mea_job_scheduled _ _ _ _ SCHED_mea) => [t'''' SCHED''''].
      by apply: (EX t'''' SCHED'''').
  Qed.

  (** Conversely, if a job is scheduled in the original schedule, it is
     also scheduled at some point in the transformed schedule. *)
  Lemma edf_prefix_job_scheduled':
    forall j t,
      scheduled_at sched j t ->
      exists t', scheduled_at sched' j t'.
  Proof.
    move=> j t SCHED_j.
    rewrite /sched' /edf_transform_prefix.
    apply prefix_map_property_invariance; last by exists t.
    move=> schedX tx [t' SCHEDX_j].
    eapply mea_job_scheduled'.
    by exact SCHEDX_j.
  Qed.

  (** Next, we note that [edf_transform_prefix] maintains the
     property that all jobs stem from a given arrival sequence. *)
  Section ArrivalSequence.

    (** For any arrival sequence,... *)
    Variable arr_seq: arrival_sequence Job.

    (** ...if all jobs in the original schedule come from the arrival sequence,... *)
    Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

    (** ...then all jobs in the transformed schedule still come from
       the same arrival sequence. *)
    Lemma edf_prefix_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched' arr_seq.
    Proof.
      rewrite /sched' /edf_transform_prefix.
      apply prefix_map_property_invariance; last by done.
      move => schedX t ARR.
      by apply mea_jobs_come_from_arrival_sequence.
    Qed.

  End ArrivalSequence.

  (** We establish the key property of [edf_transform_prefix]: that it indeed
     ensures that the resulting schedule ensures the EDF invariant up to the
     given [horizon].  *)
  Lemma edf_prefix_guarantee:
    forall t,
      t < horizon ->
      EDF_at sched' t.
  Proof.
    move=> t IN_PREFIX.
    rewrite /sched' /edf_transform_prefix.
    apply prefix_map_pointwise_property
      with (Q := EDF_at)
           (P := (fun sched => completed_jobs_dont_execute sched
                               /\
                               jobs_must_arrive_to_execute sched
                               /\
                               all_deadlines_met sched))=> //.
    - move=> schedX t_ref [COMP [ARR DL]].
      split; last split.
      + by apply mea_completed_jobs => //.
      + by apply mea_jobs_must_arrive => //.
      + by apply mea_no_deadline_misses => //.
    - move=> schedX t_ref [COMP [ARR DL]].
      by apply mea_EDF_widen.
  Qed.

End EDFPrefixFacts.

(** Finally, we observe that [edf_transform_prefix] is prefix-stable, which
   allows us to replace an earlier horizon with a later horizon.  Note: this is
   in a separate section because we need [edf_prefix_jobs_must_arrive]
   generalized for any schedule. *)
Section EDFPrefixInclusion.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved...  *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...and in which no scheduled job misses a deadline. *)
  Hypothesis H_no_deadline_misses: all_deadlines_met sched.

  Lemma edf_prefix_inclusion:
    forall h1 h2,
      h1 <= h2 ->
      forall t,
        t < h1 ->
        (edf_transform_prefix sched h1) t = (edf_transform_prefix sched h2) t.
  Proof.
    move=> h1 h2 LE_h1_h2 t LT_t_h1.
    induction h2; first by move: (ltn_leq_trans LT_t_h1 LE_h1_h2).
    move: LE_h1_h2. rewrite leq_eqVlt => /orP [/eqP ->|LT]; first by done.
    move: LT. rewrite ltnS => LE_h1_h2.
    rewrite [RHS]/edf_transform_prefix /prefix_map -/prefix_map IHh2 //.
    rewrite {1}/make_edf_at.
    destruct (prefix_map sched make_edf_at h2 h2) as [j|] eqn:SCHED; last by done.
    rewrite -(swap_before_invariant _  h2 (find_swap_candidate (edf_transform_prefix sched h2) h2 j)) // ;
      last by apply ltn_leq_trans with (n := h1).
    have SCHED_j: scheduled_at (edf_transform_prefix sched h2) j h2
      by rewrite scheduled_at_def /edf_transform_prefix; apply /eqP.
    apply fsc_range1 => //.
    - by apply edf_prefix_jobs_must_arrive.
    - apply edf_prefix_scheduled_job_has_later_deadline with (sched0 := sched) (horizon := h2) => //.
  Qed.

End EDFPrefixInclusion.


(** In the following section, we finally establish properties of the
    overall EDF transformation[edf_transform]. *)
Section EDFTransformFacts.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved...  *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...and in which no scheduled job misses a deadline. *)
  Hypothesis H_no_deadline_misses: all_deadlines_met sched.

  (** In the following, let [sched_edf] denote the EDF schedule obtained by
     transforming the given reference schedule. *)
  Let sched_edf := edf_transform sched.

  (** We begin with the first key property: the resulting schedule is actually
     an EDF schedule. *)
  Theorem edf_transform_ensures_edf:
    EDF_schedule sched_edf.
  Proof.
    rewrite /EDF_schedule /sched_edf  /edf_transform => t.
    rewrite /EDF_at //=  => j SCHED_j t' j' LE_t_t' SCHED_j' ARR_j'.
    move: SCHED_j.
    rewrite scheduled_at_def.
    have ->: edf_transform_prefix sched t.+1 t = edf_transform_prefix sched t'.+1 t
      by apply edf_prefix_inclusion.
    rewrite -scheduled_at_def.
    move=> SCHED_j.
    move: (edf_prefix_guarantee sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_no_deadline_misses t'.+1 t) => EDF.
    feed EDF; first by done.
    by apply (EDF j SCHED_j t' j' LE_t_t').
  Qed.

  (** Next, we observe that completed jobs still don't execute in the resulting
     EDF schedule. This observation is needed to establish that the resulting
     EDF schedule is valid. *)
  Lemma edf_transform_completed_jobs_dont_execute:
    completed_jobs_dont_execute sched_edf.
  Proof.
    move=> j t.
    rewrite /sched_edf /edf_transform /service /service_during.
    have ->: \sum_(0 <= t0 < t) service_at (fun t1 : instant => edf_transform_prefix sched t1.+1 t1) j t0 =
             \sum_(0 <= t0 < t) service_at (edf_transform_prefix sched t.+1) j t0.
    {
      apply eq_big_nat => t' /andP [_ LT_t].
      rewrite /service_at.
      rewrite (edf_prefix_inclusion _ _ _ _ t'.+1 t.+1) => //.
      by apply ltn_trans with (n := t).
    }
    set S := (edf_transform_prefix sched t.+1).
    rewrite -/(service_during S j 0 t) -/(service S j t) {}/S.
    move: (edf_prefix_well_formedness sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_no_deadline_misses t.+1) => [COMP _].
    by apply COMP.
  Qed.

  (** Similarly, we observe that no job is scheduled prior to its arrival. *)
  Lemma edf_transform_jobs_must_arrive:
    jobs_must_arrive_to_execute sched_edf.
  Proof.
    move=> j t.
    rewrite /sched_edf /edf_transform.
    move: (edf_prefix_well_formedness sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_no_deadline_misses t.+1) => [_ [ARR _]].
    by apply ARR.
  Qed.

  (** We next establish the second key property: in the transformed EDF
     schedule, no scheduled job misses a deadline. *)
  Theorem edf_transform_deadlines_met:
    all_deadlines_met sched_edf.
  Proof.
    move=> j t.
    rewrite /sched_edf /edf_transform /job_meets_deadline /completed_by /service /service_during  => SCHED.
    have LT_t_dl: t < job_deadline j
      by apply edf_prefix_scheduled_job_has_later_deadline with (sched0 := sched) (horizon := t.+1).
    set t_dl := (job_deadline j).
    have ->: \sum_(0 <= t0 < t_dl) service_at (fun t1 : instant => edf_transform_prefix sched t1.+1 t1) j t0 =
             \sum_(0 <= t0 < t_dl) service_at (edf_transform_prefix sched t_dl) j t0.
    {
      apply eq_big_nat => t' /andP [_ LT_t].
      rewrite /service_at.
      by rewrite (edf_prefix_inclusion _ _ _ _ t'.+1 t_dl).
    }
    move: SCHED. rewrite scheduled_at_def (edf_prefix_inclusion _ _ _ _ t.+1 t_dl) => // SCHED.
    move: (edf_prefix_well_formedness sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_no_deadline_misses t_dl) => [_ [_ DL]]. move: DL.
    rewrite /all_deadlines_met /job_meets_deadline /completed_by /service /service_during => DL.
    apply: (DL j t)=>//=.
      by rewrite scheduled_at_def.
  Qed.

  (** We observe that no new jobs are introduced: any job scheduled in the EDF
     schedule were also present in the reference schedule. *)
  Lemma edf_transform_job_scheduled:
    forall j t, scheduled_at sched_edf j t -> exists t', scheduled_at sched j t'.
  Proof.
    move=> j t.
    rewrite /sched_edf /edf_transform {1}scheduled_at_def -scheduled_at_def.
    by apply edf_prefix_job_scheduled.
  Qed.

  (** Conversely, we observe that no jobs are lost: any job scheduled in the
     reference schedule is also present in the EDF schedule. *)
  Lemma edf_transform_job_scheduled':
    forall j t, scheduled_at sched j t -> exists t', scheduled_at sched_edf j t'.
  Proof.
    move=> j t SCHED_j.
    have EX: exists t', scheduled_at (edf_transform_prefix sched (job_deadline j)) j t'
      by apply edf_prefix_job_scheduled' with (t0 := t).
    move: EX => [t' SCHED'].
    exists t'.
    rewrite /sched_edf /edf_transform scheduled_at_def.
    rewrite (edf_prefix_inclusion _ _ _ _ t'.+1 (job_deadline j)) -?scheduled_at_def=> //.
    by apply edf_prefix_scheduled_job_has_later_deadline with (sched0 := sched) (horizon := job_deadline j).
  Qed.

  (** Next, we note that [edf_transform] maintains the property that all jobs
     stem from a given arrival sequence. *)
  Section ArrivalSequence.

    (** For any arrival sequence,... *)
    Variable arr_seq: arrival_sequence Job.

    (** ...if all jobs in the original schedule come from the arrival sequence,... *)
    Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

    (** ...then all jobs in the transformed EDF schedule still come from the
       same arrival sequence. *)
    Lemma edf_transform_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched_edf arr_seq.
    Proof.
      rewrite /sched_edf /edf_transform.
      move=> j t.
      rewrite scheduled_at_def - scheduled_at_def.
      by apply (edf_prefix_jobs_come_from_arrival_sequence sched t.+1 arr_seq H_from_arr_seq).
    Qed.

  End ArrivalSequence.

End EDFTransformFacts.

(** Finally, we state the theorems that jointly make up the EDF optimality claim. *)
Section Optimality.
  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... consider an arbitrary valid job arrival sequence ... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ... and an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ... that corresponds to the given arrival sequence. *)
  Hypothesis H_sched_valid: valid_schedule sched arr_seq.

  (** In the following, let [equivalent_edf_schedule] denote the schedule that
     results from the EDF transformation. *)
  Let equivalent_edf_schedule := edf_transform sched.

  Section AllDeadlinesMet.

    (** Suppose no job scheduled in the given reference schedule misses a deadline. *)
    Hypothesis H_no_deadline_misses: all_deadlines_met sched.

    (** Then the resulting EDF schedule is a valid schedule for the given
       arrival sequence... *)
    Theorem edf_schedule_is_valid:
      valid_schedule equivalent_edf_schedule arr_seq.
    Proof.
      move: H_sched_valid => [COME READY].
      rewrite /valid_schedule; split;
        first by apply edf_transform_jobs_come_from_arrival_sequence.
      have ARR  := jobs_must_arrive_to_be_ready sched READY.
      have COMP := completed_jobs_are_not_ready sched READY.
      apply basic_readiness_compliance.
      - by apply edf_transform_jobs_must_arrive.
      - by apply edf_transform_completed_jobs_dont_execute.
    Qed.

    (** ...and no scheduled job misses its deadline. *)
    Theorem edf_schedule_meets_all_deadlines:
      all_deadlines_met equivalent_edf_schedule.
    Proof.
      move: H_sched_valid => [COME READY].
      have ARR  := jobs_must_arrive_to_be_ready sched READY.
      have COMP := completed_jobs_are_not_ready sched READY.
      by apply edf_transform_deadlines_met.
    Qed.

  End AllDeadlinesMet.

  (** Next, we strengthen the above "no deadline misses" claim by relating it
     not just to all scheduled jobs, but to all jobs in the given arrival
     sequence. *)
  Section AllDeadlinesOfArrivalsMet.

    (** Suppose no job that's part of the arrival sequence misses a deadline in
       the given reference schedule. *)
    Hypothesis H_no_deadline_misses_of_arrivals: all_deadlines_of_arrivals_met arr_seq sched.

    (** Then no job that's part of the arrival sequence misses a deadline in the
       EDF schedule, either. *)
    Theorem edf_schedule_meets_all_deadlines_wrt_arrivals:
      all_deadlines_of_arrivals_met arr_seq equivalent_edf_schedule.
    Proof.
      move=> j ARR_j.
      move: H_sched_valid => [COME READY].
      have ARR  := jobs_must_arrive_to_be_ready sched READY.
      have COMP := completed_jobs_are_not_ready sched READY.
      destruct (job_cost j ==  0) eqn:COST.
      - move: COST => /eqP COST.
        rewrite /job_meets_deadline /completed_by COST.
        by apply leq0n.
      - move: (neq0_lt0n COST) => NONZERO.
        move: (H_no_deadline_misses_of_arrivals j ARR_j). rewrite {1}/job_meets_deadline => COMP_j.
        move: (completed_implies_scheduled_before sched j NONZERO ARR (job_deadline j) COMP_j) => [t' [_ SCHED']].
        move: (all_deadlines_met_in_valid_schedule arr_seq sched COME H_no_deadline_misses_of_arrivals) => NO_MISSES.
        move: (edf_transform_job_scheduled' sched ARR COMP NO_MISSES j t' SCHED') => [t'' SCHED''].
        move: (edf_schedule_meets_all_deadlines NO_MISSES) => DL_MET.
        by apply: (DL_MET j t'' SCHED'').
    Qed.

  End AllDeadlinesOfArrivalsMet.

End Optimality.
