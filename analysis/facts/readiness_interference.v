Require Export prosa.analysis.definitions.readiness_interference.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.facts.interference.
Require Export prosa.analysis.definitions.service_inversion.readiness_aware.

(** In this file, we establish some important results regarding readiness interference. *)

Section ReadinessInterference.
  (** Consider any kind of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any processor state model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any notion of job readiness. *)
  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence of jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** and any valid schedule .*)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Consider any JLFP priority policy. *)
  Context {JLFP : JLFP_policy Job}.

  (** We establish a few basic lemmas. *)
  Section BasicLemmas.

    (** We prove a trivial result that readiness interference is exclusive of
        the interference due other higher-or-equal-priority jobs. *)
    Lemma no_hep_ready_implies_no_another_hep_interference :
      forall j t,
        no_hep_ready arr_seq sched j t ->
        ~~ another_hep_job_interference arr_seq sched j t.
    Proof.
      move=> j t /allP NO_HEP_READY.
      apply/negP => /hasP[jo INjo /andP[HEP NEQ]].
      move: INjo; rewrite mem_filter => /andP[SERVjo INjo].
      have SCHEDjo : scheduled_at sched jo t by apply service_at_implies_scheduled_at.
      have PENDjo : pending sched jo t by apply scheduled_implies_pending.
      have READYjo : job_ready sched jo t by done.
      have IN : jo \in [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j].
      { rewrite mem_filter.
        by do 2! [apply /andP; split; eauto]. }
      by move: (NO_HEP_READY jo IN); rewrite READYjo.
    Qed.

    (** Next, we prove that there readiness interference is exclusive of
        service inversion. *)
    Lemma no_hep_ready_implies_no_service_inversion :
      forall j t,
        no_hep_ready arr_seq sched j t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t /allP NO_HEP_READY.
      apply /negP => /andP[/hasP[jo INjo HEPjo] LP_SERV].
      move: INjo; rewrite mem_filter => /andP[READYjo INjo].
      have PENDjo : pending sched jo t by done.
      have IN : jo \in [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j].
      { rewrite mem_filter.
        by do 2! [apply /andP; split; eauto]. }
      by move: (NO_HEP_READY jo IN); rewrite READYjo.
    Qed.

  End BasicLemmas.

  (** In this section we establish some bounds on readiness interference. *)
  Section ReadinessInterferenceBound.

    (** Consider any job [j]. *)
    Variable j : Job.

    (** As a first step, we prove a simpler result. *)
    Section Step1.

      (** Consider any instant [t]. *)
      Variable t : instant.

      (** Now, consider some job [jo] that is part of the arrival sequence
          and has a higher-or-equal-priority w.r.t j. *)
      Variable jo : Job.
      Hypothesis H_arrives : arrives_in arr_seq jo.
      Hypothesis H_hepj' : hep_job jo j.

      (** Assume that [jo] is pending at [t]. *)
      Hypothesis H_pending : pending sched jo t.

      (** We prove a trivial result that [jo] is not ready when [no_hep_ready]
          is true at [t]. *)
      Lemma readiness_interference_implies_hep_not_ready:
        no_hep_ready arr_seq sched j t ->
        ~~ job_ready sched jo t.
      Proof.
        move=> /allP NO_HEP_READY.
        have ARRjo : jo \in arrivals_up_to arr_seq t.
        { apply job_in_arrivals_between => //=.
          by move: H_pending => /andP[? ?]. }
        have INjo : jo \in [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j]
          by rewrite mem_filter; do 2! [apply /andP; split; eauto].
        by move: (NO_HEP_READY jo INjo).
      Qed.

    End Step1.

    (** In this section, we use the above result to prove a bound on the total
        readiness interference. *)
    Section Bound1.

      (** Consider any interval <<[t1, t2)>>. *)
      Variable t1 t2 : instant.

      (** Now, assume there exists some job [jo] that is part of the arrival
          sequence and has a higher-or-equal-priority with respect to [j]. *)
      Variable jo : Job.
      Hypothesis HEPjo : hep_job jo j.
      Hypothesis ARRjo : arrives_in arr_seq jo.

      (** Assume that [jo] remains pending throughout the interval of interest. *)
      Hypothesis H_pending :
        forall t,
          t1 <= t < t2 ->
          pending sched jo t.

      (** This is a direct corollary of the result in the above section. We
          show that the total interference incurred by [j] due to [readiness interference]
          is bounded by the total duration [jo] remains not ready. *)
      Corollary readiness_interference_bounded_by_job_readiness_bound:
        cumulative_readiness_interference arr_seq sched j t1 t2
        <= \sum_(t1 <= t < t2) ~~ job_ready sched jo t.
      Proof.
        rewrite leq_sum_seq //= => t /[! mem_index_iota]INt _.
        have -> //= : forall a b : bool, (a -> b) -> a <= b by lia.
        by apply readiness_interference_implies_hep_not_ready.
      Qed.

    End Bound1.

    (** In this section, we prove another bound on [cumulative_readiness_interference]. *)
    Section Bound2.

      (** Consider any interval <<[t1, t2)>>. *)
      Variable t1 t2 : instant.

      (** Assume that, at every instance in the interval, there exists some
          pending higher-or-equal-priority job. *)
      Hypothesis H_pending_job_exists :
        forall t,
          t1 <= t < t2 ->
          (exists2 jo,
          jo \in arrivals_up_to arr_seq t
          & (pending sched jo t && hep_job jo j)).

      (** We show that the total interference incurred by [j] due to [readiness interference]
          in an interval is bounded by the sum of the duration each of the
          higher-or-equal-priority jobs remains not ready. *)
      Lemma readinesss_interference_bounded_by_total_readines_bound:
        \sum_(t1 <= t < t2) no_hep_ready arr_seq sched j t
        <= \sum_(t1 <= t < t2) \sum_(j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j) ~~ job_ready sched j' t.
      Proof.
        rewrite leq_sum_seq //= => t /[! mem_index_iota]INt _.
        have [/allP T | F] := boolP (no_hep_ready arr_seq sched j t); try by lia.
        move: (H_pending_job_exists t INt) => [jhp ARRjhp /andP[PENDjhp HEP]].
        have LT : job_arrival jhp < t.+1
          by move: PENDjhp => /andP[LEQ _]; rewrite /has_arrived in LEQ; lia.
        have GEQ : job_arrival jhp >= 0 by lia.
        have ARRsIN: jhp \in [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j]
          by rewrite mem_filter; do 2! [apply /andP; split; eauto].
        rewrite (big_rem jhp) //= PENDjhp HEP //=.
        by move: (T jhp ARRsIN) ->.
      Qed.

    End Bound2.

  End ReadinessInterferenceBound.

End ReadinessInterference.
