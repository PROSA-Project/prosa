Require Export prosa.model.processor.overhead_resource_model.

(** In this file, we prove a bound on the total blackout time (i.e.,
    time during which no job makes progress due to overheads),
    assuming a given number of schedule changes. *)
Section TotalBlackoutDueToOverheadsBounded.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Consider any valid arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any schedule of this arrival sequence... *)
  Variable sched : schedule (overheads.processor_state Job).

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Finally, we assume that the schedule respects a valid overhead
      resource model with dispatch overhead [DB], context switch
      overhead [CSB], and preemption-related overhead [CRPDB]. *)
  Variable DB CSB CRPDB : duration.
  Hypothesis H_valid_overheads_model :
    overhead_resource_model sched DB CSB CRPDB.

  (** The total blackout duration in the interval <<[t1, t2)>> can be
      decomposed into time spent in dispatching, context switching,
      and CRPD (cache-related preemption delay). *)
  Lemma blackout_during_split :
    forall (t1 t2 : instant),
      blackout_during sched t1 t2
      = total_time_in_dispatch sched t1 t2
        + total_time_in_context_switch sched t1 t2
        + total_time_in_CRPD sched t1 t2.
  Proof.
    move => t1 t2.
    rewrite /blackout_during /total_time_in_dispatch /total_time_in_context_switch /total_time_in_CRPD.
    rewrite -!big_split //= big_nat_cond [RHS]big_nat_cond; apply eq_bigr => t /andP [NEQ _].
    rewrite /is_blackout /has_supply -eqn0Ngt /supply_at /is_dispatch /is_context_switch /is_CRPD.
    by destruct (sched t) eqn:EQ; rewrite /supply_in //= sum_unit1.
  Qed.

  (** If there are no schedule changes in the interval <<[t1, t2)>>,
      then the processor must always be scheduling the same job (or be
      idle). In that case, the total dispatch time in that interval is
      equal to the time spent dispatching a specific job (or be
      idle). *)
  Lemma total_dispatch_time_eq_job_dispatch_time :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      exists (oj : option Job),
        total_time_in_dispatch sched t1 t2
        = time_spent_in_dispatch sched oj t1 t2.
  Proof.
    move=> t1 t2 NSC.
    have [IDLE|[j SCHED]] := scheduled_job_dec sched t1.
    { exists None.
      rewrite /total_time_in_dispatch /time_spent_in_dispatch big_nat_cond [RHS]big_nat_cond.
      apply: eq_bigr => t /andP [NEQ _].
      by eapply no_changes_implies_same_scheduled_job in IDLE; [ by erewrite IDLE | | | ] => //; lia.
    }
    { exists (Some j).
      rewrite /total_time_in_dispatch /time_spent_in_dispatch big_nat_cond [RHS]big_nat_cond.
      apply: eq_bigr => t /andP [NEQ _].
      by eapply no_changes_implies_same_scheduled_job in SCHED; [ erewrite SCHED, eq_refl | | | ] => //; lia.
    }
  Qed.

  (** Similar statements are true for context-switch overhead... *)
  Lemma total_cswitch_time_eq_job_cswitch_time :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      exists (oj : option Job),
        total_time_in_context_switch sched t1 t2
        = time_spent_in_context_switch sched oj t1 t2.
  Proof.
    move=> t1 t2 NSC.
    have [IDLE|[j SCHED]] := scheduled_job_dec sched t1.
    { exists None.
      rewrite /total_time_in_context_switch /time_spent_in_context_switch big_nat_cond [RHS]big_nat_cond.
      apply: eq_bigr => t /andP [NEQ _].
      by eapply no_changes_implies_same_scheduled_job in IDLE; [ by erewrite IDLE | | | ] => //; lia.
    }
    { exists (Some j).
      rewrite /total_time_in_context_switch /time_spent_in_context_switch big_nat_cond [RHS]big_nat_cond.
      apply: eq_bigr => t /andP [NEQ _].
      by eapply no_changes_implies_same_scheduled_job in SCHED; [ erewrite SCHED, eq_refl | | | ] => //; lia.
    }
  Qed.

  (** ... and CRPD. *)
  Lemma total_CRPD_time_eq_job_CRPD_time :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      exists (oj : option Job),
        total_time_in_CRPD sched t1 t2
        = time_spent_in_CRPD sched oj t1 t2.
  Proof.
    move=> t1 t2 NSC.
    have [IDLE|[j SCHED]] := scheduled_job_dec sched t1.
    { exists None.
      rewrite /total_time_in_CRPD /time_spent_in_CRPD big_nat_cond [RHS]big_nat_cond.
      apply: eq_bigr => t /andP [NEQ _].
      by eapply no_changes_implies_same_scheduled_job in IDLE; [ by erewrite IDLE | | | ] => //; lia.
    }
    { exists (Some j).
      rewrite /total_time_in_CRPD /time_spent_in_CRPD big_nat_cond [RHS]big_nat_cond.
      apply: eq_bigr => t /andP [NEQ _].
      by eapply no_changes_implies_same_scheduled_job in SCHED; [ erewrite SCHED, eq_refl | | | ] => //; lia.
    }
  Qed.

  (** If there are no schedule changes in <<[t1, t2)>>, then the
      processor must be scheduling the same job (or be idle)
      throughout. In that case, since the dispatch time spent on a
      specific job is bounded by [DB], the total dispatch time in
      <<[t1, t2)>> is also bounded by [DB]. *)
  Lemma total_time_in_dispatch_is_bounded :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      total_time_in_dispatch sched t1 t2 <= DB.
  Proof.
    move=> t1 t2 NSI; move: (NSI) => NSI2.
    have [Z|POS] := posnP (total_time_in_dispatch sched t1 t2); first by rewrite Z.
    apply total_dispatch_time_eq_job_dispatch_time in NSI2; destruct NSI2 as [oj EQ]; rewrite EQ.
    rewrite EQ in POS; clear EQ.
    move: POS; rewrite sum_nat_gt0 //= => /hasP [t]; rewrite mem_filter //= mem_index_iota.
    move=> NEQ; rewrite lt0b => /andP [/eqP SCHED] _.
    apply H_valid_overheads_model.
    apply/allP => t'; rewrite mem_index_iota => NEQ'; apply/eqP.
    by apply: no_changes_implies_same_scheduled_job; try apply SCHED.
  Qed.

  (** Same reasoning holds for context switches... *)
  Lemma total_time_in_cswitch_is_bounded :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      total_time_in_context_switch sched t1 t2 <= CSB.
  Proof.
    move=> t1 t2 NSI; move: (NSI) => NSI2.
    have [Z|POS] := posnP (total_time_in_context_switch sched t1 t2); first by rewrite Z.
    apply total_cswitch_time_eq_job_cswitch_time in NSI2; destruct NSI2 as [oj EQ]; rewrite EQ.
    rewrite EQ in POS; clear EQ.
    move: POS; rewrite sum_nat_gt0 //= => /hasP [t]; rewrite mem_filter //= mem_index_iota.
    move=> NEQ; rewrite lt0b => /andP [/eqP SCHED] _.
    apply H_valid_overheads_model.
    apply/allP => t'; rewrite mem_index_iota => NEQ'; apply/eqP.
    by apply: no_changes_implies_same_scheduled_job; try apply SCHED.
  Qed.

  (** ... and CRPD. *)
  Lemma total_time_in_CRPD_is_bounded :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      total_time_in_CRPD sched t1 t2 <= CRPDB.
  Proof.
    move=> t1 t2 NSI; move: (NSI) => NSI2.
    have [Z|POS] := posnP (total_time_in_CRPD sched t1 t2); first by rewrite Z.
    apply total_CRPD_time_eq_job_CRPD_time in NSI2; destruct NSI2 as [oj EQ]; rewrite EQ.
    rewrite EQ in POS; clear EQ.
    move: POS; rewrite sum_nat_gt0 //= => /hasP [t]; rewrite mem_filter //= mem_index_iota.
    move=> NEQ; rewrite lt0b => /andP [/eqP SCHED] _.
    apply H_valid_overheads_model.
    apply/allP => t'; rewrite mem_index_iota => NEQ'; apply/eqP.
    by apply: no_changes_implies_same_scheduled_job; try apply SCHED.
  Qed.

  (** If there are no schedule changes in the interval <<[t1+1, t2)>>,
      then the processor executes the same job (or remains idle)
      throughout the interval <<[t1, t2)>>, possibly with some initial
      scheduling activity at [t1]. In that case, the total blackout
      time in <<[t1, t2)>> is at most the sum of: dispatch overhead
      ([DB]), a context switch before ([CSB]), and cache-related
      preemption delay (CRPD).

      We exclude [t1] from the schedule-change check because a change
      between [t1−1] and [t1] is irrelevant for bounding blackout in
      <<[t1, t2)>> as it only affects the boundary. *)
  Lemma no_sched_changes_bounded_overheads_blackout :
    forall (t1 t2 : instant),
      no_schedule_changes_during sched t1 t2 ->
      blackout_during sched t1 t2 <= DB + CSB + CRPDB.
  Proof.
    move=> t1 t2 SINT.
    rewrite blackout_during_split; apply leq_add; first apply leq_add.
    { by eapply total_time_in_dispatch_is_bounded. }
    { by eapply total_time_in_cswitch_is_bounded. }
    { by eapply total_time_in_CRPD_is_bounded. }
  Qed.

  (** If there is exactly one schedule change in the interval <<[t1,
      t2)>>, and it occurs at the very beginning (i.e., at [t1]), then
      the processor schedules a job at [t1] and continues executing
      the same job (or stays idle) for the rest of the interval. *)
  Lemma sched_changes_start_busy_pref_bounded_overheads_blackout :
    forall (t1 t2 : instant),
      number_schedule_changes sched t1 t2 = 1 ->
      schedule_change sched t1 ->
      blackout_during sched t1 t2 <= DB + CSB + CRPDB.
  Proof.
    move=> t1 t2 EQ SC.
    have [NEQ|LT] := leqP t2 t1.
    { by rewrite /blackout_during big_geq //. }
    apply no_sched_changes_bounded_overheads_blackout.
    rewrite (number_schedule_changes_cat _ t1.+1) in EQ; last first.
    { lia. }
    { have EQ1: number_schedule_changes sched t1 t1.+1 = 1.
      { by rewrite /number_schedule_changes /index_iota -addn1 addKn //= SC. }
      rewrite /no_schedule_changes_during; lia.
    }
  Qed.

  (** If there are exactly [k] schedule changes in the interval <<[t1,
      t2)>>, and one of them occurs at the beginning (i.e., at [t1]),
      then the blackout time over the interval is bounded by [(DB +
      CSB + CRPDB) × k]. *)
  Lemma fin_sched_changes_start_busy_pref_bounded_overheads_blackout :
    forall (k : nat) (t1 t2 : instant),
      schedule_change sched t1 ->
      number_schedule_changes sched t1 t2 = k ->
      blackout_during sched t1 t2 <= (DB + CSB + CRPDB) * k.
  Proof.
    move=> k.
    have [B EX]: exists B, k <= B by (exists k).
    move: k EX; induction B as [ | B IHB] => k.
    { rewrite leqn0 => /eqP EQ; subst k => t1 t2 SC EQ.
      have [NEQ|LT] := leqP t2 t1; first by rewrite /blackout_during big_geq //.
      exfalso; move: EQ => /eqP; rewrite eqn0Ngt => /negP EQ; apply: EQ.
      rewrite /number_schedule_changes -has_count; apply/hasP; exists t1.
      - by rewrite mem_index_iota; lia.
      - by done.
    }
    { rewrite leq_eqVlt => /orP [/eqP EQ | LE]; last by rewrite ltnS in LE; apply IHB.
      subst => t1 t2 SC EQ.
      have [NEQ|LT] := leqP t2 t1; [by rewrite /blackout_during big_geq // | ].
      have [Z|POS] := posnP B; [by subst; rewrite muln1; apply sched_changes_start_busy_pref_bounded_overheads_blackout | ].
      have [t [LEQ DECt]]: exists t, t1 < t < t2 /\ schedule_change sched t.
      { clear IHB; rewrite (number_schedule_changes_cat _ t1.+1) in EQ; last by lia.
        { have EQ1: number_schedule_changes sched t1 t1.+1 = 1
            by rewrite / number_schedule_changes /index_iota -addn1 addKn //= SC.
          rewrite EQ1 addnC addn1 in EQ; clear EQ1.
          apply eq_add_S in EQ.
          move: POS; rewrite -EQ /number_schedule_changes -has_count => /hasP [to].
          by rewrite mem_index_iota => NEQ DECto; exists to.
        }
      }
      rewrite -(blackout_during_cat _ _ _ t); last by lia.
      have [nldp EQ1] : exists nldp, number_schedule_changes sched t1 t = nldp by eexists; reflexivity.
      have [nrdp EQ2] : exists nrdp, number_schedule_changes sched t t2 = nrdp by eexists; reflexivity.
      have EQ3: nldp + nrdp = B.+1 by subst; rewrite -EQ -number_schedule_changes_cat //; lia.
      have EQ4: (nldp > 0) && (nrdp > 0).
      { by apply/andP; split; [rewrite -EQ1 | rewrite -EQ2];
        rewrite /number_schedule_changes -has_count;
        apply /hasP; [exists t1 | exists t] => //; rewrite mem_index_iota; lia.
      }
      by rewrite -EQ3 mulnDr; apply leq_add; apply IHB => //; lia.
    }
  Qed.

  (** If there are exactly [k] schedule changes in the interval
      <<[t1+1, t2)>>, then the total blackout time in <<[t1, t2)>> is
      at most [(DB + CSB + CRPDB) × (k + 1)]. *)
  Lemma finite_sched_changes_bounded_overheads_blackout :
    forall (k : nat) (t1 t2 : instant),
      number_schedule_changes sched t1.+1 t2 = k ->
      blackout_during sched t1 t2 <= (DB + CSB + CRPDB) * (k + 1).
  Proof.
    move => k.
    have [Z|POS] := posnP k.
    { subst; move => t1 t2 NSC0.
      rewrite add0n muln1; apply no_sched_changes_bounded_overheads_blackout.
      by rewrite /no_schedule_changes_during NSC0.
    }
    { move => t1 t2 NSC.
      have [t [NEQ [SC [NSC1 NSC2]]]] := first_schedule_change_exists _ _ _ _ POS NSC.
      rewrite mulnDr -(blackout_during_cat _ _ _ t); last by lia.
      rewrite addnC leq_add //.
      { by apply fin_sched_changes_start_busy_pref_bounded_overheads_blackout. }
      { rewrite muln1; apply no_sched_changes_bounded_overheads_blackout.
        by rewrite /no_schedule_changes_during NSC1.
      }
    }
  Qed.

End TotalBlackoutDueToOverheadsBounded.
