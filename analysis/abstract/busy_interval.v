Require Export prosa.analysis.abstract.iw_auxiliary.
Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.abstract.definitions.

(** * Lemmas About Abstract Busy Intervals *)

(** In this file we prove a few basic lemmas about the notion of
    an abstract busy interval. *)
Section LemmasAboutAbstractBusyInterval.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** Next, consider any work-conserving schedule of this arrival sequence
      ... *)
  Variable sched : schedule PState.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... where jobs do not execute before their arrival. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Consider an arbitrary job [j] with positive cost. Notice that a
      positive-cost assumption is required to ensure that one cannot
      construct a busy interval without any workload inside of it. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** We first prove that any interval <<[t1, t2)>> is either a busy
      interval of job [j] or not. *)
  Lemma busy_interval_prefix_case :
    forall t1 t2,
      busy_interval_prefix sched j t1 t2 \/ ~ busy_interval_prefix sched j t1 t2.
  Proof.
    move=> t1 t2.
    have [JA|NAT] := boolP (t1 <= job_arrival j < t2); last first.
    { by right; move => PREF; move: NAT => /negP NQT; apply: NQT; apply PREF. }
    have [QT1|NQT] := boolP (quiet_time sched j t1); last first.
    { by right; move => PREF; move: NQT => /negP NQT; apply: NQT; apply PREF. }
    have [AQT|NQT] := boolP (all (fun t => ~~ quiet_time sched j t) (index_iota t1.+1 t2)); last first.
    { right; move=> PREF; move: NQT => /negP NQT; apply: NQT.
      apply/allP => t IO; apply/negP.
      by apply PREF; move: IO; rewrite mem_index_iota.
    }
    left; split; [by done | split] => //.
    move => t NEQ; apply/negP; move: AQT => /allP AQT; apply: AQT.
    by rewrite mem_index_iota.
  Qed.

  (** Consider two intervals <<[t1, t2)>> ⊆ <<[t1, t2')>>, where
      <<[t1, t2)>> is a busy-interval prefix and <<[t1, t2')>> is not
      a busy-interval prefix. Then there exists [t2''] such that
      <<[t1, t2'')>> is a busy interval. *)
  Lemma terminating_busy_prefix_is_busy_interval :
    forall t1 t2 t2',
      t2 <= t2' ->
      busy_interval_prefix sched j t1 t2 ->
      ~ busy_interval_prefix sched j t1 t2' ->
      exists t2'', busy_interval sched j t1 t2''.
  Proof.
    move=> t1 t2 t2' LE BUSY NBUSY.
    interval_to_duration t2 t2' δ.
    induction δ as [ | δ IHδ].
    { by exfalso; apply: NBUSY; rewrite addn0. }
    have [BUSY'|NBUSY'] := busy_interval_prefix_case t1 (t2 + δ); last by apply IHδ in NBUSY'.
    clear IHδ.
    exists (t2 + δ); split => //.
    apply negbNE; apply/negP => FF.
    apply:NBUSY; split; first by move: BUSY => []; lia.
    split; first by move: BUSY => []; lia.
    move => t; rewrite addnS ltnS [_ <= t2  + δ]leq_eqVlt.
    move => /andP [LT1 /orP [/eqP WDFW | VB]].
    - by subst; apply/negP.
    - by apply BUSY'; lia.
  Qed.

  (** Next, consider a busy interval <<[t1, t2)>> of job [j]. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval : busy_interval sched j t1 t2.

  (** First, we prove that job [j] completes by the end of the busy
      interval. Note that the busy interval contains the execution of
      job [j]; in addition, time instant [t2] is a quiet time. Thus by
      the definition of a quiet time the job must be completed
      before time [t2]. *)
  Lemma job_completes_within_busy_interval :
    completed_by sched j t2.
  Proof.
    move: (H_busy_interval) => [[/andP [_ LT] _] /andP [_ QT2]].
    unfold quiet_time, pending_earlier_and_at, pending, has_arrived in QT2.
    move: QT2; rewrite negb_and => /orP [QT2|QT2].
    { by move: QT2 => /negP QT2; exfalso; apply QT2, ltnW. }
    by rewrite Bool.negb_involutive in QT2.
  Qed.

  (** We show that, similarly to the classical notion of busy
      interval, the job does not receive service before the busy
      interval starts. *)
  Lemma no_service_before_busy_interval :
    forall t, service sched j t = service_during sched j t1 t.
  Proof.
    move => t; move : (H_busy_interval) => [[/andP [LE1 LE2] [QT1 AQT]] QT2].
    destruct (leqP t1 t) as [NEQ1|NEQ1]; first destruct (leqP t2 t) as [NEQ2|NEQ2].
    - apply/eqP; rewrite eqn_leq; apply/andP; split.
      + rewrite /service -(service_during_cat _ _ _ t1);
          [ | by apply/andP; split; lia].
        by rewrite cumulative_service_before_job_arrival_zero; eauto 2.
      + rewrite /service -[in X in _ <= X](service_during_cat _ _ _ t1);
          [ | by apply/andP; split; lia].
        by (erewrite cumulative_service_before_job_arrival_zero with (t1 := 0)
           || erewrite cumulative_service_before_job_arrival_zero with (t3 := 0)).
    - rewrite /service -(service_during_cat _ _ _ t1);
        [ | by apply/andP; split; lia].
      by rewrite cumulative_service_before_job_arrival_zero; eauto 2.
    - rewrite service_during_geq; last by lia.
      by rewrite /service cumulative_service_before_job_arrival_zero//; lia.
  Qed.

  (** Since the job cannot arrive before the busy interval starts and
      completes by the end of the busy interval, it receives at least
      [job_cost j] units of service within the interval. *)
  Lemma service_within_busy_interval_ge_job_cost :
    job_cost j <= service_during sched j t1 t2.
  Proof.
    move : (H_busy_interval) => [[/andP [LE1 LE2] [QT1 AQT]] QT2].
    rewrite -[service_during _ _ _ _]add0n.
    rewrite -(cumulative_service_before_job_arrival_zero sched j _ 0 _ LE1)//.
    rewrite service_during_cat; last by apply/andP; split; lia.
    rewrite  -/(completed_by sched j t2).
    exact: job_completes_within_busy_interval.
  Qed.

  (** Trivially, job [j] arrives before the end of the busy window (if arrival
      times are consistent), which is a useful fact to observe for proof
      automation. *)
  Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.
  Fact abstract_busy_interval_arrivals_before :
    j \in arrivals_before arr_seq t2.
  Proof.
    move: (H_busy_interval) => [[/andP [_ LT] _] _].
    by apply: arrived_between_implies_in_arrivals.
  Qed.

  (** For the same reason, we note the trivial fact that by definition [j]
      arrives no earlier than at time [t1]. For automation, we note this both as
      a fact on busy-interval prefixes ... *)
  Fact abstract_busy_interval_prefix_job_arrival :
    forall t t',  busy_interval_prefix sched j t t' -> t <= job_arrival j.
  Proof.
    by move=> ? ? [/andP [GEQ _] _].
  Qed.

  (** ... and complete busy-intervals. *)
  Fact abstract_busy_interval_job_arrival :
    t1 <= job_arrival j.
  Proof.
    move: H_busy_interval => [PREFIX _].
    exact: abstract_busy_interval_prefix_job_arrival.
  Qed.

  (** Next, let us assume that the introduced processor model is
      unit-supply. *)
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** Under this assumption, the sum of the total service during the
      time interval <<[t1, t1 + Δ)>> and the cumulative interference
      during the same interval is bounded by the length of the time
      interval. *)
  Lemma service_and_interference_bound :
    forall Δ,
      t1 + Δ <= t2 ->
      service_during sched j t1 (t1 + Δ) + cumulative_interference j t1 (t1 + Δ) <= Δ.
  Proof.
    move=> Δ LE; rewrite -big_split //= -{2}(sum_of_ones t1 Δ).
    rewrite big_nat [in X in _ <= X]big_nat; apply leq_sum => t /andP[Lo Hi].
    move: (H_work_conserving j t1 t2 t) => Workj.
    feed_n 4 Workj => //.
    { by move: H_busy_interval => [PREF QT]. }
    { by apply/andP; split; lia. }
    rewrite /cond_interference //=; move: Workj; case: interference => Workj.
    - by rewrite addn1 ltnS; move_neq_up NE; apply Workj.
    - by rewrite addn0; apply: H_unit_service_proc_model.
  Qed.

End LemmasAboutAbstractBusyInterval.

(** In the following section, we derive a sufficient condition for the
    existence of abstract busy intervals for unit-service
    processors. *)
Section AbstractBusyIntervalExists.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of of unit-service processor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** Assume we are provided with abstract functions for interference
      and interfering workload ... *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** ... that do not allow speculative execution. *)
  Hypothesis H_no_speculative_exec : no_speculative_execution.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arrival_sequence_is_a_set : arrival_sequence_uniq arr_seq.

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** Next, consider any work-conserving (in the abstract sense)
      schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an arbitrary job [j] from task [tsk] with positive cost. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_task : job_of_task tsk j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** In this section, we prove a fact that allows one to extend an
      inequality between cumulative interference and interfering
      workload from a busy-interval prefix <<[t1, t)>> to the whole
      timeline <<[0, t)>>. *)
  Section CumulativeIntIntWorkExtension.

    (** Consider any busy-interval prefix of job [j]. *)
    Variable t1 t_busy : instant.
    Hypothesis H_is_busy_prefix : busy_interval_prefix sched j t1 t_busy.+1.

      (** We assume that, for some positive [δ], the cumulative
          interfering workload within interval <<[t1, t1 + δ)>> is
          bounded by cumulative interference in the same interval. *)
    Variable δ : duration.
    Hypothesis H_iw_bounded :
      cumulative_interfering_workload j t1 (t1 + δ) <= cumulative_interference j t1 (t1 + δ).

    (** Then the cumulative interfering workload within interval <<[0, t1 + δ)>>
        is bounded by the cumulative interference in the
        same interval. *)
      Local Lemma cumul_iw_bounded_by_cumul_i :
        cumulative_interfering_workload j 0 (t1 + δ) <= cumulative_interference j 0 (t1 + δ).
      Proof.
        move: (H_iw_bounded) => LE.
        rewrite /definitions.cumulative_interference
                /definitions.cumulative_interfering_workload
                /cumul_cond_interference.
        rewrite (@big_cat_nat _ _ _ t1) //=; last by lia.
        rewrite [in X in _ <= X](@big_cat_nat _ _ _ t1) //=; last by lia.
        move: H_is_busy_prefix => [_  [/andP [/eqP DD KK ] ADD]].
        rewrite /cumulative_interfering_workload in LE; rewrite (leqRW LE); clear LE.
        rewrite leq_add2r.
        rewrite /cumulative_interfering_workload in DD.
        by rewrite -DD; clear DD.
      Qed.

  End CumulativeIntIntWorkExtension.

  (** In the following section, we show that the busy interval is
      bounded. More specifically, we show that the length of any
      abstract busy interval is bounded, as long as there is enough
      supply to accommodate the interfering workload.  *)
  Section BoundingBusyInterval.

    (** For simplicity, let us define some local names. *)
    Let quiet_time t := quiet_time sched j t.
    Let busy_interval_prefix := busy_interval_prefix sched j.
    Let busy_interval := busy_interval sched j.

    (** Suppose that job [j] is pending at time [t_busy]. *)
    Variable t_busy : instant.
    Hypothesis H_j_is_pending : pending sched j t_busy.

    (** First, we show that there must exist a busy interval prefix. *)
    Section LowerBound.

      (** Since job [j] is pending at time [t_busy], there is a
          (potentially unbounded) busy interval that starts no later
          than with the arrival of [j]. *)
      Lemma exists_busy_interval_prefix :
        exists t1,
          busy_interval_prefix t1 t_busy.+1 /\
          t1 <= job_arrival j <= t_busy.
      Proof.
        rename H_j_is_pending into PEND.
        destruct ([exists t:'I_t_busy.+1, quiet_time t]) eqn:EX.
        { set (last0 := \max_(t < t_busy.+1 | quiet_time t) t).
          move: EX => /existsP [t EX].
          have PRED: quiet_time last0 by apply (bigmax_pred t_busy.+1 (quiet_time) t).
          move: PRED => QUIET.
          exists last0.
          have JARRIN: last0 <= job_arrival j <= t_busy.
          { move: PEND => /andP [ARR NCOM].
            apply/andP; split => //. move: QUIET => /andP [_ PE]. 
            move: PE; rewrite negb_and -leqNgt => /orP [ | /negPn COMPL] => //; exfalso.
            apply completion_monotonic with (t' := t_busy) in COMPL.
            - by move: NCOM => /negP.
            - by rewrite -ltnS; eapply bigmax_ltn_ord.
          }
          repeat split; auto 2; try apply QUIET => //=.
          move => t0 /andP [GTlast LTbusy] QUIET0.
          move_neq_down GTlast.
          by eapply (@leq_bigmax_cond
                       _ (fun (x: 'I_t_busy.+1) => quiet_time x)
                       (fun x => x) (Ordinal LTbusy)).
        }
        { apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL.
          exists 0; split; last by apply/andP; split; last by move: PEND => /andP [ARR _].
          repeat split.
          - apply/andP; split => //; rewrite ltnS.
            by move: PEND => /andP PEND; apply PEND.
          - apply/andP; split;
              first by rewrite /cumulative_interference /cumul_cond_interference /cumulative_interfering_workload !big_geq.
            by apply not_pending_earlier_and_at_0.
          - move => t /andP [GE LT] QUIET.
            move: (ALL (Ordinal LT)) => /negP ALL'.
            by apply ALL'.
        }
      Qed.

    End LowerBound.

    (** Next we prove that, if there is a point where the requested
        workload is upper-bounded by the supply, then the busy
        interval eventually ends. *)
    Section UpperBound.

      (** Consider any busy interval prefix of job [j]. *)
      Variable t1 : instant.
      Hypothesis H_is_busy_prefix : busy_interval_prefix t1 t_busy.+1.

      (** We assume that for some positive [δ], the cumulative
          interfering workload within interval <<[t1, t1 + δ)>> is
          bounded by [δ]. *)
      Variable δ : duration.
      Hypothesis H_δ_positive : δ > 0.
      Hypothesis H_workload_is_bounded :
        workload_of_job arr_seq j t1 (t1 + δ)
        + cumulative_interfering_workload j t1 (t1 + δ) <= δ.

      (** If there is a quiet time by time [t1 + δ], it trivially
          follows that the busy interval is bounded. Thus, let's
          consider first the harder case where there is no quiet time,
          which turns out to be impossible. *)
      Section CannotBeBusyForSoLong.

        (** Assume that there is no quiet time in the interval <<(t1, t1 + δ]>>. *)
        Hypothesis H_no_quiet_time : forall t, t1 < t <= t1 + δ -> ~ quiet_time t.

        (** We prove that the sum of cumulative service and cumulative
            interference in the interval <<[t, t + δ)>> is equal to
            [δ]. *)

        (** Since the interval is always non-quiet, the processor is
            always busy processing job [j] and the job's interference
            and, hence, the sum of service of [j] and its cumulative
            interference within the interval <<[t1, t1 + δ)>> is
            greater than or equal to [δ]. *)
        Lemma busy_interval_has_uninterrupted_service :
          δ <= service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ).
        Proof.
          clear H_δ_positive H_workload_is_bounded H_j_is_pending.
          rewrite /service_during /cumulative_interference /cumul_cond_interference  /cond_interference /service_at.
          rewrite -big_split //= -{1}(sum_of_ones t1 δ).
          rewrite big_nat [in X in _ <= X]big_nat.
          apply leq_sum => x /andP[Lo Hi].
          destruct (leqP (t1 + δ) (t_busy.+1)) as [LE|LT].
          { move: (H_work_conserving j t1 t_busy.+1 x) => Workj.
            feed_n 4 Workj; try done.
            { by apply/andP; split; eapply leq_trans; eauto. }
            destruct interference.
            - by lia.
            - by rewrite //= addn0; apply Workj.
          }
          { move: (H_work_conserving j t1 (t1 + δ) x) => Workj.
            feed_n 4 Workj; try done.
            - move: H_is_busy_prefix => [/andP [A1 A2] [QT NQT]]; split; [ | split].
              + by apply/andP; split => //; rewrite (leqRW A2) -(leqRW LT).
              + by apply QT.
              + move => t /andP [A3 A4]; apply H_no_quiet_time.
                by apply/andP; split; lia.
            - by apply/andP; split; eapply leq_trans; eauto 2.
            - destruct interference.
              + by lia.
              + by rewrite //= addn0; apply Workj.
          }
        Qed.

        (** However, since the total workload is bounded (see
            [H_workload_is_bounded]), the sum of [j]'s cost and its
            interfering workload within the interval <<[t1, t1 + δ)>>
            is bounded by [j]'s service and its interference within
            the same time interval. *)
        Lemma busy_interval_too_much_workload :
          job_cost j + cumulative_interfering_workload j t1 (t1 + δ) <=
          service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ).
        Proof.
          replace (job_cost j) with (workload_of_job arr_seq j t1 (t1 + δ));
            first by rewrite (leqRW H_workload_is_bounded)
                     -(leqRW busy_interval_has_uninterrupted_service).
          move: (H_is_busy_prefix) => [/andP [NEQ1 _] _].
          erewrite workload_of_job_eq_job_arrival => //=.
          rewrite NEQ1 Bool.andb_true_l.
          have -> : job_arrival j < t1 + δ; last by done.
          move_neq_up GE.
          apply (H_no_quiet_time (t1 + δ)).
          { by apply/andP; split; [rewrite -addn1 leq_add2l | done]. }
          apply/andP; split.
          - move: (H_workload_is_bounded); rewrite workload_of_job_eq_job_arrival //=.
            rewrite NEQ1 Bool.andb_true_l [_ < _ + _]leqNgt ltnS GE //= add0n => LE.
            rewrite eqn_leq; apply/andP; split.
            + by apply H_no_speculative_exec.
            + apply (cumul_iw_bounded_by_cumul_i _ t_busy) => //=; rewrite (leqRW LE).
              eapply leq_trans; first apply busy_interval_has_uninterrupted_service.
              by have -> : service_during sched j t1 (t1 + δ) = 0
                by rewrite cumulative_service_before_job_arrival_zero.
          - by rewrite /pending_earlier_and_at negb_and;
              apply/orP; left; rewrite -ltnNge ltnS.
        Qed.

        (** The latter two lemmas imply that [t1 + δ] is a quiet time ... *)
        Lemma t1δ_is_quiet : quiet_time (t1 + δ).
        Proof.
          have LW := busy_interval_too_much_workload.
          have NEQ: forall a b c d, a >= c -> b >= d -> a + b <= c + d -> a = c /\ b = d by lia.
          apply NEQ in LW; first destruct LW as [EQ1 EQ2].
          - apply/andP; split.
            + rewrite eqn_leq; apply/andP; split.
              * by apply H_no_speculative_exec.
              * by apply (cumul_iw_bounded_by_cumul_i _ t_busy) => //=; rewrite EQ2.
            + rewrite negb_and Bool.negb_involutive; apply/orP; right.
              rewrite /completed_by EQ1.
              by erewrite <-(service_cat); [apply leq_addl | ]; lia.
          - eapply leq_trans; last by apply service_at_most_cost => //=.
            by erewrite <-(service_cat); [apply leq_addl | ]; lia.
          - move: H_is_busy_prefix => [_ [/andP [/eqP D _] _]].
            rewrite -(leq_add2l (definitions.cumulative_interference j 0 t1)) {2}D.
            rewrite -(big_cat_nat) //=; last by lia.
            by rewrite -(big_cat_nat) //=; last by lia.
        Qed.

        (** ... which is a contradiction with the initial
            assumption. *)
        Lemma t1δ_is_quiet_contra : False.
        Proof.
          eapply H_no_quiet_time; last by apply t1δ_is_quiet.
          apply/andP; split; last by done.
          by rewrite -addn1 leq_add2l.
        Qed.

      End CannotBeBusyForSoLong.

      (** Since the interval cannot remain busy for so long, we prove
          that the busy interval finishes at some point [t2 <= t1 +
          δ]. *)
      Lemma busy_interval_is_bounded :
        exists t2,
          t_busy < t2
          /\ t2 <= t1 + δ
          /\ busy_interval t1 t2.
      Proof.
        move: H_is_busy_prefix => [NEQ [QT NQT]].
        destruct ([exists t2:'I_(t1 + δ).+1, (t2 > t1) && quiet_time t2]) eqn:EX.
        { have EX': exists (t2 : instant), ((t1 < t2 <= t1 + δ) && quiet_time t2).
          { move: EX => /existsP [t2 /andP [LE QUIET]].
            exists t2; apply/andP; split => //;
              by apply/andP; split; last (rewrite -ltnS; apply ltn_ord). }
          move: (ex_minnP EX') => [t2 /andP [/andP [GT LE] QUIET] MIN]; clear EX EX'.
          exists t2; split; [ | split; [ |split; [split; [ | split] | ] ]]; try done.
          { move_neq_up NEQ2.
            move: (H_is_busy_prefix) => [_ [_ NQ]]; apply:(NQ t2) => //.
            by apply/andP; split => //.
          }
          { move: NEQ => /andP [IN1 IN2].
            apply/andP; split => //.
            apply leq_ltn_trans with t_busy; eauto 2.
            rewrite ltnNge; apply/negP; intros CONTR.
            apply NQT with t2 => //.
            by apply/andP; split; last rewrite ltnS.
          }
          { move => t /andP [GT1 LT2] BUG.
            feed (MIN t); first (apply/andP; split) => //.
            { by apply/andP; split; last apply leq_trans with (n := t2); eauto using ltnW. }
            { by lia. }
          }
        }
        { apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL'.
          have ALL: forall t, t1 < t <= t1 + δ -> ~ quiet_time t.
          { move => t /andP [GTt LEt] QUIET; rewrite -ltnS in LEt.
            specialize (ALL' (Ordinal LEt)); rewrite negb_and /= GTt orFb in ALL'. 
            by move: ALL' => /negP ALL'; apply ALL'; clear ALL'.
          }
          by clear ALL'; exfalso; eapply t1δ_is_quiet_contra.
        }
      Qed.

    End UpperBound.

  End BoundingBusyInterval.

End AbstractBusyIntervalExists.


(** We add some facts into the "Hint Database" basic_rt_facts, so Coq will be
    able to apply them automatically where needed. *)
Global Hint Resolve
  abstract_busy_interval_arrivals_before
  job_completes_within_busy_interval
  abstract_busy_interval_prefix_job_arrival
  abstract_busy_interval_job_arrival
  : basic_rt_facts.
