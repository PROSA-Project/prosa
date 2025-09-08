Require Export prosa.analysis.abstract.restricted_supply.iw_instantiation.


(** * Helper Lemmas for Bounded Busy Interval Lemmas *)

(** In this section, we introduce a few lemmas that facilitate the
    proof of an upper bound on busy intervals for various priority
    policies in the context of the restricted-supply processor
    model. *)
Section BoundedBusyIntervalsAux.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of fully supply-consuming unit-supply
      uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider a JLFP policy that indicates a higher-or-equal
      priority relation, and assume that the relation is reflexive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider a schedule of this arrival sequence, ... *)
  Variable sched : schedule PState.

  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context `{!JobReady Job PState}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** Recall that [busy_intervals_are_bounded_by] is an abstract
      notion. Hence, we need to introduce interference and interfering
      workload. We will use the restricted-supply instantiations. *)

  (** We say that job [j] incurs interference at time [t] iff it
      cannot execute due to (1) the lack of supply at time [t], (2)
      service inversion (i.e., a lower-priority job receiving service
      at [t]), or a higher-or-equal-priority job receiving service. *)
  #[local] Instance rs_jlfp_interference : Interference Job :=
    rs_jlfp_interference arr_seq sched.

  (** The interfering workload, in turn, is defined as the sum of the
      blackout predicate, service inversion predicate, and the
      interfering workload of jobs with higher or equal priority. *)
  #[local] Instance rs_jlfp_interfering_workload : InterferingWorkload Job :=
    rs_jlfp_interfering_workload arr_seq sched.

  (** Assume that the schedule is work-conserving in the abstract sense. *)
  Hypothesis H_work_conserving : abstract.definitions.work_conserving arr_seq sched.

  (** Consider any job [j] of task [tsk] that has a positive job cost
      and is in the arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** First, we note that, since job [j] is pending at time
      [job_arrival j], there is a (potentially unbounded) busy
      interval that starts no later than with the arrival of [j]. *)
  Lemma busy_interval_prefix_exists :
    exists t1,
      t1 <= job_arrival j
      /\ busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
  Proof.
    have PEND : pending sched j (job_arrival j) by apply job_pending_at_arrival => //.
    have PREFIX := busy_interval.exists_busy_interval_prefix ltac:(eauto) j.
    feed (PREFIX (job_arrival j)); first by done.
    move: PREFIX => [t1 [PREFIX /andP [GE1 _]]].
    by eexists; split; last by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
  Qed.

  (** Let <<[t1, t2)>> be a busy-interval prefix. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** We show that the service of higher-or-equal-priority jobs is
      less than the workload of higher-or-equal-priority jobs in any
      subinterval <<[t1, t)>> of the interval <<[t1, t2)>>. *)
  Lemma service_lt_workload_in_busy :
    forall t,
      t1 < t < t2 ->
      service_of_hep_jobs arr_seq sched j t1 t
      < workload_of_hep_jobs arr_seq j t1 t.
  Proof.
    move=> t /andP [LT1 LT2]; move: (H_busy_prefix) => PREF.
    move_neq_up LE.
    have EQ: workload_of_hep_jobs arr_seq j t1 t = service_of_hep_jobs arr_seq sched j t1 t.
    { apply/eqP; rewrite eqn_leq; apply/andP; split => //.
      by apply service_of_jobs_le_workload => //.
    }
    clear LE; move: PREF => [LT [QT1 [NQT QT2]]].
    specialize (NQT t ltac:(lia)); apply: NQT => s ARR HEP BF.
    have EQ2: workload_of_hep_jobs arr_seq j 0 t = service_of_hep_jobs arr_seq sched j 0 t.
    { rewrite /workload_of_hep_jobs (workload_of_jobs_cat _ t1); last by lia.
      rewrite /service_of_hep_jobs (service_of_jobs_cat_scheduling_interval _ _ _ _ _ 0 t t1) //; last by lia.
      rewrite /workload_of_hep_jobs in EQ; rewrite EQ; clear EQ.
      apply/eqP; rewrite eqn_add2r.
      replace (service_of_jobs sched (hep_job^~ j) (arrivals_between arr_seq 0 t1) t1 t) with 0; last first.
      { symmetry; apply: big1_seq => h /andP [HEPh BWh].
        apply big1_seq => t' /andP [_ IN].
        apply not_scheduled_implies_no_service, completed_implies_not_scheduled => //.
        apply: completion_monotonic; last apply QT1 => //.
        { by rewrite mem_index_iota in IN; lia. }
        { by apply: in_arrivals_implies_arrived. }
        { by apply: in_arrivals_implies_arrived_before. }
      }
      rewrite addn0; apply/eqP.
      apply all_jobs_have_completed_impl_workload_eq_service => //.
      move => h ARRh HEPh; apply: QT1 => //.
      - by apply: in_arrivals_implies_arrived.
      - by apply: in_arrivals_implies_arrived_before.
    }
    by apply: workload_eq_service_impl_all_jobs_have_completed => //.
  Qed.

  (** Consider a subinterval <<[t1, t1 + Δ)>> of the interval
      <<[t1, t2)>>. We show that the sum of [j]'s workload and the cumulative
      workload in <<[t1, t1 + Δ)>> is strictly larger than [Δ]. *)
  Lemma workload_exceeds_interval :
    forall Δ,
      0 < Δ ->
      t1 + Δ < t2 ->
      Δ < workload_of_job arr_seq j t1 (t1 + Δ) + cumulative_interfering_workload j t1 (t1 + Δ).
  Proof.
    move=> δ POS LE; move: (H_busy_prefix) => PREF.
    apply leq_ltn_trans with (service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ)).
    { rewrite /service_during /cumulative_interference /cumul_cond_interference  /cond_interference /service_at.
      rewrite -big_split //= -{1}(sum_of_ones t1 δ) big_nat [in X in _ <= X]big_nat.
      apply leq_sum => x /andP[Lo Hi].
      { move: (H_work_conserving j t1 t2 x) => Workj.
        feed_n 4 Workj; try done.
        { by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix. }
        { by apply/andP; split; eapply leq_trans; eauto. }
        destruct interference.
        - by lia.
        - by rewrite //= addn0; apply Workj.
      }
    }
    rewrite cumulative_interfering_workload_split // cumulative_interference_split //.
    rewrite cumulative_iw_hep_eq_workload_of_ohep cumulative_i_ohep_eq_service_of_ohep //; last by apply PREF.
    rewrite -[leqRHS]addnC -[leqRHS]addnA [(_ + workload_of_job _ _ _ _)]addnC.
    rewrite workload_job_and_ahep_eq_workload_hep //.
    rewrite -addnC -addnA [(_ + service_during _ _ _ _ )]addnC.
    rewrite service_plus_ahep_eq_service_hep //; last by move: PREF => [_ [_ [_ /andP [A B]]]].
    rewrite ltn_add2l.
    by apply: service_lt_workload_in_busy; eauto; lia.
  Qed.

End BoundedBusyIntervalsAux.
