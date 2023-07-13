 Require Export prosa.analysis.facts.blocking_bound_fp.
Require Export prosa.analysis.abstract.restricted_supply.abstract_rta.
Require Export prosa.analysis.abstract.restricted_supply.iw_instantiation.
Require Export prosa.analysis.definitions.sbf.busy.


(** * Sufficient Condition for Bounded Busy Intervals for RS FP *)

(** In this section, we show that the existence of [L] such that [B +
    total_hep_rbf L <= SBF L], where [B] is the blocking bound and
    [SBF] is a supply-bound function, is a sufficient condition for
    the existence of bounded busy intervals under FP scheduling with a
    restricted-supply processor model. *)
Section BoundedBusyIntervals.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

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

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation, and assume that the relation is reflexive and
      transitive. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

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

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Furthermore, we assume that the schedule is work-conserving ... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and that it respects the scheduling policy. *)
  Hypothesis H_respects_policy : respects_FP_policy_at_preemption_point arr_seq sched FP.

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

  (** Consider an arbitrary task set [ts], ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and that the cost of a job does not exceed its task's WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider a valid, unit supply-bound function "busy" [SBF]. That
      is, (1) [SBF 0 = 0], (2) for any duration [Δ], the supply
      produced during a busy-interval prefix of length [Δ] is at least
      [SBF Δ], and (3) [SBF] makes steps of at most one. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts], [max_arrival tsk] is (1) an arrival
      bound of [tsk], and (2) it is a monotonic function that equals
      [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Let [L] be any positive fixed point of the busy-interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.
  Hypothesis H_fixed_point :
    blocking_bound ts tsk + total_hep_request_bound_function_FP ts tsk L <= SBF L.

  (** Next, we provide a step-by-step proof of busy-interval boundedness. *)
  Section StepByStepProof.

    (** Consider any job [j] of task [tsk] that has a positive job
        cost and is in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** First, we note that since job [j] is pending at time
        [job_arrival j], there is a (potentially unbounded) busy
        interval that starts no later than with the arrival of [j]. *)
    Local Lemma busy_interval_prefix_exists :
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

    (** Next, consider two cases: (1) when the busy-interval prefix
        continues until time instant [t1 + L] and (2) when the busy
        interval prefix terminates earlier. In either case, we can
        show that the busy-interval prefix is bounded. *)

    (** We start with the first case, where the busy-interval prefix
        continues until time instant [t1 + L]. *)
    Section Case1.

      (** Consider a time instant [t1] such that <<[t1, job_arrival
          j]>> and <<[t1, t1 + L)>> are both busy-interval prefixes of
          job [j].

          Note that at this point we do not necessarily know that
          [job_arrival j <= L]; hence, we assume the existence of both
          prefixes. *)
      Variable t1 : instant.
      Hypothesis H_busy_prefix_arr : busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
      Hypothesis H_busy_prefix_L : busy_interval_prefix arr_seq sched j t1 (t1 + L).

      (** The crucial point to note is that the sum of the job's cost
          (represented as [workload_of_job]) and the interfering
          workload in the interval <<[t1, t1 + L)>> is bounded by [L]
          due to the fixed point [H_fixed_point]. *)
      Local Lemma workload_is_bounded :
        workload_of_job arr_seq j t1 (t1 + L) + cumulative_interfering_workload j t1 (t1 + L) <= L.
      Proof.
        rewrite (cumulative_interfering_workload_split _ _ _).
        (rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ _ _ _ _)); try apply H_busy_prefix) => //.
        rewrite // addnC -!addnA.
        have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
        apply: E; first by lia.
        rewrite subKn; last by apply: sbf_bounded_by_duration => //.
        rewrite -(leqRW H_fixed_point); apply leq_add.
        - apply: leq_trans; first apply: service_inversion_is_bounded => //.
          + instantiate (1 := fun _ => blocking_bound ts tsk) => //=.
            by move=> jo t t' ARRo TSKo PREFo; apply: priority_inversion_is_bounded_by_blocking => //.
          + by done.
        - rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
          by apply hep_workload_le_total_hep_rbf.
      Qed.

      (** It follows that [t1 + L] is a quiet time, which means that
          the busy prefix ends (i.e., it is bounded). *)
      Local Lemma busy_prefix_is_bounded_case1 :
        exists t2,
          job_arrival j < t2
          /\ t2 <= t1 + L
          /\ busy_interval arr_seq sched j t1 t2.
      Proof.
        have PEND : pending sched j (job_arrival j) by apply job_pending_at_arrival => //.
        enough(exists t2, job_arrival j < t2 /\ t2 <= t1 + L /\ definitions.busy_interval sched j t1 t2) as BUSY.
        { have [t2 [LE1 [LE2 BUSY2]]] := BUSY.
          eexists; split; first by exact: LE1.
          split; first by done.
          by apply instantiated_busy_interval_equivalent_busy_interval.
        }
        eapply busy_interval.busy_interval_is_bounded; eauto 2 => //.
        - by apply unit_supply_is_unit_service.
        - by eapply instantiated_i_and_w_no_speculative_execution; eauto 2 => //.
        - by eapply instantiated_i_and_w_are_coherent_with_schedule; eauto 2 => //.
        - by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
        - by apply workload_is_bounded => //.
      Qed.

    End Case1.

    (** Next, we consider the case when the interval <<[t1, t1 + L)>>
        is not a busy-interval prefix. *)
    Section Case2.

      (** First, we prove a few helper lemmas. *)
      Section HelperLemmas.

        (** Let <[t1, t2)>> be a busy-interval prefix. *)
        Variable t1 t2 : instant.
        Hypothesis H_busy_prefix : busy_interval_prefix arr_seq sched j t1 t2.

        (** Then, the service of higher-or-equal-priority jobs is less
            than the workload of higher-or-equal-priority jobs in any
            subinterval <<[t1, t)>> of the interval <<[t1, t2)>>. *)
        Local Lemma service_lt_workload_in_busy :
          forall t,
            t1 < t < t2 ->
            service_of_hep_jobs arr_seq sched j t1 t < workload_of_hep_jobs arr_seq j t1 t.
        Proof.
          move=> t /andP [LT1 LT2]; move: (H_busy_prefix) => PREF.
          move_neq_up LE.
          have EQ: workload_of_hep_jobs arr_seq j t1 t = service_of_hep_jobs arr_seq sched j t1 t.
          { apply/eqP; rewrite eqn_leq; apply/andP; split => //.
            apply service_of_jobs_le_workload => //.
            by apply unit_supply_is_unit_service.
          }
          clear LE; move: PREF => [LT [QT1 [NQT QT2]]].
          specialize (NQT t ltac:(lia)); apply: NQT => s ARR HEP BF.
          have EQ2: workload_of_hep_jobs arr_seq j 0 t = service_of_hep_jobs arr_seq sched j 0 t. (* TODO: new lemma *)
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
            apply all_jobs_have_completed_impl_workload_eq_service => //; first by apply unit_supply_is_unit_service.
            move => h ARRh HEPh; apply: QT1 => //.
            - by apply: in_arrivals_implies_arrived.
            - by apply: in_arrivals_implies_arrived_before.
          }
          apply: workload_eq_service_impl_all_jobs_have_completed => //.
          by apply unit_supply_is_unit_service.
        Qed.

        (** Consider a subinterval <<[t1, t1 + Δ)>> of the interval
            <<[t1, t2)>>.  We show that the sum of [j]'s workload and
            the cumulative workload in <<[t1, t1 + Δ)>> is strictly
            larger than [Δ]. *)
        Local Lemma workload_exceeds_interval :
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
            { eapply instantiated_i_and_w_are_coherent_with_schedule in H_work_conserving; eauto 2 => //.
              move: (H_work_conserving j t1 t2 x) => Workj.
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
          rewrite -[leqRHS]addnC -[leqRHS]addnA [(_ + workload_of_job _ _ _ _ )]addnC.
          rewrite workload_job_and_ahep_eq_workload_hep //.
          rewrite -addnC -addnA [(_ + service_during _ _ _ _ )]addnC.
          rewrite service_plus_ahep_eq_service_hep //; last by move: PREF => [_ [_ [_ /andP [A B]]]].
          rewrite ltn_add2l.
          by apply: service_lt_workload_in_busy; eauto; lia.
        Qed.

      End HelperLemmas.

      (** Consider a time instant [t1] such that <<[t1, job_arrival
          j]>> is a busy-interval prefix of [j] and <<[t1, t1 + L)>>
          is _not_. *)
      Variable t1 : instant.
      Hypothesis H_arrives : t1 <= job_arrival j.
      Hypothesis H_busy_prefix_arr : busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
      Hypothesis H_no_busy_prefix_L : ~ busy_interval_prefix arr_seq sched j t1 (t1 + L).

      (** From the properties of busy intervals, one can conclude that
          [j]'s arrival time is less than [t1 + L]. *)
      Lemma job_arrival_is_bounded :
        job_arrival j < t1 + L.
      Proof.
        move_neq_up FF.
        move: (H_busy_prefix_arr) (H_busy_prefix_arr) => PREFIX PREFIXA.
        apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in PREFIXA => //.
        move: (PREFIXA) => GTC.
        eapply workload_exceeds_interval with (Δ := L) in PREFIX => //.
        { move_neq_down PREFIX.
          rewrite (cumulative_interfering_workload_split _ _ _).
          (rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ _ _ _ _)); try apply GTC) => //; first last.
          { move=> *; split; first by apply H_valid_SBF.
            move => *; destruct H_valid_SBF as [A B].
            apply: B => //.
            by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
          }
          rewrite addnC -!addnA.
          have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
          apply: E; first by lia.
          rewrite subKn; last by apply: sbf_bounded_by_duration => //.
          rewrite -(leqRW H_fixed_point); apply leq_add.
          { rewrite (leqRW (service_inversion_widen _ _ _ t1 _ _ (job_arrival j).+1 _ _ )).
            - apply: leq_trans.
              + apply: service_inversion_is_bounded => //.
                move => *; instantiate (1 := fun _ => blocking_bound ts tsk) => //.
                by apply: priority_inversion_is_bounded_by_blocking => //.
              + by done.
            - by done.
            - lia.
          }
          { rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
            by apply hep_workload_le_total_hep_rbf. }
        }
      Qed.

      (** Lemma [job_arrival_is_bounded] implies that the
          busy-interval prefix starts at time [t1], continues until
          [job_arrival j + 1], and then terminates before [t1 + L].
          Or, in other words, there is point in time [t2] such that
          (1) [j]'s arrival is bounded by [t2], (2) [t2] is bounded by
          [t1 + L], and (3) <<[t1, t2)>> is busy interval of job
          [j]. *)
      Lemma busy_prefix_is_bounded_case2:
        exists t2, job_arrival j < t2 /\ t2 <= t1 + L /\ busy_interval arr_seq sched j t1 t2.
      Proof.
        have LE: job_arrival j < t1 + L
          by apply job_arrival_is_bounded => //; try apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
        move: (H_busy_prefix_arr) => PREFIX.
        move: (H_no_busy_prefix_L) => NOPREF.
        apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in PREFIX => //.
        have BUSY := terminating_busy_prefix_is_busy_interval _ _ _ _ _ _ _ PREFIX.
        edestruct BUSY as [t2 BUS]; clear BUSY; try apply TSK; eauto 2 => //.
        { move => T; apply: NOPREF.
          by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in T => //.
        }
        exists t2; split; last split.
        { move: BUS => [[A _] _]; lia. }
        { move_neq_up FA.
          apply: NOPREF; split; [lia | split; first by apply H_busy_prefix_arr].
          split.
          - move=> t NEQ.
            apply abstract_busy_interval_classic_busy_interval_prefix in BUS => //.
            by apply BUS; lia.
          - lia.
        }
        { by apply instantiated_busy_interval_equivalent_busy_interval => //. }
      Qed.

    End Case2.

  End StepByStepProof.

  (** Combining the cases analyzed above, we conclude that busy
      intervals of jobs released by task [tsk] are bounded by [L].  *)
  Lemma busy_intervals_are_bounded_rs_fp :
    busy_intervals_are_bounded_by arr_seq sched tsk L.
  Proof.
    move => j ARR TSK POS.
    have PEND : pending sched j (job_arrival j) by apply job_pending_at_arrival => //.
    have [t1 [GE PREFIX]] := busy_interval_prefix_exists _ ARR POS.
    exists t1.
    enough(exists t2, job_arrival j < t2 /\ t2 <= t1 + L /\ busy_interval arr_seq sched j t1 t2) as BUSY.
    { move: BUSY => [t2 [LT [LE BUSY]]]; eexists; split; last first.
      { split; first by exact: LE.
        by apply instantiated_busy_interval_equivalent_busy_interval. }
      { by apply/andP; split. }
    }
    { have [LPREF|NOPREF] := busy_interval_prefix_case ltac:(eauto) j t1 (t1 + L).
      { apply busy_prefix_is_bounded_case1 => //.
        by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //. }
      { apply busy_prefix_is_bounded_case2=> //.
        move=> NP; apply: NOPREF.
        by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
      }
    }
  Qed.

End BoundedBusyIntervals.
