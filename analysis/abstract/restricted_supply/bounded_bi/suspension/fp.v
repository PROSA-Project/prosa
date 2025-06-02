Require Export prosa.analysis.abstract.restricted_supply.abstract_rta.
Require Export prosa.analysis.abstract.restricted_supply.iw_readiness_instantiation.
Require Export prosa.analysis.facts.model.dynamic_suspension.
Require Export prosa.analysis.definitions.sbf.busy.
Require Export prosa.analysis.facts.model.preemption.
Require Export prosa.analysis.facts.preemption.job.preemptive.
Require Export prosa.analysis.facts.preemption.task.preemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.preemptive.

Section BoundedBusyIntervals.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskTotalSuspension Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobSuspension Job}.
 
  Hypothesis H_valid_dynamic_suspensions : valid_dynamic_suspensions.

  (** Consider any kind of fully supply-consuming unit-supply
      uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  #[local] Existing Instance suspension_ready_instance.

  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider a schedule of this arrival sequence, ... *)
  Variable sched : schedule PState.

  (** ... and assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  #[local] Existing Instance fully_preemptive_job_model.
  #[local] Existing Instance fully_preemptive_task_model.
  #[local] Existing Instance fully_preemptive_rtc_threshold.

 Hypothesis H_respects_policy : respects_FP_policy_at_preemption_point arr_seq sched FP.

(** Recall that [busy_intervals_are_bounded_by] is an abstract
      notion. Hence, we need to introduce interference and interfering
      workload. We will use the restricted-supply instantiations. *)

  (** We say that job [j] incurs interference at time [t] iff it
      cannot execute due to (1) the lack of supply at time [t], (2)
      service inversion (i.e., a lower-priority job receiving service
      at [t]), or a higher-or-equal-priority job receiving service. *)
  #[local] Instance rs_readiness_jlfp_interference : Interference Job :=
    rs_readiness_jlfp_interference arr_seq sched.

  (** The interfering workload, in turn, is defined as the sum of the
      blackout predicate, service inversion predicate, and the
      interfering workload of jobs with higher or equal priority. *)
  #[local] Instance rs_readiness_jlfp_interfering_workload : InterferingWorkload Job :=
    rs_readiness_jlfp_interfering_workload arr_seq sched.

Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  Let quiet_time_ab := definitions.quiet_time sched.
  Let quiet_time_cl := classical.quiet_time arr_seq sched.

    (** ... as well as notions of busy interval prefix. *)
  Let busy_interval_prefix_ab := definitions.busy_interval_prefix sched.
  Let busy_interval_prefix_cl := classical.busy_interval_prefix arr_seq sched.

  Let busy_interval_ab := definitions.busy_interval sched.
  Let busy_interval_cl := classical.busy_interval arr_seq sched.

  (** Assume that the schedule is work-conserving in the classical sense. *)
  Hypothesis H_work_conserving_cl : work_conserving_cl.
  
  (** Consider an arbitrary task set [ts], ... *)
  Variable ts : list Task.

  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and that the cost of a job does not exceed its task's WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

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

  (** Consider a unit SBF valid in busy intervals (w.r.t. task
      [tsk]). That is, (1) [SBF 0 = 0], (2) for any duration [Δ], the
      supply produced during a busy-interval prefix of length [Δ] is
      at least [SBF Δ], and (3) [SBF] makes steps of at most one. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched tsk SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  Section ServiceInversionBound.
    
    Variable t1 t2 : instant.
    Variable j : Job.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_j_arrives : arrives_in arr_seq j.

    Lemma cumulative_service_inversion_zero :
      cumulative_service_inversion arr_seq sched j t1 t2 = 0.
    Proof.
      rewrite /cumulative_service_inversion.
      apply /eqP; rewrite sum_nat_eq0_nat.
      apply/negP => /negPn /allPn[t INt SERVINV].
      rewrite -lt0n in SERVINV.
      have A: forall (b : bool), b > 0 -> b by lia.
      move: SERVINV => /A /andP[/hasP[jo INjo HEPjo] /hasP[j' SERVj' HEPj']].
      move: INjo; rewrite mem_filter => /andP[READYjo /in_arrivals_implies_arrived ARRjo].
      move:  SERVj'; rewrite mem_filter => /andP[SERVj' /in_arrivals_implies_arrived ARRj'].
      have SCHEDj' : scheduled_at sched j' t by apply service_at_implies_scheduled_at.
      have PT : preemption_time arr_seq sched t.
      { rewrite /preemption_time /job_preemptable /fully_preemptive_job_model.
        by have ->: scheduled_job_at arr_seq sched t = Some j'
          by apply/eqP; rewrite scheduled_job_at_scheduled_at. }
      have [BACK|NOTBACK] := boolP(backlogged sched jo t).
      { move: (H_work_conserving_cl jo t ARRjo BACK) => [je SCHEDje].
        move: (H_respects_policy jo je t ARRjo PT BACK SCHEDje).
        rewrite hep_job_at_jlfp => HEP.
        have HEPje : hep_job je j by done.
        have [/eqP EQ|NEQ] := boolP(je == j'); first by subst je; rewrite HEPje in HEPj'.
        have NOTSCHEDj' : ~~ scheduled_at sched j' t
          by apply scheduled_job_at_neq with (j := je).
        by rewrite SCHEDj' in NOTSCHEDj'. }
      { move: NOTBACK; rewrite /backlogged READYjo andTb => /negPn SCHEDjo.
        have [/eqP EQ|NEQ] := boolP(jo == j'); first by subst jo; rewrite HEPjo in HEPj'.
        have NOTSCHEDj' : ~~ scheduled_at sched j' t
          by apply scheduled_job_at_neq with (j := jo).
        by rewrite SCHEDj' in NOTSCHEDj'. }
    Qed.

  End ServiceInversionBound.

  Section SuspensionReadinessInterferenceBoundAux.
    
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    Variable t1 : instant.
    Variable delta : duration.
    Hypothesis H_quiet_time : quiet_time_ab j t1.

    (** Assume that, at every instance in the interval, there exists some
        pending higher-or-equal-priority job. *)
    Hypothesis H_pending_job_exists :
      forall t,
        t1 <= t < t1 + delta ->
        (exists2 jo,
        jo \in arrivals_up_to arr_seq t
        & (pending sched jo t && hep_job jo j)).
    
    Section Step0_9.
      
      Lemma b:
        \sum_(t1 <= t < t1 + delta) no_hep_ready arr_seq sched j t
          <= \sum_(t1 <= t < t1 + delta) \sum_(j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j) suspended sched j' t. 
      Proof.
        apply: leq_trans;
          first by apply readinesss_interference_bounded_by_total_readines_bound.
        rewrite leq_sum_seq //= => t INt.
        rewrite leq_sum_seq //= => j' ARR' /andP[PENDj' _].
        rewrite /suspended PENDj' //=.
        move: PENDj' => /andP[_ ->]; by lia.
      Qed.

      Lemma c:
        \sum_(t1 <= t < t1 + delta) \sum_(j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j) suspended sched j' t
            = \sum_(t1 <= t < t1 + delta) \sum_(j' <- arrivals_between arr_seq t1 (t1 + delta) | pending sched j' t && hep_job j' j) suspended sched j' t. 
      Proof.
        apply eq_sum_seq => //= t INt _ .
        rewrite mem_index_iota in INt.
        rewrite /arrivals_up_to (@arrivals_between_cat _ _ 0 t1 ); try by lia.
        rewrite big_cat -big_filter //=.
        have ->: [seq j' <- arrivals_between arr_seq 0 t1 | pending sched j' t && hep_job j' j] = [::].
        { rewrite (@eq_in_filter _ _ pred0); first by apply filter_pred0.
          move=> j' IN' //=.
          apply /negP => /andP[/andP[ARR NOTCOMP] HEPj'].
          have Qt1: quiet_time_cl j t1
            by rewrite /quiet_time_cl instantiated_quiet_time_equivalent_quiet_time.
          have ARRj' : arrives_in arr_seq j' by apply: in_arrivals_implies_arrived.
          have ARR_beforej' : arrived_before j' t1 by apply: job_arrival_between_lt.
          move: (Qt1 j' ARRj' HEPj' ARR_beforej') => COMP.
          have COMPt : completed_by sched j' t by apply completion_monotonic with (t := t1); lia.
          by rewrite COMPt in NOTCOMP. }
        rewrite big_nil add0n.
        rewrite (@arrivals_between_cat _ _ t1 t.+1 (t1 + delta)); try by lia.
        rewrite big_cat //=.
        have ->: \sum_(j' <- arrivals_between arr_seq t.+1 (t1 + delta) | pending sched j' t && hep_job j' j) suspended sched j' t = 0.
        { apply /eqP; rewrite sum_nat_seq_eq0.
          apply /allP => [j' INj']; apply /implyP => /andP[/andP[ARRj' NOTCOMP] HEPj'].
          exfalso; rewrite /has_arrived in ARRj'.
          have ARRTj' : t.+1 <= job_arrival j' by apply: job_arrival_between_ge.
          by lia. }
        by rewrite addn0.
      Qed.

      Lemma d:
        \sum_(t1 <= t < t1 + delta) \sum_(j' <- arrivals_between arr_seq t1 (t1 + delta) | pending sched j' t && hep_job j' j) suspended sched j' t
            = \sum_(t1 <= t < t1 + delta) \sum_(j' <- arrivals_between arr_seq t1 (t1 + delta) | hep_job j' j) suspended sched j' t.
      Proof.
        apply eq_sum_seq => t INt _.
        apply /eqP; rewrite [in RHS](bigID (fun j' => pending sched j' t)) //=.
        under eq_bigl do rewrite andbC.
        have ->: \sum_(i <- arrivals_between arr_seq t1 (t1 + delta) | hep_job i j && ~~ pending sched i t) suspended sched i t = 0.
        { apply /eqP; rewrite sum_nat_seq_eq0.
          rewrite /suspended; apply /allP => [j' INj'].
          by apply /implyP => /andP[_ /negPf ->]; rewrite andbF. }
        by rewrite addn0.
      Qed. 

      Lemma e:
        \sum_(t1 <= t < (t1 + delta)) \sum_(jo <- arrivals_between arr_seq t1 (t1 + delta) | hep_job jo j) suspended sched jo t
            <= \sum_(tsko <- ts | hep_task tsko tsk) \sum_(t1 <= t < (t1 + delta)) \sum_(jo <- task_arrivals_between arr_seq tsko t1 (t1 + delta)) suspended sched jo t.
      Proof.
        rewrite [in leqRHS]exchange_big_idem //=.
        rewrite leq_sum_seq //= => t INt _.
        rewrite /task_arrivals_between.
        apply leq_trans with 
          (n := \sum_(tsko <- ts | hep_task tsko tsk) \sum_(jo <- arrivals_between arr_seq t1 (t1 + delta) | hep_job jo j && job_of_task tsko jo) suspended sched jo t).
          { rewrite /job_of_task -[in leqRHS]big_filter.
            apply: sum_over_partitions_le => j' INj'.
            rewrite /hep_job /FP_to_JLFP => HEPtsko.
            rewrite mem_filter; apply /andP; split; 
              first by move: H_job_of_tsk; rewrite /job_of_task => /eqP <-.
            by apply /H_all_jobs_from_taskset /in_arrivals_implies_arrived. }
        rewrite leq_sum_seq //= => tsko tskoIN HEPtsko.
        rewrite big_filter eq_leq //=.
        apply eq_bigl; rewrite /eqfun => jo.
        rewrite /hep_job /FP_to_JLFP.
        apply andb_idl; rewrite /job_of_task => /eqP ->.
        by move: H_job_of_tsk; rewrite /job_of_task => /eqP ->.
      Qed.
  
    End Step0_9.

  End SuspensionReadinessInterferenceBoundAux.

  Section SuspensionReadinessInterferenceBound.

    Let suspension_readiness_bound (A delta : duration):=
      \sum_(tsko <- ts | hep_task tsko tsk) (max_arrivals tsko delta * task_total_suspension tsko).
 
    Lemma suspension_readiness_interference_bounded :
      readiness_interference_is_bounded arr_seq sched tsk suspension_readiness_bound.
    Proof.
      move=> j t1 t2 delta LT ARRj TSKj PCostj PREF.
      apply: leq_trans. 
      { apply b => //=; first by move: PREF => [? [? ?]].
        move=> t INt.
        have [jhp [ARRs [PEND HEPjhp]]]: exists jhp, arrives_in arr_seq jhp /\ pending sched jhp t /\ hep_job jhp j.
        { have INt' : t1 <= t < t2 by lia.
          apply: pending_hep_job_exists_inside_busy_interval => //=. }
        exists jhp; last by apply /andP; split.
        have ARR_LT : job_arrival jhp <= t by move: PEND => /andP[? ?].
        by apply job_in_arrivals_between. }
      rewrite c => //=; try by move: PREF => [? [? ?]].
      rewrite d.
      apply: leq_trans; first by apply e.
      rewrite leq_sum_seq //= => ? ? ?.
      by apply suspension_of_task_bounded.
    Qed.

  End SuspensionReadinessInterferenceBound.
      
  Section Duplicates.
  
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    Lemma busy_interval_prefix_exists :
      exists t1,
        t1 <= job_arrival j
        /\ busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
    Proof.
      have PEND : pending sched j (job_arrival j) by apply job_pending_at_arrival => //.
      have PREFIX := busy_interval.exists_busy_interval_prefix ltac:(eauto) j.
      feed (PREFIX (job_arrival j)); first by done.
      move: PREFIX => [t1 [PREFIX /andP [GE1 _]]].
      by eexists; split; last by rewrite instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
    Qed.
 
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

    (** Consider a subinterval <<[t1, t1 + Δ)>> of the interval <<[t1,
        t2)>>. We show that the sum of [j]'s workload and the cumulative
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
        { have work_conservation_ab : definitions.work_conserving arr_seq sched by apply
            instantiated_i_and_w_are_coherent_with_schedule.
          move: (work_conservation_ab j t1 t2 x) => Workj.
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
      rewrite [leqRHS]addnA [leqRHS]addnCAC -[leqRHS]addnA.
      rewrite -[X in _ <= _ + X]addnA -[X in _ <= _ + X]addnA. 
      rewrite [X in _ <= _ + (_ + X)]addnA.
      rewrite [X in _ <= _ + (_ + X)]addnACl.
      rewrite workload_job_and_ahep_eq_workload_hep //.
      rewrite addnA addnCAC -addnA.
      rewrite -[X in _ + X]addnA -[X in _ + X]addnA. 
      rewrite [X in _ + (_ + X)]addnA.
      rewrite [X in _ + (_ + X)]addnACl.
      rewrite service_plus_ahep_eq_service_hep //; last by move: PREF => [_ [_ [_ /andP [A B]]]].
      rewrite ltn_add2l ltn_add2l ltn_add2l.
      by apply: service_lt_workload_in_busy; eauto; lia.
    Qed.

 
  End Duplicates.

  Variable service_inversion_bound : duration.
  Hypothesis H_service_inversion_is_bounded :
    service_inversion_is_bounded arr_seq sched tsk service_inversion_bound.


  (** Let [L] be any positive fixed point of the busy-interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.
  Hypothesis H_fixed_point :
    \sum_(tsko <- ts | hep_task tsko tsk) (max_arrivals tsko L * task_total_suspension tsko)  
        + total_hep_request_bound_function_FP ts tsk L + service_inversion_bound
      <= SBF L.

  (** Next, we provide a step-by-step proof of busy-interval boundedness. *)
  Section StepByStepProof.

    (** Consider any job [j] of task [tsk] that has a positive job
        cost and is in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Consider two cases: (1) when the busy-interval prefix
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
      Hypothesis H_busy_prefix_arr : busy_interval_prefix_cl j t1 (job_arrival j).+1.
      Hypothesis H_busy_prefix_L : busy_interval_prefix_cl j t1 (t1 + L).

      (** The crucial point to note is that the sum of the job's cost
          (represented as [workload_of_job]) and the interfering
          workload in the interval <<[t1, t1 + L)>> is bounded by [L]
          due to the fixed point [H_fixed_point]. *)
      Local Lemma workload_is_bounded :
        workload_of_job arr_seq j t1 (t1 + L) + cumulative_interfering_workload j t1 (t1 + L) <= L.
      Proof.
        rewrite (cumulative_interfering_workload_split _ _ _).
        rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ (t1 + L) _ _ _)); (try apply H_valid_SBF) => //.
        rewrite addnC -!addnA.
        have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
        apply: E; first by lia.
        rewrite addnC -addnA subKn; last by apply: sbf_bounded_by_duration => //.
        rewrite cumulative_iw_hep_eq_workload_of_ohep. 
        rewrite -[X in _ + X]addnA.
        rewrite workload_job_and_ahep_eq_workload_hep => //=.
        rewrite addnC -addnA.
        rewrite -(leqRW H_fixed_point).
        rewrite -[X in _ <= X]addnA.
        apply leq_add; last first.
        { apply leq_add; first by apply hep_workload_le_total_hep_rbf.
          apply H_service_inversion_is_bounded => //=.
          by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix. }
        { apply: leq_trans.
          { apply: leq_sum => t _.
            instantiate (1 := no_hep_ready arr_seq sched j) => //=; by lia. } 
          rewrite //=.
          have BUSY_ab : busy_interval_prefix_ab j t1 (t1 + L)
            by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
          apply suspension_readiness_interference_bounded with (t2 := t1 + L) => //=. }
      Qed.

      (** It follows that [t1 + L] is a quiet time, which means that
          the busy prefix ends (i.e., it is bounded). *)
      Local Lemma busy_prefix_is_bounded_case1 :
        exists t2,
          job_arrival j < t2
          /\ t2 <= t1 + L
          /\ busy_interval_cl j t1 t2.
      Proof.
        have PEND : pending sched j (job_arrival j) by apply job_pending_at_arrival => //.
        enough(exists t2, job_arrival j < t2 /\ t2 <= t1 + L /\ definitions.busy_interval sched j t1 t2) as BUSY.
        { have [t2 [LE1 [LE2 BUSY2]]] := BUSY.
          eexists; split; first by exact: LE1.
          split; first by done.
          rewrite /busy_interval_cl.
          by rewrite instantiated_busy_interval_equivalent_busy_interval.
        }
        eapply busy_interval.busy_interval_is_bounded; eauto 2 => //.
        - by eapply instantiated_i_and_w_no_speculative_execution; eauto 2 => //.
        - by apply instantiated_i_and_w_are_coherent_with_schedule.
        - by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
        - by apply workload_is_bounded => //.
      Qed.

    End Case1.

    (** Next, we consider the case when the interval <<[t1, t1 + L)>>
        is not a busy-interval prefix. *)
    Section Case2.

      (** Consider a time instant [t1] such that <<[t1, job_arrival
          j]>> is a busy-interval prefix of [j] and <<[t1, t1 + L)>>
          is _not_. *)
      Variable t1 : instant.
      Hypothesis H_arrives : t1 <= job_arrival j.
      Hypothesis H_busy_prefix_arr : busy_interval_prefix_cl j t1 (job_arrival j).+1.
      Hypothesis H_no_busy_prefix_L : ~ busy_interval_prefix_cl j t1 (t1 + L).

      (** From the properties of busy intervals, one can conclude that
          [j]'s arrival time is less than [t1 + L]. *)
      Local Lemma job_arrival_is_bounded :
        job_arrival j < t1 + L.
      Proof.
        move_neq_up FF.
        move: (H_busy_prefix_arr) (H_busy_prefix_arr) => PREFIX PREFIXA.
        rewrite /busy_interval_prefix_cl instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in PREFIXA => //.
        move: (PREFIXA) => GTC.
        eapply workload_exceeds_interval with (Δ := L) in PREFIX => //.
        { move_neq_down PREFIX.
          rewrite (cumulative_interfering_workload_split _ _ _).
          rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ (job_arrival j).+1 _ _ _)); (try apply H_valid_SBF) => //.
          rewrite addnC -!addnA.
          have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
          apply: E; first by lia.
          rewrite subKn; last by apply: sbf_bounded_by_duration => //.
          rewrite -(leqRW H_fixed_point).
          rewrite addnC -addnA addnC. 
          apply leq_add; last first.
          { rewrite (leqRW (service_inversion_widen _ _ _ t1 _ _ (job_arrival j).+1 _ _ ));
              first by apply H_service_inversion_is_bounded.
            - lia.
            - lia.
          }
          rewrite -addnA.
          apply leq_add. 
          { apply leq_trans with (cumulative_readiness_interference arr_seq sched j t1 (t1 + L));
              first by apply leq_sum_seq => ? ? ?; lia.
            apply suspension_readiness_interference_bounded with (t2 := (job_arrival j).+1) => //=. }
          { rewrite cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
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
      Local Lemma busy_prefix_is_bounded_case2:
        exists t2, job_arrival j < t2 /\ t2 <= t1 + L /\ busy_interval arr_seq sched j t1 t2.
      Proof.
        have LE: job_arrival j < t1 + L
          by apply job_arrival_is_bounded => //; try apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
        move: (H_busy_prefix_arr) => PREFIX.
        move: (H_no_busy_prefix_L) => NOPREF.
        rewrite /busy_interval_prefix_cl instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in PREFIX => //.
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
        { rewrite instantiated_busy_interval_equivalent_busy_interval => //. }
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
    have [t1 [GE PREFIX]]:
      exists t1, t1 <= job_arrival j
            /\ busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1
        by apply: busy_interval_prefix_exists.
    exists t1.
    enough(exists t2, job_arrival j < t2 /\ t2 <= t1 + L /\ busy_interval arr_seq sched j t1 t2) as BUSY.
    { move: BUSY => [t2 [LT [LE BUSY]]]; eexists; split; last first.
      { split; first by exact: LE.
        by apply instantiated_busy_interval_equivalent_busy_interval. }
      { by apply/andP; split. }
    }
    { have [LPREF|NOPREF] := busy_interval_prefix_case ltac:(eauto) j t1 (t1 + L).
      { apply busy_prefix_is_bounded_case1 => //.
        rewrite /busy_interval_prefix_cl instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //. }
      { apply busy_prefix_is_bounded_case2=> //.
        move=> NP; apply: NOPREF.
        by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
      }
    }
  Qed.

End BoundedBusyIntervals.
