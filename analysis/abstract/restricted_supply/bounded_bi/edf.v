Require Export prosa.model.priority.edf.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.definitions.busy_interval.edf_pi_bound.
Require Export prosa.analysis.abstract.restricted_supply.abstract_rta.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.aux.
Require Export prosa.analysis.definitions.sbf.busy.

(** * Sufficient Condition for Bounded Busy Intervals for RS EDF *)

(** In this section, we show that the existence of [L] such that
    [total_rbf L <= SBF L /\ longest_busy_interval_with_pi <= SBF L],
    where [longest_busy_interval_with_pi] is the length of the longest
    busy interval starting with a priority inversion (w.r.t. a job of
    a task under analysis) and [SBF] is a supply-bound function, is a
    sufficient condition for the existence of bounded busy intervals
    under EDF scheduling with a restricted-supply processor model.

    The proof uses the following observation. Consider the beginning
    of a busy interval of a job [j] to be analyzed. If there is
    service inversion, one can derive an upper bound on the relative
    arrival of job [j], which in turn can be used to derive a bound on
    the total higher-or-equal priority workload
    ([longest_busy_interval_with_pi]). If there is no service
    inversion, we use the standard fixpoint approach with [total_rbf L]. *)
Section BoundedBusyIntervals.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** For brevity, let's denote the relative deadline of a task as [D]. *)
  Let D tsk := task_deadline tsk.

  (** Consider any kind of fully supply-consuming unit-supply
      uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

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

  (** Assume that jobs have bounded non-preemptive segments. *)
  Context `{JobPreemptable Job}.
  Context `{TaskMaxNonpreemptiveSegment Task}.
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Furthermore, we assume that the schedule is work-conserving ... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and that it respects the scheduling policy. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).

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
  Variable ts : seq Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and that the cost of a job does not exceed its task's WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Let [max_arrivals] be a family of valid arrival curves. *)
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

  (** First, we show that the constant [longest_busy_interval_with_pi
      ts tsk] indeed bounds the cumulative interference incurred by
      job [j]. *)
  Section LongestBusyIntervalWithPIIsValid.

    (** Consider any job [j] of task [tsk] that has a positive job
        cost and is in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Let <<[t1, t2)>> be a busy-interval prefix. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_prefix : busy_interval_prefix arr_seq sched j t1 t2.

    (** Consider an interval <<[t1, t1 + δ) ⊆ [t1, t2)>>. *)
    Variable δ : duration.
    Hypothesis H_interval_in_busy_prefix : t1 + δ <= t2.

    (** Assume that cumulative service inversion of job [j] in this
        interval is positive. *)
    Hypothesis H_positive_service_inversion :
      cumulative_service_inversion arr_seq sched j t1 (t1 + δ) > 0.

    (** The LHS of the following inequality represents all possible
        interference as well as the cost of the job itself in a prefix
        of length [δ]. On the RHS of the inequality, there is a
        constant [longest_busy_interval_with_pi]. We prove that this
        inequality is indeed true. This implies that if the cumulative
        service inversion of job [j] is positive, its busy interval
        cannot possibly be longer than
        [longest_busy_interval_with_pi]. *)
    Lemma longest_bi_with_pi_bound_is_valid :
      cumulative_service_inversion arr_seq sched j t1 (t1 + δ)
      + (cumulative_other_hep_jobs_interfering_workload arr_seq j t1 (t1 + δ)
         + workload_of_job arr_seq j t1 (t1 + δ))
      <= longest_busy_interval_with_pi ts tsk.
    Proof.
      move: (H_positive_service_inversion) => PP.
      eapply cumulative_service_inversion_from_one_job in H_positive_service_inversion => //.
      move: H_positive_service_inversion => [jlp [ARR [LP EQs]]].
      move: (H_job_of_tsk) => /eqP TSK; unfold longest_busy_interval_with_pi, D in *; subst tsk.
      move: (H_busy_prefix) => [_ [_ [_ /andP [ARRj _]]]].
      have [t_sched [_ SCHEDjlp]]: exists t, t1 <= t < t1 + δ /\ scheduled_at sched jlp t
          by apply cumulative_service_implies_scheduled; rewrite -EQs.
      apply leq_bigmax_sup; exists (job_task jlp); split; last split.
      { by apply H_all_jobs_from_taskset. }
      {  move_neq_up LP'; move: LP => /negP LP; apply: LP.
         by rewrite /hep_job /EDF /job_deadline /job_deadline_from_task_deadline; lia. }
      apply leq_add.
      - rewrite EQs (leqRW (lp_job_bounded_service _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) => //.
        by rewrite leq_sub2r //; apply H_valid_model_with_bounded_nonpreemptive_segments.
      - rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
        apply leq_trans with (workload_of_jobs (hep_job^~ jlp) (arrivals_between arr_seq t1 (t1 + δ))).
        { apply workload_of_jobs_weaken => jo; move: LP; clear.
          by rewrite /hep_job /EDF /job_deadline /job_deadline_from_task_deadline; lia. }
        erewrite workload_of_jobs_partitioned_by_tasks with (ts := undup ts).
        + eapply leq_trans; first by apply sum_le_subseq, undup_subseq. 
          apply leq_sum_seq => tsk_o INo HEP; rewrite -(leqRW (workload_le_rbf' _ _ _ _ _ _ _)) //.
          have [A | B] := (leqP δ (task_deadline (job_task jlp) - task_deadline tsk_o)).
          { by apply workload_of_jobs_reduce_range; lia. }
          { have EQt: forall a b, a = b -> a <= b; [by lia | apply: EQt].
            apply workload_of_jobs_nil_tail => //; [lia | move => jo IN LE].
            have [EQ|NEQ] := (@eqP _ (job_task jo) (tsk_o)); last by rewrite andbF.
            rewrite andbT /hep_job /EDF /job_deadline /job_deadline_from_task_deadline -ltnNge.
            by subst tsk_o; rewrite /hep_job /EDF /job_deadline /job_deadline_from_task_deadline in LP; lia.
          }
        + by move=> jo IN; rewrite in_seq_equiv_undup;
            apply: H_all_jobs_from_taskset; apply: in_arrivals_implies_arrived.
        + move=> jo IN.
          have ARRjo : t1 <= job_arrival jo by apply: job_arrival_between_ge.
          rewrite /hep_job /D /EDF => T; move_neq_up LEQ; move_neq_down T.
          by rewrite /job_deadline /job_deadline_from_task_deadline; lia.
        + by apply arrivals_uniq.
        + by apply undup_uniq.
    Qed.

  End LongestBusyIntervalWithPIIsValid.

  (** We introduce the main assumption of this section. Let [L]
      be any positive constant that satisfies two properties. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.

  (** First, we assume that [SBF L] bounds
      [longest_busy_interval_with_pi ts tsk]. As discussed, when a
      busy interval starts with service inversion, one can upper-bound
      the total interfering workload that a job under analysis incurs
      via [longest_busy_interval_with_pi ts tsk]. The time to consume
      this workload is [SBF L]. *)
  Hypothesis H_L_bounds_bi_with_pi : longest_busy_interval_with_pi ts tsk <= SBF L.

  (** And second, we assume that [total_RBF L <= SBF L]. When there is
      no service inversion at the beginning of a busy interval, one
      can show that there is no carry-in workload (including the
      lower-priority workload). This allows us to bound interfering
      workload within a busy interval with [total_RBF L] without
      adding an extra [+ blocking_bound] as in the case of the general
      JLFP bound. *)
  Hypothesis H_fixed_point : total_request_bound_function ts L <= SBF L.


  (** In the following, we prove busy-interval boundedness via a case
      analysis on two cases: (1) when the busy-interval prefix is at
      least [L] time units long and (2) when the busy interval prefix
      terminates earlier. In either case, we can show that the
      busy-interval prefix is bounded. *)
  Section StepByStepProof.

    (** Consider any job [j] of task [tsk] that has a positive job
        cost and is in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** As a preparation step, we show that [L] bounds the relative
        arrival time of job [j]. *)
    Section RelativeArrivalIsBounded.

      (** Consider a time instant [t1] such that <<[t1, job_arrival
          j]>> is a busy-interval prefix of [j]. *)
      Variable t1 : instant.
      Hypothesis H_arrives : t1 <= job_arrival j.
      Hypothesis H_busy_prefix_arr : busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.

      (** From the properties of the workload (defined by hypotheses
          [H_L_bounds_bi_with_pi] and [H_fixed_point]), we show that
          [j]'s arrival time is necessarily less than [t1 + L]. *)
      Local Lemma job_arrival_is_bounded :
        job_arrival j < t1 + L.
      Proof.
        move_neq_up FF.
        move: (H_busy_prefix_arr) (H_busy_prefix_arr) => PREFIX PREFIXA.
        apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in PREFIXA => //.
        move: (PREFIXA) => GTC.
        eapply workload_exceeds_interval with (Δ := L) in PREFIX => //; last first.
        move_neq_down PREFIX.
        rewrite (cumulative_interfering_workload_split _ _ _).
        rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ (job_arrival j).+1 _ _ _)); (try apply H_valid_SBF) => //.
        rewrite addnC -!addnA.
        have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
        apply: E; first by lia.
        rewrite subKn; last by apply: sbf_bounded_by_duration => //.
        have [ZERO|POS] := (posnP (cumulative_service_inversion arr_seq sched j t1 (t1 + L))).
        { rewrite ZERO add0n -(leqRW H_fixed_point).
          rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
          have DD := hep_workload_le_total_rbf.
          by apply hep_workload_le_total_rbf. }
        { by rewrite -(leqRW H_L_bounds_bi_with_pi); apply: longest_bi_with_pi_bound_is_valid. }
      Qed.

    End RelativeArrivalIsBounded.

    (** We start with the first case, where the busy-interval prefix
        continues until time instant [t1 + L]. *)
    Section Case1.

      (** Consider a time instant [t1] such that <<[t1, job_arrival
          j]>> and <<[t1, t1 + L)>> are both busy-interval prefixes of
          job [j]. *)
      Variable t1 : instant.
      Hypothesis H_busy_prefix_arr : busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
      Hypothesis H_busy_prefix_L : busy_interval_prefix arr_seq sched j t1 (t1 + L).

      (** The crucial point to note is that the sum of the job's cost
          (represented as [workload_of_job]) and the interfering
          workload in the interval <<[t1, t1 + L)>> is bounded by [L]
          due to hypotheses [H_L_bounds_bi_with_pi] and
          [H_fixed_point]. *)
      Local Lemma workload_is_bounded :
        workload_of_job arr_seq j t1 (t1 + L) + cumulative_interfering_workload j t1 (t1 + L) <= L.
      Proof.
        rewrite (cumulative_interfering_workload_split _ _ _).
        rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ (t1 + L) _ _ _)); (try apply H_valid_SBF) => //.
        rewrite // addnC -!addnA.
        have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
        apply: E; first by lia.
        rewrite subKn; last by apply: sbf_bounded_by_duration => //.
        have [ZERO|POS] := (posnP (cumulative_service_inversion arr_seq sched j t1 (t1 + L))).
        { rewrite ZERO add0n -(leqRW H_fixed_point).
          rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
          by apply hep_workload_le_total_rbf => //; move: (H_busy_prefix_arr) => [LE _]; rewrite -ltnS. }
        { by rewrite -(leqRW H_L_bounds_bi_with_pi); apply: longest_bi_with_pi_bound_is_valid => //;
            move: (H_busy_prefix_arr) => [LE _]; rewrite -ltnS. }
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
        - by eapply instantiated_i_and_w_no_speculative_execution; eauto 2 => //.
        - by eapply instantiated_i_and_w_are_coherent_with_schedule; eauto 2 => //.
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
      Hypothesis H_busy_prefix_arr : busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
      Hypothesis H_no_busy_prefix_L : ~ busy_interval_prefix arr_seq sched j t1 (t1 + L).

      (** Lemma [job_arrival_is_bounded] implies that the
          busy-interval prefix starts at time [t1], continues until
          [job_arrival j + 1], and then terminates before [t1 + L].
          Or, in other words, there is point in time [t2] such that
          (1) [j]'s arrival is bounded by [t2], (2) [t2] is bounded by
          [t1 + L], and (3) <<[t1, t2)>> is busy interval of job
          [j]. *)
      Local Lemma busy_prefix_is_bounded_case2:
        exists t2,
          job_arrival j < t2
          /\ t2 <= t1 + L
          /\ busy_interval arr_seq sched j t1 t2.
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
  Lemma busy_intervals_are_bounded_rs_edf :
    busy_intervals_are_bounded_by arr_seq sched tsk L.
  Proof.
    move => j ARR TSK POS.
    have PEND : pending sched j (job_arrival j) by apply job_pending_at_arrival => //.
    edestruct ( busy_interval_prefix_exists) as [t1 [GE PREFIX]]; eauto 2; first by apply EDF_is_reflexive.
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
