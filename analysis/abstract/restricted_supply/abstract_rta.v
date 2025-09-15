Require Export prosa.analysis.facts.behavior.supply.
Require Export prosa.analysis.facts.SBF.
Require Export prosa.analysis.abstract.abstract_rta.
Require Export prosa.analysis.abstract.iw_auxiliary.
Require Export prosa.analysis.abstract.IBF.supply.
Require Export prosa.analysis.abstract.restricted_supply.busy_sbf.

(** * Abstract Response-Time Analysis for Restricted-Supply Processors (aRSA) *)
(** In this section we propose a general framework for response-time
    analysis ([RTA]) for real-time tasks with arbitrary arrival models
    under uni-processor scheduling subject to supply restrictions,
    characterized by a given [SBF]. *)

(** We prove that the maximum (with respect to the set of offsets)
    among the solutions of the response-time bound recurrence is a
    response-time bound for [tsk]. Note that in this section we add
    additional restrictions on the processor state. These assumptions
    allow us to eliminate the second equation from [aRTA+]'s
    recurrence since jobs experience delays only due to the lack of
    supply while executing non-preemptively. *)
Section AbstractRTARestrictedSupply.

  (** Consider any type of tasks with a run-to-completion threshold ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any kind of fully supply-consuming unit-supply
      processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Consider any restricted supply uniprocessor schedule of this
      arrival sequence ...*)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume we are given valid WCETs for all tasks.  *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Consider a task set [ts]... *)
  Variable ts : list Task.

  (** ... and a task [tsk] of [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model ... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtc tsk] is (1) no bigger than [tsk]'s cost and (2)
      for any job [j] of task [tsk] [job_rtct j] is bounded by
      [task_rtct tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Assume we are provided with abstract functions for Interference
      and Interfering Workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** We assume that the scheduler is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Let [L] be a constant that bounds any busy interval of task [tsk]. *)
  Variable L : duration.
  Hypothesis H_busy_interval_exists :
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** Consider a unit SBF valid in busy intervals (w.r.t. task
      [tsk]). That is, (1) [SBF 0 = 0], (2) for any duration [Δ], the
      supply produced during a busy-interval prefix of length [Δ] is
      at least [SBF Δ], and (3) [SBF] makes steps of at most one. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched tsk SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  (** Next, we assume that [intra_IBF] is a bound on the intra-supply
      interference incurred by task [tsk]. *)
  Variable intra_IBF : duration -> duration -> duration.
  Hypothesis H_intra_supply_interference_is_bounded :
    intra_interference_is_bounded_by arr_seq sched tsk intra_IBF.

  (** Given any job [j] of task [tsk] that arrives exactly [A] units
      after the beginning of the busy interval, the bound on the
      interference incurred by [j] within an interval of length [Δ] is
      no greater than [(Δ - SBF Δ) + intra_IBF A Δ]. *)
  Let IBF_P (A Δ : duration) :=
    (Δ - SBF Δ) + intra_IBF A Δ.

  (** Next, we instantiate function [IBF_NP], which is a function that
      bounds interference in a non-preemptive stage of execution. We
      prove that this function can be instantiated as [λ tsk F Δ ⟹ (F
      - task_rtct tsk) + (Δ - SBF Δ - (F - SBF F))]. *)

  (** Let us reiterate on the intuitive interpretation of this
      function. Since [F] is a solution to the first equation
      [task_rtct tsk + IBF_P A F <= F], we know that by time
      instant [t1 + F] a job receives [task_rtct tsk] units of service
      and, hence, it becomes non-preemptive. Knowing this information,
      how can we bound the job's interference in an interval
      <<[t1, t1 + Δ)>>?  Note that this interval starts with the beginning of
      the busy interval. We know that the job receives [F - task_rtct
      tsk] units of interference. In the non-preemptive mode, a job
      under analysis can still experience some interference due to a
      lack of supply. This interference is bounded by [(Δ - SBF Δ) -
      (F - SBF F)] since part of this interference has already been
      accounted for in the preemptive part of the execution ([F - SBF
      F]). *)
  Let IBF_NP (F Δ : duration) :=
    (F - task_rtct tsk) + (Δ - SBF Δ - (F - SBF F)).

  (** In the next section, we prove a few helper lemmas. *)
  Section AuxiliaryLemmas.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_job_cost_positive : job_cost_positive j.

      (** Consider the busy interval <<[t1, t2)>> of job [j]. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval : busy_interval_prefix sched j t1 t2.

      (** Let's define [A] as a relative arrival time of job [j] (with
          respect to time [t1]). *)
      Let A : duration := job_arrival j - t1.

      (** Consider an arbitrary time [Δ] ... *)
      Variable Δ : duration.
      (** ... such that [t1 + Δ] is inside the busy interval... *)
      Hypothesis H_inside_busy_interval : t1 + Δ < t2.
      (** ... the job [j] is not completed by time [(t1 + Δ)]. *)
      Hypothesis H_job_j_is_not_completed : ~~ completed_by sched j (t1 + Δ).

      (** First, we show that blackout is counted as interference. *)
      Lemma blackout_impl_interference :
        forall t,
          t1 <= t < t2 ->
          is_blackout sched t ->
          interference j t.
      Proof.
        move=> t /andP [LE1 LE2].
        apply contraLR => /negP INT.
        eapply H_work_conserving in INT =>//; last by lia.
        by apply/negPn; eapply pos_service_impl_pos_supply.
      Qed.

      (** Next, we show that interference is equal to a sum of two
          functions: [is_blackout] and [intra_interference]. *)
      Lemma blackout_plus_local_is_interference :
        forall t,
          t1 <= t < t2 ->
          is_blackout sched t + intra_interference sched j t
          = interference j t.
      Proof.
        move=> t t_INT.
        rewrite /intra_interference /cond_interference.
        destruct (is_blackout sched t) eqn:BLACKOUT; rewrite (negbRL BLACKOUT) //.
        by rewrite blackout_impl_interference.
      Qed.

      (** As a corollary, cumulative interference during a time
          interval <<[t1, t1 + Δ)>> can be split into a sum of total
          blackouts in <<[t1, t1 + Δ)>> and cumulative intra-supply
          interference during <<[t1, t1 + Δ)>>. *)
      Corollary blackout_plus_local_is_interference_cumul :
        blackout_during sched t1 (t1 + Δ) + cumul_intra_interference sched j t1 (t1 + Δ)
        = cumulative_interference j t1 (t1 + Δ).
      Proof.
        rewrite -big_split; apply eq_big_nat => //=.
        move=> t /andP [t_GEQ t_LTN_td].
        move: (ltn_trans t_LTN_td H_inside_busy_interval) => t_LTN_t2.
        by apply blackout_plus_local_is_interference; apply /andP.
      Qed.

      (** Moreover, since the total blackout duration in an interval
          of length [Δ] is bounded by [Δ - SBF Δ], the cumulative
          interference during the time interval <<[t1, t1 + Δ)>> is
          bounded by the sum of [Δ - SBF Δ] and cumulative
          intra-supply interference during <<[t1, t1 + Δ)>>. *)
      Corollary cumulative_job_interference_bound :
        cumulative_interference j t1 (t1 + Δ)
        <= (Δ - SBF Δ) + cumul_intra_interference sched j t1 (t1 + Δ).
      Proof.
        rewrite -blackout_plus_local_is_interference_cumul leq_add2r.
        by eapply blackout_during_bound_SBF with (t2 := t2) => //.
      Qed.

      (** Next, consider a duration [F] such that [F <= Δ] and job [j]
          has enough service to become non-preemptive by time instant
          [t1 + F]. *)
      Variable F : duration.
      Hypothesis H_F_le_Δ : F <= Δ.
      Hypothesis H_enough_service : task_rtct tsk <= service sched j (t1 + F).

      (** Then, we show that job [j] does not experience any
          intra-supply interference in the time interval
          <<[t1 + F, t1 + Δ)>>. *)
      Lemma no_intra_interference_after_F :
        cumul_intra_interference sched j (t1 + F) (t1 + Δ) = 0.
      Proof.
        rewrite /cumul_intra_interference/ cumul_cond_interference big_nat.
        apply big1; move => t /andP [GE__t LT__t].
        apply/eqP; rewrite eqb0; apply/negP.
        move => /andP [P /negPn /negP D]; apply: D; apply/negP.
        eapply H_work_conserving with (t1 := t1) (t2 := t2); eauto 2.
        { by apply/andP; split; lia. }
        eapply progress_inside_supplies; eauto.
        eapply job_nonpreemptive_after_run_to_completion_threshold; eauto 2.
        - rewrite -(leqRW H_enough_service).
          by apply H_valid_run_to_completion_threshold.
        - move: H_job_j_is_not_completed; apply contra.
          by apply completion_monotonic; lia.
      Qed.

  End AuxiliaryLemmas.

  (** For clarity, let's define a local name for the search space. *)
  Let is_in_search_space_rs := is_in_search_space L IBF_P.

  (** We use the following equation to bound the response-time of a
      job of task [tsk]. Consider any value [R] that upper-bounds the
      solution of each response-time recurrence, i.e., for any
      relative arrival time [A] in the search space, there exists a
      corresponding solution [F] such that (1) [F <= A + R],
      (2) [task_rtct tsk + intra_IBF tsk A F <= SBF F] and [SBF F +
      (task_cost tsk - task_rtct tsk) <= SBF (A + R)].

      Note that, compared to "ideal RTA," there is an additional requirement
      [F <= A + R]. Intuitively, it is needed to rule out a nonsensical
      situation when the non-preemptive stage completes earlier than
      the preemptive stage.  *)
  Variable R : duration.
  Hypothesis H_R_is_maximum_rs :
    forall (A : duration),
      is_in_search_space_rs A ->
      exists (F : duration),
        F <= A + R
        /\ task_rtct tsk + intra_IBF A F <= SBF F
        /\ SBF F + (task_cost tsk - task_rtct tsk) <= SBF (A + R).

  (** In the following section we prove that all the premises of
      abstract RTA are satisfied. *)
  Section RSaRTAPremises.

    (** First, we show that [IBF_P] correctly upper-bounds
        interference in the preemptive stage of execution. *)
    Lemma IBF_P_bounds_interference :
      job_interference_is_bounded_by
        arr_seq sched tsk IBF_P (relative_arrival_time_of_job_is_A sched).
    Proof.
      move=> t1 t2 Δ j ARR TSK BUSY LT NCOM A PAR; move: (PAR _ _ BUSY) => EQ.
      rewrite fold_cumul_interference.
      rewrite (leqRW (cumulative_job_interference_bound _ _ _ _ _ t2 _ _ _ _)) => //.
      - rewrite leq_add2l /cumul_intra_interference.
        by apply: H_intra_supply_interference_is_bounded => //.
      - by eapply incomplete_implies_positive_cost => //.
      - by apply BUSY.
    Qed.

    (** Next, we prove that [IBF_NP] correctly bounds interference in
        the non-preemptive stage given a solution to the preemptive
        stage [F]. *)
    Lemma IBF_NP_bounds_interference :
      job_interference_is_bounded_by
        arr_seq sched tsk IBF_NP (relative_time_to_reach_rtct sched tsk IBF_P).
    Proof.
      have USER : unit_service_proc_model PState by apply unit_supply_is_unit_service.
      move=> t1 t2 Δ j ARR TSK BUSY LT NCOM F RT.
      have POS := incomplete_implies_positive_cost _ _ _ NCOM.
      move: (RT _ _ BUSY) (BUSY) => [FIX RTC] [[/andP [LE1 LE2] _] _].
      have RleF : task_rtct tsk <= F.
      { apply cumulative_service_ge_delta with (j := j) (t := t1) (sched := sched) => //.
        rewrite -[X in _ <= X]add0n.
        by erewrite <-cumulative_service_before_job_arrival_zero;
          first erewrite service_during_cat with (t1 := 0) => //; auto; lia. }
      rewrite /IBF_NP addnBAC // leq_subRL_impl // addnC.
      have [NEQ1|NEQ1] := leqP t2 (t1 + F); last have [NEQ2|NEQ2] := leqP F Δ.
      { rewrite -leq_subLR in NEQ1.
        rewrite -{1}(leqRW NEQ1) (leqRW RTC) (leqRW (service_at_most_cost _ _ _ _ _)) => //.
        rewrite (leqRW (cumulative_interference_sub _ _ _ _ t1 t2 _ _)) => //.
        rewrite (leqRW (service_within_busy_interval_ge_job_cost _ _ _ _ _ _ _)) => //.
        have LLL : (t1 < t2) by lia.
        interval_to_duration t1 t2 k.
        by rewrite addnC (leqRW (service_and_interference_bound _ _ _ _ _ _ _ _ _ _ _ _)) => //; lia. }
      { rewrite addnC -{1}(leqRW FIX) -addnA leq_add2l /IBF_P.
        rewrite (@addnC (_ - _) _) -addnA subnKC; last by apply complement_SBF_monotone.
        rewrite -/(cumulative_interference _ _ _).
        erewrite <-blackout_plus_local_is_interference_cumul with (t2 := t2) => //; last by apply BUSY.
        rewrite addnC leq_add //; last first.
        { by eapply blackout_during_bound_SBF with (t2 := t2) => //; split; [ | apply BUSY]. }
        rewrite /cumul_intra_interference (cumulative_interference_cat _ j (t1 + F)) //=; last by lia.
        rewrite -!/(cumul_intra_interference _ _ _ _).
        rewrite (no_intra_interference_after_F _ _ _ _ _ t2) //; last by move: BUSY => [].
        rewrite addn0 //; eapply H_intra_supply_interference_is_bounded => //.
        - by move : NCOM; apply contra, completion_monotonic; lia.
        - move => t1' t2' BUSY'.
          have [EQ1 E2] := busy_interval_is_unique _ _ _ _ _ _ BUSY BUSY'.
          by subst; lia. }
      { rewrite addnC (leqRW RTC); eapply leq_trans.
        - by erewrite leq_add2l; apply cumulative_interference_sub with (bl := t1) (br := t1 + F); lia.
        - erewrite no_service_before_busy_interval => //.
          by rewrite (leqRW (service_and_interference_bound _ _ _ _ _ _ _ _ _ _ _ _)) => //; lia.  }
    Qed.

    (** Next, we prove that [F] is bounded by [task_cost tsk + IBF_NP
        F Δ] for any [F] and [Δ]. As explained in file
        [analysis/abstract/abstract_rta], this shows that the second
        stage indeed takes into account service received in the first
        stage. *)
    Lemma IBF_P_sol_le_IBF_NP :
      forall (F Δ : duration),
        F <= task_cost tsk + IBF_NP F Δ.
    Proof.
      move=> F Δ.
      have [NEQ|NEQ] := leqP F (task_rtct tsk).
      - apply: leq_trans; [apply NEQ | ].
        by apply: leq_trans; [apply H_valid_run_to_completion_threshold | lia].
      - rewrite addnA (@addnBCA _ F _); try lia.
        by apply H_valid_run_to_completion_threshold; lia.
    Qed.

    (** Next we prove that [H_R_is_maximum_rs] implies [H_R_is_maximum]. *)
    Lemma max_in_rs_hypothesis_impl_max_in_arta_hypothesis :
      forall (A : duration),
        is_in_search_space L IBF_P A ->
        exists (F : duration),
          task_rtct tsk + (F - SBF F + intra_IBF A F) <= F
          /\ task_cost tsk + (F - task_rtct tsk + (A + R - SBF (A + R) - (F - SBF F))) <= A + R.
    Proof.
      move=> A SP.
      case: (H_R_is_maximum_rs A SP) => [F [EQ0 [EQ1 EQ2]]].
      exists F; split.
      { have -> : forall a b c, a + (b + c) = (a + c) + b by lia.
        have -T : forall a b c, c >= b -> (a <= c - b) -> (a + b <= c); [by lia | apply: T; first by lia].
        have LE : SBF F <= F by eapply sbf_bounded_by_duration; eauto.
        by rewrite (leqRW EQ1); lia.
      }
      { have JJ := IBF_P_sol_le_IBF_NP F (A + R); rewrite /IBF_NP in JJ.
        rewrite addnA; rewrite addnA in JJ.
        have T: forall a b c, c >= b -> (a <= c - b) -> (a + b <= c); [by lia | apply: T; first by lia].
        rewrite subnA; [ | by apply complement_SBF_monotone | by lia].
        have LE : forall Δ, SBF Δ <= Δ by move => ?; eapply sbf_bounded_by_duration; eauto.
        rewrite subKn; last by eauto.
        have T: forall a b c d e, b >= e -> b >= c ->  e + (a - c) <= d -> a + (b - c) <= d + (b - e) by lia.
        apply : T => //.
        eapply leq_trans; last by apply LE.
        by rewrite -(leqRW EQ1); lia.
      }
    Qed.

  End RSaRTAPremises.

  (** Finally, we apply the [uniprocessor_response_time_bound]
      theorem, and using the lemmas above, we prove that all the
      requirements are satisfied. So, [R] is a response time bound. *)
  Theorem uniprocessor_response_time_bound_restricted_supply :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    eapply uniprocessor_response_time_bound => //.
    { by apply IBF_P_bounds_interference. }
    { by apply IBF_NP_bounds_interference. }
    { by apply IBF_P_sol_le_IBF_NP. }
    { by apply max_in_rs_hypothesis_impl_max_in_arta_hypothesis. }
  Qed.

End AbstractRTARestrictedSupply.
