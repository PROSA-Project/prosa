Require Export prosa.analysis.facts.blocking_bound.elf.
Require Export prosa.analysis.abstract.restricted_supply.abstract_rta.
Require Export prosa.analysis.abstract.restricted_supply.iw_instantiation.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.aux.
Require Export prosa.analysis.definitions.sbf.busy.
Require Export prosa.analysis.facts.priority.jlfp_with_fp.

(** * Sufficient Condition for Bounded Busy Intervals for RS ELF *)

(** In this section, we show that the existence of [L] such that [B +
    total_hep_rbf L <= SBF L], where [B] is the blocking bound and
    [SBF] is a supply-bound function, is a sufficient condition for
    the existence of bounded busy intervals under ELF scheduling with a
    restricted-supply processor model. *)
Section BoundedBusyIntervals.

  (** Consider any type of tasks with relative priority-points ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{PriorityPoint Task}.

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
      relation, and assume that the relation is reflexive, transitive.
      and total. *)
  Context (FP : FP_policy Task).
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

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

  (** Further assume that the schedule follows the ELF scheduling policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched (ELF FP).

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
  Hypothesis H_work_conserving : definitions.work_conserving arr_seq sched.

  (** Consider an arbitrary task set [ts], ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
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

  (** The next step is to establish a bound on the maximum busy-window length,
      which aRSA requires to be given. To this end, let L be any positive
      fixed point of the busy-interval recurrence. As the lemma
      busy_intervals_are_bounded_rs_elf shows, under ELF scheduling, this is
      sufficient to guarantee that all busy intervals are bounded by L. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.

  Hypothesis H_fixed_point:
    forall (A : duration),
      blocking_bound ts tsk A + total_hep_request_bound_function_FP ts tsk L <= SBF L.

  (** Next, we provide a step-by-step proof of busy-interval boundedness. *)
  Section StepByStepProof.

    (** Consider any job [j] of task [tsk] that has a positive job
        cost and is in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Consider [t1] to be the start of the busy-interval. *)
    Variable t1 : instant.

    (** Now we have two cases: (1) when the busy-interval prefix
        continues until time instant [t1 + L] and (2) when the busy
        interval prefix terminates earlier. In either case, we can
        show that the busy-interval prefix is bounded. *)

    (** We start with the first case, where the busy-interval prefix
        continues until time instant [t1 + L]. *)
    Section Case1.

      (** Consider that <<[t1, job_arrival j]>> and <<[t1, t1 + L)>> are both
          busy-interval prefixes of job [j]. Note that at this point we do not
          necessarily know that [job_arrival j <= L]; hence, we assume the
          existence of both prefixes. *)
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
        rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ (t1 + L) _ _ _)); (try apply H_valid_SBF) => //.
        rewrite // addnC -!addnA.
        have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
        apply: E; first by lia.
        rewrite subKn; last by apply: sbf_bounded_by_duration => //.
        specialize (H_fixed_point (job_arrival j - t1)).
        rewrite -(leqRW H_fixed_point); apply leq_add.
        - apply: leq_trans; first apply: service_inversion_is_bounded => //.
          + instantiate (1 := fun (A : duration) => blocking_bound ts tsk A) => //=.
            by move=> jo t t' ARRo TSKo PREFo; apply: nonpreemptive_segments_bounded_by_blocking => //.
          + by done.
        - rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
          apply workload_of_jobs_bounded => //.
          move=> j'.
          move: H_job_of_tsk => /eqP <-.
          by apply hep_job_implies_hep_task.
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
        - by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
        - by apply workload_is_bounded => //.
      Qed.

    End Case1.

    (** Next, we consider the case when the interval <<[t1, t1 + L)>>
        is not a busy-interval prefix. *)
    Section Case2.

      (** Consider that <<[t1, job_arrival j]>> is a busy-interval prefix of [j]
          and <<[t1, t1 + L)>> is _not_. *)
      Hypothesis H_arrives : t1 <= job_arrival j.
      Hypothesis H_busy_prefix_arr : busy_interval_prefix arr_seq sched j t1 (job_arrival j).+1.
      Hypothesis H_no_busy_prefix_L : ~ busy_interval_prefix arr_seq sched j t1 (t1 + L).

      (** From the properties of busy intervals, one can conclude that
          [j]'s arrival time is less than [t1 + L]. *)
      Local Lemma job_arrival_is_bounded :
        job_arrival j < t1 + L.
      Proof.
        move_neq_up FF.
        move: (H_busy_prefix_arr) (H_busy_prefix_arr) => PREFIX PREFIXA.
        apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in PREFIXA => //.
        move: (PREFIXA) => GTC.
        eapply workload_exceeds_interval with (Δ := L) in PREFIX => //.
        { move_neq_down PREFIX.
          rewrite (cumulative_interfering_workload_split _ _ _).
          rewrite (leqRW (blackout_during_bound _ _ _ _ _ _ _ _ (job_arrival j).+1 _ _ _)); (try apply H_valid_SBF) => //.
          rewrite addnC -!addnA.
          have E: forall a b c, a <= c -> b <= c - a -> a + b <= c by move => ? ? ? ? ?; lia.
          apply: E; first by lia.
          rewrite subKn; last by apply: sbf_bounded_by_duration => //.
          specialize (H_fixed_point (job_arrival j - t1)).
          rewrite -(leqRW H_fixed_point); apply leq_add.
          { rewrite (leqRW (service_inversion_widen _ _ _ t1 _ _ (job_arrival j).+1 _ _ )).
            - apply: leq_trans.
              + apply: service_inversion_is_bounded => //.
                move => *; instantiate (1 := fun (A : duration) => blocking_bound ts tsk A) => //.
                by apply: nonpreemptive_segments_bounded_by_blocking => //.
              + by done.
            - by done.
            - lia.
          }
          { rewrite addnC cumulative_iw_hep_eq_workload_of_ohep workload_job_and_ahep_eq_workload_hep //.
            apply workload_of_jobs_bounded => //.
            move=> j'.
            move: H_job_of_tsk => /eqP <-.
            by apply hep_job_implies_hep_task. }
        }
      Qed.

      (** Lemma [job_arrival_is_bounded] implies that the
          busy-interval prefix starts at time [t1], continues until
          [job_arrival j + 1], and then terminates before [t1 + L].
          Or, in other words, there is point in time [t2] such that
          (1) [j]'s arrival is bounded by [t2], (2) [t2] is bounded by
          [t1 + L], and (3) <<[t1, t2)>> is the busy interval of job
          [j]. *)
      Local Lemma busy_prefix_is_bounded_case2:
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
  Lemma busy_intervals_are_bounded_rs_elf :
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
        by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //. }
      { apply busy_prefix_is_bounded_case2=> //.
        move=> NP; apply: NOPREF.
        by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix => //.
      }
    }
  Qed.

End BoundedBusyIntervals.
