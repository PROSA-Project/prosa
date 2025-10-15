Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.model.overheads.blackout_bound.
Require Export prosa.analysis.facts.model.overheads.schedule_change_bound.
Require Export prosa.analysis.definitions.sbf.busy.

(** In this section, we define an SBF for the FP scheduling policy in
    the presence of overheads. *)
Section OverheadResourceModelValidSBF.

  (** Consider any type of tasks,... *)
  Context {Task : TaskType}.
  Context {FP : FP_policy Task}.
  Context `{MaxArrivals Task}.

  (** ... an arbitrary task set [ts], ... *)
  Variable ts : seq Task.

  (** ... and bounds [DB], [CSB], and [CRPDB] on dispatch overhead,
      context-switch overhead, and preemption-related overhead,
      respectively. *)
  Variable DB CSB CRPDB : duration.

  (** Consider a task [tsk]. *)
  Variable tsk : Task.

  (** We define the blackout bound for FP in an interval of length [Δ]
      as the number of jobs with higher-or-equal priority (w.r.t. a
      given task [tsk]) that can arrive in [Δ] times two, plus one,
      multiplied by the sum of all overhead bounds.

      The "+1" accounts for the fact that [n] arrivals can result in
      up to [1 + 2n] segments without a schedule change, and thus up
      to [1 + 2n] intervals wherein overhead duration is bounded by
      [DB + CSB + CRPDB].

      Under FP scheduling the set of tasks that needs to be considered
      is restricted: only jobs of tasks with higher-or-equal priority
      relative to [tsk] can cause schedule changes, which allows the
      blackout bound to be stated in terms of this subset of tasks. *)
  Definition fp_blackout_bound (Δ : duration) :=
    (DB + CSB + CRPDB) * (1 + 2 * \sum_(tsko <- ts | hep_task tsko tsk) max_arrivals tsko Δ).

  (** First, we define the FP SBF as the interval length minus the FP
      blackout bound. *)
  #[local] Instance fp_ovh_sbf : SupplyBoundFunction :=
    fun Δ => Δ - fp_blackout_bound Δ.

  (** Next, we define the "slowed-down" version of the FP SBF as the
      interval length minus the slowed-down blackout bound. The
      slowdown ensures that the resulting SBF is monotone and
      unit-growth, which is necessary to obtain response-time bounds
      using aRSA. This slowed-down FP SBF is used internally in the
      analysis, while the unmodified FP SBF is used to state the
      top-level analysis result. *)
  Definition fp_ovh_sbf_slow : SupplyBoundFunction :=
    fun Δ => Δ - slowed fp_blackout_bound Δ.

End OverheadResourceModelValidSBF.

(** In the following section, we show that the SBF defined above is
    indeed a valid SBF. *)
Section OverheadResourceModelValidSBF.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{MaxArrivals Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider an FP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** Consider any valid arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any explicit-overhead uni-processor schedule without
      superfluous preemptions of this arrival sequence. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** Assume that the schedule respects the FP policy. *)
  Hypothesis H_respects_policy :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** Assume that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** We consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrival tsk] is (1) an arrival
      bound of [tsk], and ... *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** ... (2) a monotone function that equals 0 for the empty interval [delta = 0]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** We assume that all jobs have positive cost. This restriction is
      not fundamental to the analysis, but rather an artifact of the
      current proof structure in the library. *)
  Hypothesis H_all_jobs_have_positive_cost :
    forall j,
      arrives_in arr_seq j ->
      job_cost_positive j.

  (** Finally, we assume that the schedule respects a valid overhead
      resource model with dispatch overhead [DB], context-switch
      overhead [CSB], and preemption-related overhead [CRPDB]. *)
  Variable DB CSB CRPDB : duration.
  Hypothesis H_valid_overheads_model :
    overhead_resource_model sched DB CSB CRPDB.

  (** We show that the slowed SBF is monotone. *)
  Lemma overheads_sbf_monotone :
    forall tsk,
      sbf_is_monotone (fp_ovh_sbf_slow ts DB CSB CRPDB tsk).
  Proof.
    move=> tsk x y NEQ.
    interval_to_duration x y k.
    have EQ: forall a b c d, (a + d <= b + c) -> (a - b <= c - d). { clear. intros. lia. }
    apply: EQ.
    rewrite [in leqRHS]addnC -addnA leq_add2l.
    apply unit_growth_function_k_steps_bounded.
    by apply slowed_is_unit_step.
  Qed.

  (** In addition, we note that [fp_blackout_bound] is monotone as well. *)
  Remark fp_blackout_bound_monotone :
    forall tsk,
      monotone leq (fp_blackout_bound ts DB CSB CRPDB tsk).
  Proof.
    intros tsk; unfold fp_blackout_bound.
    have Lem1 : forall f c, monotone leq f -> monotone leq (fun x => c * f x).
    { intros f c MON x y LE; specialize (MON x y).
      by apply MON in LE; apply leq_mul. }
    have Lem2: forall f c, monotone leq f -> monotone leq (fun x => c + f x).
    { intros f c MON x y LE; specialize (MON x y).
      by apply MON in LE; apply leq_add. }
    by apply Lem1, Lem2, Lem1, sum_leq_mono, H_valid_arrival_curve.
  Qed.

  (** The slowed SBF is also a unit-supply SBF. *)
  Lemma overheads_sbf_unit :
    forall tsk,
      unit_supply_bound_function (fp_ovh_sbf_slow ts DB CSB CRPDB tsk).
  Proof.
    move=> tsk δ; rewrite/fp_ovh_sbf_slow.
    have LE:
      slowed (fp_blackout_bound ts DB CSB CRPDB tsk) δ
      <= slowed (fp_blackout_bound ts DB CSB CRPDB tsk) δ.+1.
    { apply slowed_respects_monotone; last by lia.
      move=> x y LE; rewrite /fp_ovh_sbf.
      rewrite leq_mul2l; apply/orP; right.
      rewrite leq_add2l leq_mul2l; apply/orP; right.
      rewrite big_seq_cond [leqRHS]big_seq_cond.
      apply leq_sum => tsko /andP [INo _].
      by apply H_valid_arrival_curve.
    }
    lia.
  Qed.

  (** Lastly, we prove that the slowed SBF is valid. *)
  Lemma overheads_sbf_busy_valid :
    forall tsk,
      valid_busy_sbf arr_seq sched tsk (fp_ovh_sbf_slow ts DB CSB CRPDB tsk).
  Proof.
    move => tsk; split; first by unfold fp_ovh_sbf_slow.
    move => j t1 t2 ARR [TSK PREF] t /andP [NEQ1 NEQ2].
    interval_to_duration t1 t δ.
    rewrite supply_during_complement; last first.
    { by apply: overheads_proc_model_provides_unit_supply; eauto 1. }
    rewrite addKn; apply leq_sub2l.
    apply slowed_respects_pointwise_leq with (f := fun δ => blackout_during sched t1 (t1 + δ)).
    { by move=> ?; rewrite addnA; apply blackout_during_unit_growth. }
    move=> Δ LE; rewrite /fp_blackout_bound.
    have F:
      blackout_during sched t1 (t1 + Δ)
      <= (DB + CSB + CRPDB) * (1 + 2 * (\sum_(tsko <- ts | hep_task tsko (job_task j)) max_arrivals tsko Δ)).
    { apply: leq_trans; first by apply: finite_sched_changes_bounded_overheads_blackout => //.
      rewrite /blackout_during leq_mul2l; apply/orP; right.
      have [Z|POSΔ] := posnP Δ.
      { by subst; rewrite addn0 /number_schedule_changes /index_iota subnS subnn //=. }
      rewrite [_ + 1]addnC leq_add2l; eapply schedule_changes_bounded_by_total_arrivals_FP => //.
      lia.
    }
    by apply: leq_trans; [apply: F | move: TSK => /eqP TSK; rewrite -TSK; lia].
  Qed.

End OverheadResourceModelValidSBF.
