Require Import prosa.model.readiness.basic.
Require Import prosa.model.preemption.fully_preemptive.
Require Export prosa.analysis.facts.transform.edf_opt.
Require Export prosa.analysis.facts.transform.edf_wc.
Require Export prosa.analysis.facts.edf_definitions.
Require prosa.model.priority.edf.

(** * Optimality of EDF on Ideal Uniprocessors *)

(** This module provides the famous EDF optimality theorem: if there
    is any way to meet all deadlines (assuming an ideal uniprocessor
    schedule), then there is also an (ideal) EDF schedule in which all
    deadlines are met. *)

(** ** Optimality Theorem *)

Section Optimality.

  (** Consider any given type of jobs, each characterized by execution
      costs, an arrival time, and an absolute deadline,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any valid arrival sequence of such jobs. *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** We assume that jobs are fully preemptive. *)
  #[local] Existing Instance fully_preemptive_job_model.

  (** Under these assumptions, EDF is optimal in the sense that, if there
      exists any schedule in which all jobs of [arr_seq] meet their deadline,
      then there also exists an EDF schedule in which all deadlines are met. *)
  Theorem EDF_optimality:
    (exists any_sched : schedule (ideal.processor_state Job),
        valid_schedule any_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq any_sched) ->
    exists edf_sched : schedule (ideal.processor_state Job),
        valid_schedule edf_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq edf_sched /\
        EDF_schedule edf_sched.
  Proof.
    move=> [sched [[COME READY] DL_ARR_MET]].
    have ARR  := jobs_must_arrive_to_be_ready sched READY.
    have COMP := completed_jobs_are_not_ready sched READY.
    move: (all_deadlines_met_in_valid_schedule _ _ COME DL_ARR_MET) => DL_MET.
    set sched' := edf_transform sched.
    exists sched'. split; last split.
    - by apply edf_schedule_is_valid.
    - by apply edf_schedule_meets_all_deadlines_wrt_arrivals.
    - by apply edf_transform_ensures_edf.
  Qed.

  (** Moreover, we note that, since EDF maintains work conservation, if there
      exists a schedule in which all jobs of [arr_seq] meet their deadline,
      then there also exists a work-conserving EDF in which all deadlines are
      met. *)
  Theorem EDF_WC_optimality :
    (exists any_sched : schedule (ideal.processor_state Job),
        valid_schedule any_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq any_sched) ->
    exists edf_wc_sched : schedule (ideal.processor_state Job),
      valid_schedule edf_wc_sched arr_seq /\
      all_deadlines_of_arrivals_met arr_seq edf_wc_sched /\
      work_conserving arr_seq edf_wc_sched /\
      EDF_schedule edf_wc_sched.
  Proof.
    move=> [sched [[COME READY] DL_ARR_MET]].
    move: (all_deadlines_met_in_valid_schedule _ _ COME DL_ARR_MET) => DL_MET.
    set wc_sched := wc_transform arr_seq sched.
    have wc_COME : jobs_come_from_arrival_sequence wc_sched arr_seq
      by apply wc_jobs_come_from_arrival_sequence.
    have wc_READY : jobs_must_be_ready_to_execute wc_sched
      by apply wc_jobs_must_be_ready_to_execute.
    have wc_ARR := jobs_must_arrive_to_be_ready wc_sched wc_READY.
    have wc_COMP := completed_jobs_are_not_ready wc_sched wc_READY.
    have wc_DL_ARR_MET : all_deadlines_of_arrivals_met arr_seq wc_sched
      by apply wc_all_deadlines_of_arrivals_met; apply DL_ARR_MET.
    move: (all_deadlines_met_in_valid_schedule _ _ wc_COME wc_DL_ARR_MET) => wc_DL_MET.
    set sched' := edf_transform wc_sched.
    exists sched'. split; last split; last split.
    - by apply edf_schedule_is_valid.
    - by apply edf_schedule_meets_all_deadlines_wrt_arrivals.
    - apply edf_transform_maintains_work_conservation; by [ | apply wc_is_work_conserving ].
    - by apply edf_transform_ensures_edf.
  Qed.

  (** Remark: [EDF_optimality] is of course an immediate corollary of
      [EDF_WC_optimality]. We nonetheless have two separate proofs for historic
      reasons as [EDF_optimality] predates [EDF_WC_optimality] (in Prosa). *)

  (** Finally, we state the optimality theorem also in terms of a
      policy-compliant schedule, which a more generic notion used in Prosa for
      scheduling policies (rather than the simpler, but ad-hoc
      [EDF_schedule] predicate used above).

      Given that we're considering the EDF priority policy and a fully
      preemptive job model, satisfying the [EDF_schedule] predicate is
      equivalent to satisfying the [respects_policy_at_preemption_point]
      w.r.t. to the EDF policy predicate. The optimality of priority-compliant
      schedules that are work-conserving follows hence directly from the above
      [EDF_WC_optimality] theorem. *)
  Corollary EDF_priority_compliant_WC_optimality:
    (exists any_sched : schedule (ideal.processor_state Job),
        valid_schedule any_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq any_sched) ->
    exists priority_compliant_sched : schedule (ideal.processor_state Job),
        valid_schedule priority_compliant_sched arr_seq /\
        all_deadlines_of_arrivals_met arr_seq priority_compliant_sched /\
        work_conserving arr_seq priority_compliant_sched /\
        respects_JLFP_policy_at_preemption_point arr_seq priority_compliant_sched (EDF Job).
  Proof.
    move /EDF_WC_optimality => [edf_sched [[ARR READY] [DL_MET [WC EDF]]]].
    exists edf_sched.
    apply (EDF_schedule_equiv arr_seq _) in EDF => //.
    now apply (completed_jobs_are_not_ready edf_sched READY).
  Qed.

End Optimality.

(** ** Weak Optimality Theorem *)

(** We further state a weaker notion of the above optimality result
    that avoids a dependency on a given arrival
    sequence. Specifically, it establishes that, given a reference
    schedule without deadline misses, there exists an EDF schedule of
    the same jobs in which no deadlines are missed. *)
Section WeakOptimality.

  (** For any given type of jobs, each characterized by execution
      costs, an arrival time, and an absolute deadline,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... if we have a well-behaved reference schedule ... *)
  Variable any_sched: schedule (ideal.processor_state Job).
  Hypothesis H_must_arrive: jobs_must_arrive_to_execute any_sched.
  Hypothesis H_completed_dont_execute: completed_jobs_dont_execute any_sched.

  (**  ... in which no deadlines are missed, ... *)
  Hypothesis H_all_deadlines_met: all_deadlines_met any_sched.

  (** ...then there also exists an EDF schedule in which no deadlines
      are missed (and in which exactly the same set of jobs is
      scheduled, as ensured by the last clause). *)
  Theorem weak_EDF_optimality:
    exists edf_sched : schedule (ideal.processor_state Job),
      jobs_must_arrive_to_execute edf_sched /\
      completed_jobs_dont_execute edf_sched /\
      all_deadlines_met edf_sched /\
      EDF_schedule edf_sched /\
      forall j,
          (exists t,  scheduled_at any_sched j t) <->
          (exists t', scheduled_at edf_sched j t').
  Proof.
    set sched' := edf_transform any_sched.
    exists sched'. repeat split.
    - by apply edf_transform_jobs_must_arrive.
    - by apply edf_transform_completed_jobs_dont_execute.
    - by apply edf_transform_deadlines_met.
    - by apply edf_transform_ensures_edf.
    - by move=> [t SCHED_j]; apply edf_transform_job_scheduled' with (t := t).
    - by move=> [t SCHED_j]; apply edf_transform_job_scheduled with (t := t).
  Qed.

End WeakOptimality.
