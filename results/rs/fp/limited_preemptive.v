Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.facts.preemption.rtc_threshold.limited.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.fp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fp.
Require Export prosa.analysis.facts.model.sbf.periodic.

(** * RTA for FP Scheduling with Fixed Preemption Points on Restricted-Supply Uniprocessors *)

(** In the following, we derive a response-time analysis for FP
    schedulers, assuming a workload of sporadic real-time tasks
    characterized by arbitrary arrival curves executing upon a
    uniprocessor with arbitrary supply restrictions. To this end, we
    instantiate the sequential variant of _abstract Restricted-Supply
    Response-Time Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)
Section RTAforLimitedPreemptiveFPModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is
      needed to define the system model under consideration. To this
      end, we next introduce and define the following notions using
      Prosa's standard definitions and behavioral semantics:

      - tasks, jobs, and their parameters,
      - processor model,
      - the sequence of job arrivals,
      - worst-case execution time (WCET) and the absence of self-suspensions,
      - the task under analysis,
      - an arbitrary schedule of the task set, and finally,
      - a supply-bound function. *)

  (** *** Tasks and Jobs  *)

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], an arrival curve [max_arrivals], and a predicate
      indicating task's preemption points [task_preemption_points], ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskPreemptionPoints Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], an arrival time
      [job_arrival], and a predicate indicating job's preemption
      points [job_preemption_points]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobPreemptionPoints Job}.

  (** We assume that jobs are limited-preemptive. *)
  #[local] Existing Instance limited_preemptive_job_model.

  (** *** Processor Model *)

  (** Consider any kind of fully-supply-consuming, unit-supply
      processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** *** The Job Arrival Sequence *)

  (** Consider any arrival sequence [arr_seq] with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** *** Absence of Self-Suspensions and WCET Compliance *)

  (** We assume the sequential model of readiness without jitter or
      self-suspensions, wherein a pending job [j] is ready as soon as
      all prior jobs of the same task are completed. *)
  #[local] Instance sequential_readiness : JobReady _ _ :=
    sequential_ready_instance arr_seq.

  (** We further require that a job's cost cannot exceed its task's stated WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** *** The Task Set *)

  (** We consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume a model with fixed preemption points. I.e., each task
      is divided into a number of non-preemptive segments by inserting
      statically predefined preemption points. *)
  Hypothesis H_valid_model_with_fixed_preemption_points :
    valid_fixed_preemption_points_model arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrival tsk] is (1) an arrival
      bound of [tsk], and ... *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** ... (2) a monotonic function that equals 0 for the empty interval [delta = 0]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** *** The Task Under Analysis *)

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** *** The Schedule *)

  (** Consider any arbitrary, work-conserving, valid
      uniprocessor schedule with limited preemptions of the given
      arrival sequence [arr_seq] (and hence the given task set [ts]). *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_schedule_with_limited_preemptions :
    schedule_respects_preemption_model arr_seq sched.

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation, and assume that the relation is reflexive and
      transitive. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** We assume that the schedule respects the [FP] scheduling policy. *)
  Hypothesis H_respects_policy_at_preemption_point :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** *** Supply-Bound Function *)

  (** Assume the minimum amount of supply that any job of task [tsk]
      receives is defined by a monotone unit-supply-bound function [SBF]. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_SBF_monotone : sbf_is_monotone SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  (** We assume that [SBF] properly characterizes all busy intervals
      (w.r.t. task [tsk]) in [sched]. That is, (1) [SBF 0 = 0] and (2)
      for any duration [Δ], at least [SBF Δ] supply is available in
      any busy-interval prefix of length [Δ]. *)
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched tsk SBF.

  (** ** Workload Abbreviation *)

  (** We introduce the abbreviation [rbf] for the task request-bound
      function, which is defined as [task_cost(T) × max_arrivals(T,Δ)]
      for a task [T]. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [total_hep_rbf] as an abbreviation for the
      request-bound function of all tasks with higher-or-equal
      priority ... *)
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.

  (** ... and [total_ohep_rbf] as an abbreviation for the
      request-bound function of all tasks with higher-or-equal
      priority other than task [tsk]. *)
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

  (** ** Length of Busy Interval *)

  (** The next step is to establish a bound on the maximum busy-window
      length, which aRSA requires to be given. *)

  (** To this end, let [L] be any positive fixed point of the
      busy-interval recurrence. As the lemma
      [busy_intervals_are_bounded_rs_fp] shows, under [FP] scheduling,
      this is sufficient to guarantee that all busy intervals are
      bounded by [L]. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.
  Hypothesis H_fixed_point : blocking_bound ts tsk + total_hep_rbf L <= SBF L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally
      time to state the claimed response-time bound [R]. *)

  (** A value [R] is a response-time bound if, for any given offset
      [A] in the search space, the response-time bound recurrence has
      a solution [F] not exceeding [A + R]. *)
  Definition rta_recurrence_solution R :=
    forall (A : duration),
      is_in_search_space tsk L A ->
      exists (F : duration),
        SBF F >= blocking_bound ts tsk
                + (rbf tsk (A + ε) - (task_last_nonpr_segment tsk - ε))
                + total_ohep_rbf F
        /\ SBF (A + R) >= SBF F + (task_last_nonpr_segment tsk - ε)
        /\ A + R >= F.

  (** Finally, using the sequential variant of abstract
      restricted-supply analysis, we establish that any such [R] is a
      sound response-time bound for the concrete model of
      fixed-priority scheduling with limited preemptions and with
      arbitrary supply restrictions.  *)
  Theorem uniprocessor_response_time_bound_limited_fp :
    forall (R : duration),
      rta_recurrence_solution R ->
      task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> R SOL js ARRs TSKs.
    have VAL1 : valid_preemption_model arr_seq sched.
    { apply valid_fixed_preemption_points_model_lemma => //.
      by apply H_valid_model_with_fixed_preemption_points. }
    have [ZERO|POS] := posnP (job_cost js);
      first by rewrite /job_response_time_bound /completed_by ZERO.
    have READ : work_bearing_readiness arr_seq sched
      by exact: sequential_readiness_implies_work_bearing_readiness.
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - exact: sequential_readiness_implies_sequential_tasks.
    - exact: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - apply: busy_intervals_are_bounded_rs_fp => //=.
      by apply: instantiated_i_and_w_are_coherent_with_schedule.
    - apply: valid_pred_sbf_switch_predicate; last by exact: H_valid_SBF.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by apply athep_workload_le_total_ohep_rbf.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        unshelve rewrite (leqRW (nonpreemptive_segments_bounded_by_blocking _ _ _ _ _ _ _ _ _)) => //.
        by instantiate (1 := fun _ => blocking_bound ts tsk).
    - move=> A SP.
      move: (SOL A) => [].
      { by apply: search_space_sub => //; apply: search_space_switch_IBF. }
      move=> FF [EQ1 [EQ2 EQ3]].
      exists FF; split; last split.
      + by lia.
      + move: EQ2; rewrite /task_intra_IBF -/rbf -/total_ohep_rbf.
        by erewrite last_segment_eq_cost_minus_rtct => //; lia.
      + by erewrite last_segment_eq_cost_minus_rtct.
  Qed.

End RTAforLimitedPreemptiveFPModelwithArrivalCurves.
