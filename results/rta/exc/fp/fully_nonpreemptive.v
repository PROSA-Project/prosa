Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.fp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fp.
Require Export prosa.analysis.facts.preemption.task.nonpreemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.
Require Export prosa.analysis.facts.model.exceedance.SBF.
Require Export prosa.model.composite.valid_task_arrival_sequence.

(** * Exceedance-Aware RTA for Fully Non-Preemptive Fixed-Priority Uniprocessor Scheduling *)

(** In this file, we state and prove an RTA for ideal uniprocessors with
    exceedance. We assume a fixed-priority policy and fully non-preemptive
    tasks. *)
Section RTA.

  (** Consider tasks characterized by _nominal_ execution times and arbitrary arrival curves, ...*)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}.

  (** ... and their corresponding jobs. *)
  Context {Job : JobType} `{JobTask Job Task}
          `{JobCost Job} `{JobArrival Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We assume sequential readiness. *)
   #[local] Instance sequential_readiness : JobReady _ _ :=
    sequential_ready_instance arr_seq.

  (** We assume that all tasks are fully non-preemptive. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.
  #[local] Existing Instance fully_nonpreemptive_task_model.
  #[local] Existing Instance fully_nonpreemptive_rtc_threshold.

  (** We assume we are given a task set, with valid arrival curves for each task
      in the task set, and that all jobs in the arrival sequence stem from tasks
      in the given task set. *)
  Variable ts : seq Task.
  Hypothesis H_valid_task_arrival_sequence : valid_task_arrival_sequence ts arr_seq.

  (** Assume we have a valid, nonpreemptive, and work-conserving schedule. *)
  Variable sched : schedule (exceedance_proc_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule sched.

  (** Assume that the FP policy under consideration is reflexive
      and transitive. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** We assume that the schedule respects the [FP] scheduling policy. *)
  Hypothesis H_respects_policy_at_preemption_point :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** Let us say that [e] is the bound on the total exceedance ... *)
  Variable e : work.

  (** ... inside any busy interval of a task [tsk] from the given task set. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Let us locally recall the exceedance SBF using [Instance] to make
      it available to the typeclasses hints database. *)
  #[local] Instance EPS_SBF_inst : SupplyBoundFunction := eps_sbf e.

  (** Let us formally state that the total exceedance inside the busy
      window is bounded. *)
  Hypothesis H_exceedance_in_busy_interval_bounded :
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      busy_interval_prefix arr_seq sched j t1 t2 ->
      \sum_(t1 <= t < t2) is_exceedance_exec (sched t) <= e.

  (** First, we define the bound on the maximum length of a busy window. *)
  Definition busy_window_recurrence_solution L :=
    L > e
    /\ L >= blocking_bound ts tsk
          + total_hep_request_bound_function_FP ts tsk L
          + e.

  (** Then we define the response-time "recurrence" (i.e., set of inequalities) ... *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space tsk L A ->
      exists (F : duration),
        F >= blocking_bound ts tsk
            + (task_request_bound_function tsk (A + ε) - (task_cost tsk - ε))
            + total_ohep_request_bound_function_FP ts tsk F
            + e
        /\ A + R >= F + (task_cost tsk - ε).

  (** ... and prove that any solution [R] satisfying this predicate is a bound on the
      maximum response time of task [tsk] in [sched]. *)
  Theorem uniprocessor_response_time_bound_fully_nonpreemptive_fp :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> L [BW_POS BW_FIX] R SOL js ARRs TSKs.
    have VPR : valid_preemption_model arr_seq sched by apply: valid_fully_nonpreemptive_model.
    have [ZERO|POS] := posnP (job_cost js);
      first by rewrite /job_response_time_bound /completed_by ZERO.
    have READ : work_bearing_readiness arr_seq sched
      by apply: sequential_readiness_implies_work_bearing_readiness.
    have NET: arrivals_have_valid_job_costs arr_seq by done.
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) => //.
    - by apply: instantiated_i_and_w_are_coherent_with_schedule => //=.
    - exact: sequential_readiness_implies_sequential_tasks.
    - exact: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - apply: busy_intervals_are_bounded_rs_fp => //.
      + by apply: instantiated_i_and_w_are_coherent_with_schedule.
      + apply: eps_sbf_is_valid.
        exact: H_exceedance_in_busy_interval_bounded.
      + exact: eps_sbf_is_unit.
      + by move: BW_FIX; rewrite /eps_sbf; lia.
      + by move: BW_FIX; rewrite /EPS_SBF_inst /eps_sbf; lia.
    - apply: valid_pred_sbf_switch_predicate; last by exact: eps_sbf_is_valid.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - apply: eps_sbf_is_unit.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by apply athep_workload_le_total_ohep_rbf.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        unshelve rewrite (leqRW (nonpreemptive_segments_bounded_by_blocking _ _ _ _ _ _ _ _ _)) => //.
        by instantiate (1 := fun _ => blocking_bound ts tsk).
    -  move => A SP; move: (SOL A) => [].
       + apply: search_space_sub => //; first lia.
         by apply: non_pathological_max_arrivals =>//; apply H_valid_task_arrival_sequence.
      + move => F [FIX1 FIX2]; exists F; split => //; try lia.
        rewrite /task_intra_IBF /task_rtct /fully_nonpreemptive_rtc_threshold /constant.
        rewrite /EPS_SBF_inst /eps_sbf.
        by split; lia.
  Qed.

End RTA.
