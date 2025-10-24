Require Export prosa.model.job.properties.
Require Export prosa.model.composite.valid_task_arrival_sequence.
Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.facts.model.overheads.schedule.
Require Export prosa.analysis.facts.preemption.task.nonpreemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.edf.
Require Export prosa.analysis.abstract.restricted_supply.search_space.edf.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.facts.priority.edf.
Require Export prosa.analysis.facts.blocking_bound.edf.
Require Export prosa.analysis.facts.workload.edf_athep_bound.
Require Export prosa.analysis.facts.model.overheads.sbf.jlfp.

(** * RTA for Fully Non-Preemptive EDF Scheduling on Uniprocessors with Overheads *)

(** In the following, we derive a response-time analysis for EDF schedulers,
    assuming a workload of sporadic fully non-preemptive real-time tasks,
    characterized by arbitrary arrival curves, executing upon a uniprocessor
    subject to scheduling overheads. To this end, we instantiate the sequential
    variant of _abstract Restricted-Supply Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)

Section RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is needed to
      define the system model under consideration. To this end, we next
      introduce and define the following notions using Prosa's standard
      definitions and behavioral semantics:

      - the processor model,
      - tasks, jobs, and their parameters,
      - the task set and the task under analysis,
      - the sequence of job arrivals,
      - the absence of self-suspensions,
      - an arbitrary schedule of the task set, and finally,
      - an upper bound on overhead-induced delays. *)

  (** *** Processor Model *)

  (** Consider a unit-speed uniprocessor subject to scheduling overheads. *)
  #[local] Existing Instance overheads.processor_state.

  (** *** Tasks and Jobs  *)

  (** Consider tasks characterized by a WCET [task_cost], relative deadline
      [task_deadline], and an arrival curve [max_arrivals], ... *)
  Context {Task : TaskType} `{TaskCost Task} `{TaskDeadline Task} `{MaxArrivals Task}.

  (** ... and their associated jobs, where each job has a corresponding task
      [job_task], an execution time [job_cost], and an arrival time
      [job_arrival]. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{JobArrival Job}.

  (** Furthermore, assume that jobs and tasks are fully non-preemptive. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.
  #[local] Existing Instance fully_nonpreemptive_task_model.
  #[local] Existing Instance fully_nonpreemptive_rtc_threshold.

  (** *** The Task Set and the Task Under Analysis *)

  (** Consider an arbitrary task set [ts], and ... *)
  Variable ts : seq Task.

  (** ... let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** *** The Job Arrival Sequence *)

  (** Allow for any possible arrival sequence [arr_seq] consistent with the
      parameters of the task set [ts]. That is, [arr_seq] is a valid arrival
      sequence in which each job's cost is upper-bounded by its task's WCET,
      every job stems from a task in [ts], and the number of arrivals respects
      each task's [max_arrivals] bound. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_task_arrival_sequence : valid_task_arrival_sequence ts arr_seq.

  (** Additionally, we assume that all jobs in [arr_seq] have positive execution
      costs. This requirement is not fundamental to the analysis approach itself
      but reflects an artifact of the current proof structure specific to upper
      bounds on the total duration of overheads. *)
  Hypothesis H_arrivals_have_positive_job_costs :
    arrivals_have_positive_job_costs arr_seq.

  (** *** Absence of Self-Suspensions *)

  (** We assume the classic (i.e., Liu & Layland) model of readiness without
      jitter or self-suspensions, wherein pending jobs are always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** *** The Schedule *)

  (** Consider a non-preemptive, work-conserving, valid uniprocessor schedule
      _with explicit overheads_ that corresponds to the given arrival sequence
      [arr_seq] (and hence the given task set [ts]). *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule sched.

  (** We assume that the schedule respects the given [EDF] scheduling policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).

  (** Furthermore, we require that the schedule has no superfluous preemptions;
      that is, preemptions occur only when strictly required by the scheduling
      policy (specifically, a job is never preempted by another job of equal
      priority). *)
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** *** Bounding the Total Overhead Duration *)

  (** We assume that the scheduling overheads encountered in the schedule [sched]
      are bounded by the following upper bounds:

      - the maximum _dispatch overhead_ is bounded by [DB],
      - the maximum _context-switch overhead_ is bounded by [CSB], and
      - the maximum _cache-related preemption delay_ is bounded by [CRPDB]. *)
  Variable DB CSB CRPDB : duration.
  Hypothesis H_valid_overheads_model : overhead_resource_model sched DB CSB CRPDB.

  (** To conservatively account for the maximum cumulative delay that task [tsk]
      may experience due to scheduling overheads, we introduce an _overhead
      bound_. This term upper-bounds the maximum cumulative duration during
      which processor cycles are "lost" to dispatch, context-switch, and
      preemption-related delays in a given interval.

      For EDF scheduling, we use a generic JLFP bound, where the bound in an
      interval of length [Δ] is determined by the total number of arrivals in
      the system. In this case, up to [n] such arrivals can lead to at most [1 +
      2n] segments without a schedule change, each potentially incurring
      dispatch, context-switch, and preemption-related overhead. *)
  Let overhead_bound Δ :=
    (DB + CSB + CRPDB) * (1 + 2 * \sum_(tsk_o <- ts) max_arrivals tsk_o Δ).

  (** ** Maximum Length of a Busy Interval *)

  (** In order to apply aRSA, we require a bound on the maximum busy-window
      length. To this end, let [L] be any positive solution of the busy-interval
      "recurrences" (i.e., set of inequalities) [overhead_bound L +
      total_request_bound_function ts L <= L] and [overhead_bound L +
      longest_busy_interval_with_pi ts tsk <= L], as defined below.

      As the lemma [busy_intervals_are_bounded_rs_edf] shows, under [EDF]
      scheduling, this condition is sufficient to guarantee that the maximum
      busy-window length is at most [L], i.e., the length of any busy interval
      is bounded by [L]. *)
  Definition busy_window_recurrence_solution (L : duration) :=
    L > 0
    /\ L >= overhead_bound L + total_request_bound_function ts L
    /\ L >= overhead_bound L + longest_busy_interval_with_pi ts tsk.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally time to
      state the claimed response-time bound [R]. *)

  (** A value [R] is a response-time bound for task [tsk] if, for any given
      offset [A] in the search space (w.r.t. the busy-window bound [L]), the
      response-time bound "recurrence" (i.e., inequality) has a solution [F] not
      exceeding [R]. *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space ts tsk L A ->
      exists (F : duration),
        F >= overhead_bound F
              + blocking_bound ts tsk A
              + (task_request_bound_function tsk (A + ε) - (task_cost tsk - ε))
              + bound_on_athep_workload ts tsk A F
        /\ A + R >= F + (overhead_bound (A + R) - overhead_bound F)
                  + (task_cost tsk - ε).

  (** Finally, using the sequential variant of abstract restricted-supply
      analysis, we establish that, given a bound on the maximum busy-window
      length [L], any such [R] is indeed a sound response-time bound for task
      [tsk] under fully non-preemptive EDF scheduling on a unit-speed
      uniprocessor subject to scheduling overheads. *)
  Theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> L [BW_POS [BW_SOL1 BW_SOL2]] R SOL js ARRs TSKs; set (sSBF := jlfp_ovh_sbf_slow ts DB CSB CRPDB).
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have VMBNS : valid_model_with_bounded_nonpreemptive_segments arr_seq sched
      by apply fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions => //.
    have VBSBF : valid_busy_sbf arr_seq sched tsk sSBF by apply overheads_sbf_busy_valid => //=.
    have USBF : unit_supply_bound_function sSBF by apply overheads_sbf_unit => //=.
    have POStsk: 0 < task_cost tsk
      by move: TSKs => /eqP <-; apply: leq_trans; [apply POS | apply H_valid_task_arrival_sequence].
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) (SBF := sSBF) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - exact: EDF_implies_sequential_tasks.
    - exact: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - apply: busy_intervals_are_bounded_rs_edf => //.
      + by apply: instantiated_i_and_w_are_coherent_with_schedule.
      + by apply bound_preserved_under_slowed; unfold jlfp_blackout_bound, overhead_bound in *; lia.
      + by apply bound_preserved_under_slowed; unfold jlfp_blackout_bound, overhead_bound in *; lia.
    - apply: valid_pred_sbf_switch_predicate; last (eapply overheads_sbf_busy_valid) => //=.
      by move => ? ? ? ? [? ?]; split => //; apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by (apply: bound_on_athep_workload_is_valid; try apply H_fixed_point) => //.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        by apply: nonpreemptive_segments_bounded_by_blocking => //.
    - move=> A SP; move: (SOL A) => [].
      + apply: search_space_sub => //=.
        by apply: non_pathological_max_arrivals =>//; apply H_valid_task_arrival_sequence.
      + move => F [FIX1 FIX2].
        have [δ [LEδ EQ]]:= slowed_subtraction_value_preservation
                              (jlfp_blackout_bound ts DB CSB CRPDB) F (ltac:(apply jlfp_blackout_bound_monotone => //)).
        exists δ; split; [lia | split].
        * rewrite /sSBF /jlfp_ovh_sbf_slow -EQ.
          apply: leq_trans; last by apply leq_subRL_impl; rewrite -!addnA in FIX1; apply FIX1.
          have NEQ: bound_on_athep_workload ts tsk A δ <= bound_on_athep_workload ts tsk A F
            by apply bound_on_athep_workload_monotone.
          by move: FIX1; rewrite /task_intra_IBF; set (c := _ _ (A +1) - ( _ )); lia.
        * rewrite /sSBF /jlfp_ovh_sbf_slow -EQ.
          apply bound_preserved_under_slowed, leq_subRL_impl; apply: leq_trans; last by apply FIX2.
          move: FIX1; rewrite /task_rtct /fully_nonpreemptive_rtc_threshold /constant
                              /jlfp_blackout_bound /overhead_bound; lia.
  Qed.

End RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.
