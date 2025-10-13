Require Export prosa.model.job.properties.
Require Export prosa.model.composite.valid_task_arrival_sequence.
Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.facts.model.overheads.schedule.
Require Export prosa.analysis.facts.preemption.task.preemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.preemptive.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.fp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fp.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.facts.model.overheads.sbf.fp.

(** * RTA for Fully Preemptive FP Scheduling on Uniprocessors with Overheads *)

(** In the following, we derive a response-time analysis for FP schedulers,
    assuming a workload of fully preemptive sporadic real-time tasks,
    characterized by arbitrary arrival curves, executing upon a uniprocessor
    subject to scheduling overheads. To this end, we instantiate the sequential
    variant of _abstract Restricted-Supply Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)

Section RTAforFullyPreemptiveFPModelwithArrivalCurves.

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
      - a supply-bound function to account for overhead-induced delays. *)

  (** *** Processor Model *)

  (** Consider a unit-speed uniprocessor subject to scheduling overheads. *)
  #[local] Existing Instance overheads.processor_state.

  (** *** Tasks and Jobs  *)

  (** Consider tasks characterized by a WCET [task_cost] and an arrival curve
      [max_arrivals], ... *)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}.

  (** ... and their associated jobs, where each job has a corresponding task
      [job_task], an execution time [job_cost], and an arrival time
      [job_arrival]. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{JobArrival Job}.

  (** Furthermore, assume that jobs and tasks are fully preemptive. *)
  #[local] Existing Instance fully_preemptive_job_model.
  #[local] Existing Instance fully_preemptive_task_model.
  #[local] Existing Instance fully_preemptive_rtc_threshold.

  (** *** The Task Set and the Task Under Analysis*)

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

  (** Consider an arbitrary fixed-priority policy [FP] that indicates a
      higher-or-equal priority relation among the tasks in [ts], and assume that
      the relation is reflexive and transitive. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** Consider a work-conserving, valid uniprocessor schedule _with explicit
      overheads_ that corresponds to the given arrival sequence [arr_seq] (and
      hence the given task set [ts]). *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** We assume that the schedule respects the given [FP] scheduling policy. *)
  Hypothesis H_respects_policy :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** Furthermore, we require that the schedule ensures two additional
      properties: jobs of the same task are executed in the order of their
      arrival, ... *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.

  (** ... and preemptions occur only when strictly required by the scheduling
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

      Under FP scheduling, the bound in an interval of length [Δ] is determined
      by the arrivals of tasks with higher-or-equal priority relative to
      [tsk]. Up to [n] such arrivals can lead to at most [1 + 2n] segments
      without a schedule change, each potentially incurring dispatch,
      context-switch, and preemption-related overhead.

      We denote this bound by [overhead_bound] for the task under analysis
      [tsk]. *)
  Let overhead_bound Δ :=
    (DB + CSB + CRPDB) * (1 + 2 * \sum_(tsk_o <- ts | hep_task tsk_o tsk) max_arrivals tsk_o Δ).

  (** *** Workload Abbreviations *)

  (** For brevity in the following definitions, we introduce a number of local
      abbreviations. *)

  (** We let [rbf] denote the task request-bound function, which is defined as
      [task_cost(T) × max_arrivals(T,Δ)] for a task [T]. *)
  Let rbf := task_request_bound_function.

  (** Additionally, we let [total_hep_rbf] denote the cumulative request-bound
      function w.r.t. all tasks with higher-or-equal priority ... *)
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.

  (** ... and use [total_ohep_rbf] as an abbreviation for the cumulative
      request-bound function w.r.t. all tasks with higher-or-equal priority
      other than task [tsk] itself. *)
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

  (** ** Maximum Length of a Busy Interval *)

  (** In order to apply aRSA, we require a bound on the maximum busy-window
      length.  To this end, let [L] be any positive solution of the
      busy-interval "recurrence" (i.e., inequality) [total_hep_rbf L <= SBF tsk
      L], as defined below.

      As the lemma [busy_intervals_are_bounded_rs_fp] shows, under [FP]
      scheduling, this condition is sufficient to guarantee that the maximum
      busy-window length is at most [L], i.e., the length of any busy interval
      is bounded by [L]. *)
  Definition busy_window_recurrence_solution (L : duration) :=
    L > 0
    /\ L >= overhead_bound L + total_hep_rbf L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally
      time to state the claimed response-time bound [R]. *)

  (** A value [R] is a response-time bound for task [tsk] if, for any given
      offset [A] in the search space (w.r.t. the busy-window bound [L]), the
      response-time bound "recurrence" (i.e., inequality) has a solution [F] not
      exceeding [A + R]. *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space tsk L A ->
      exists (F : duration),
        F >= overhead_bound F + rbf tsk (A + ε) + total_ohep_rbf F
        /\ A + R >= F.

  (** Finally, using the sequential variant of abstract restricted-supply
      analysis, we establish that, given a bound on the maximum busy-window
      length [L], any such [R] is indeed a sound response-time bound for task
      [tsk] under fully-preemptive fixed-priority scheduling on a unit-speed
      uniprocessor subject to scheduling overheads. *)
  Theorem uniprocessor_response_time_bound_fully_preemptive_fp :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    set (sSBF := fp_ovh_sbf_slow ts DB CSB CRPDB tsk).
    move=> L [BW_POS BW_SOL] R SOL js ARRs TSKs.
    have BLOCK: forall tsk , blocking_bound ts tsk = 0.
    { by move=> tsk2; rewrite /blocking_bound /parameters.task_max_nonpreemptive_segment
                 /fully_preemptive_task_model subnn big1_eq. }
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have VBSBF : valid_busy_sbf arr_seq sched tsk sSBF by apply overheads_sbf_busy_valid => //=.
    have USBF : unit_supply_bound_function sSBF by apply overheads_sbf_unit => //=.
    have POStsk: 0 < task_cost tsk
      by move: TSKs => /eqP <-; apply: leq_trans; [apply POS | apply H_valid_task_arrival_sequence].
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) (SBF := sSBF) => //=.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - apply instantiated_interference_and_workload_consistent_with_sequential_tasks => //.
    - eapply busy_intervals_are_bounded_rs_fp with (SBF := sSBF) => //=.
      + exact: instantiated_i_and_w_are_coherent_with_schedule.
      + rewrite BLOCK add0n; apply bound_preserved_under_slowed.
        unfold fp_blackout_bound, overhead_bound, total_hep_rbf in *; lia.
    - apply: valid_pred_sbf_switch_predicate; last (eapply overheads_sbf_busy_valid) => //=.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by apply athep_workload_le_total_ohep_rbf.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        by unshelve rewrite (leqRW (nonpreemptive_segments_bounded_by_blocking _ _ _ _ _ _ _ _ _)) => //.
    - move => A SP; move: (SOL A) => [].
      + apply: search_space_sub => //=.
        { by apply: non_pathological_max_arrivals =>//; apply H_valid_task_arrival_sequence. }
        apply: search_space_switch_IBF; last by exact: SP.
        by move=> A1 Δ1; rewrite //= BLOCK.
      + move => F [FIX LE]; exists F; split => //.
        rewrite /task_intra_IBF /task_rtct /fully_preemptive_rtc_threshold.
        rewrite BLOCK subnn //= add0n addn0 subn0; split.
        * apply bound_preserved_under_slowed.
          move: FIX.
          by rewrite /sSBF -/rbf -/total_ohep_rbf /fp_blackout_bound /overhead_bound; lia.
        * exact: overheads_sbf_monotone.
  Qed.

End RTAforFullyPreemptiveFPModelwithArrivalCurves.
