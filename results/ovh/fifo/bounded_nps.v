Require Export prosa.model.job.properties.
Require Export prosa.model.composite.valid_task_arrival_sequence.
Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.facts.model.overheads.schedule.
Require Export prosa.analysis.facts.preemption.rtc_threshold.limited.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.facts.priority.fifo.
Require Export prosa.analysis.facts.priority.fifo_ahep_bound.
Require Export prosa.analysis.facts.model.overheads.sbf.fifo.

(** * RTA for FIFO Scheduling on Uniprocessors with Overheads *)

(** In the following, we derive a response-time analysis for FIFO schedulers,
    assuming a workload of sporadic real-time tasks, characterized by arbitrary
    arrival curves, executing upon a uniprocessor subject to scheduling
    overheads. To this end, we instantiate the sequential variant of _abstract
    Restricted-Supply Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)
Section RTAforFIFOModelwithArrivalCurves.

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

  (** Consider tasks characterized by a WCET [task_cost], an arrival curve
      [max_arrivals], and a run-to-completion threshold [task_rtct], ... *)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}
          `{TaskRunToCompletionThreshold Task}.

  (** ... and their associated jobs, where each job has a corresponding task
      [job_task], an execution time [job_cost], an arrival time [job_arrival],
      and a list of preemption points [job_preemptable]. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{JobArrival Job}
          `{JobPreemptable Job}.

  (** *** The Task Set and The Task Under Analysis*)

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

  (** We assume that [tsk] is described by a valid task _run-to-completion
      threshold_. That is, there exists a task parameter [task_rtct] such that
      [task_rtct tsk] is
      - (1) no larger than [tsk]'s WCET, and
      - (2) for any job of task [tsk], the job's run-to-completion threshold
            [job_rtct] is bounded by [task_rtct tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

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

  (** Consider a work-conserving, valid uniprocessor schedule with _explicit
      overheads_ that corresponds to the given arrival sequence [arr_seq] (and
      hence the given task set [ts]). *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** We assume that the schedule complies with some valid preemption model.
      Under FIFO scheduling, the specific choice of preemption model does not
      matter, since the resulting schedule behaves as if it were non-preemptive:
      jobs are executed in arrival order without preemption. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** We assume that the schedule respects the FIFO scheduling policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).

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

      Under FIFO scheduling, the bound in an interval of length [Δ] is
      determined by the total number of arrivals in the system. In this case, up
      to [n] such arrivals can lead to at most [1 + n] segments without a
      schedule change, each potentially incurring dispatch, context-switch, and
      preemption-related overhead. Unlike JLFP and FP, FIFO does not require
      doubling the arrivals (i.e., [1 + 2n]), because all jobs are treated
      uniformly and there are no preemptions caused by higher-priority jobs.

      We denote this bound by [overhead_bound] for the task under analysis
      [tsk]. *)
  Let overhead_bound Δ :=
    (DB + CSB + CRPDB) * (1 + \sum_(tsk_o <- ts) max_arrivals tsk_o Δ).

  (** *** Workload Abbreviations *)

  (** For brevity in the following definitions, we introduce a number of local
      abbreviations. *)

  (** We let [rbf] denote the task request-bound function, which is defined as
      [task_cost(T) × max_arrivals(T,Δ)] for a task [T]. *)
  Let rbf := task_request_bound_function.

  (** ** Maximum Length of a Busy Interval *)

  (** In order to apply aRSA, we require a bound on the maximum busy-window
      length. To this end, let [L] be any positive solution of the busy-interval
      "recurrence" (i.e., inequality) [overhead_bound L + total_RBF ts L <= L],
      as defined below.

      As the lemma [busy_intervals_are_bounded_rs_fifo] shows, under [EDF]
      scheduling, this condition is sufficient to guarantee that the maximum
      busy-window length is at most [L], i.e., the length of any busy interval
      is bounded by [L]. *)
  Definition busy_window_recurrence_solution (L : duration) :=
    L > 0
    /\ L >= overhead_bound L + total_request_bound_function ts L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally time to
      state the claimed response-time bound [R]. *)

  (** A value [R] is a response-time bound for task [tsk] if, for any given
      offset [A] in the search space (w.r.t. the busy-window bound [L]), the
      response-time bound "recurrence" (i.e., inequality) has a solution [F] not
      exceeding [R]. *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space ts L A ->
      exists (F : duration),
        A <= F <= A + R
        /\ F >= overhead_bound F + total_request_bound_function ts (A + ε).

  (** Finally, using the abstract restricted-supply analysis, we establish that
      any [R] that satisfies the stated equation is a sound response-time bound
      for FIFO scheduling on a unit-speed uniprocessor subject to scheduling
      overheads. *)
  Theorem uniprocessor_response_time_bound_fifo :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    set (sSBF := fifo_ovh_sbf_slow ts DB CSB CRPDB).
    move=> L [BW_POS BW_SOL] R SOL js ARRs TSKs.
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have VBSBF : valid_busy_sbf arr_seq sched tsk sSBF by apply overheads_sbf_busy_valid => //=.
    have USBF : unit_supply_bound_function sSBF by apply overheads_sbf_unit => //=.
    have POStsk: 0 < task_cost tsk
      by move: TSKs => /eqP <-; apply: leq_trans; [apply POS | apply H_valid_task_arrival_sequence].
    eapply uniprocessor_response_time_bound_restricted_supply
      with (L := L) (intra_IBF  := fun A Δ => (\sum_(tsko <- ts) task_request_bound_function tsko (A + ε)) - task_cost tsk) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - eapply busy_intervals_are_bounded_rs_jlfp with (blocking_bound := fun _ => 0)=> //.
      + exact: instantiated_i_and_w_are_coherent_with_schedule.
      + by apply: FIFO_implies_no_service_inversion.
      + apply bound_preserved_under_slowed.
        by move: BW_SOL; rewrite add0n /sSBF /fifo_blackout_bound /overhead_bound; lia.
    - apply: valid_pred_sbf_switch_predicate; last (eapply overheads_sbf_busy_valid) => //=.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - move => t1 t2 Δ j ARR TSK BUSY LT NCOMPL A OFF.
      move: (OFF _ _ BUSY) => EQA; subst A.
      have [ZERO|POSj] := posnP (job_cost j).
      { by exfalso; rewrite /completed_by ZERO in NCOMPL. }
      eapply leq_trans; first by eapply cumulative_intra_interference_split => //.
      rewrite -[leqRHS]add0n leq_add //.
      + rewrite (leqRW (service_inversion_widen _ _ _ _ _ _ _ _ _)).
        * apply: FIFO_implies_no_service_inversion => //.
          by apply instantiated_busy_interval_equivalent_busy_interval => //.
        * by done.
        * by done.
      + unshelve apply: bound_on_hep_workload; (try apply H_fixed_point).
        all: try apply H_L_positive.
        all: try done.
        apply instantiated_busy_interval_equivalent_busy_interval => //.
    - apply: soln_abstract_response_time_recurrence => //.
      + by apply overheads_sbf_monotone.
      + by apply: non_pathological_max_arrivals =>//; apply H_valid_task_arrival_sequence.
      + move => A SP; move: (SOL A) => [] => // => δ [INδ FIXδ].
        exists δ; split; [done | apply bound_preserved_under_slowed].
        by move: FIXδ; rewrite /sSBF /fifo_blackout_bound /overhead_bound; lia.
  Qed.

End RTAforFIFOModelwithArrivalCurves.
