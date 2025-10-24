Require Import prosa.analysis.facts.readiness.basic.
Require Export prosa.model.composite.valid_task_arrival_sequence.
Require Export prosa.analysis.facts.preemption.rtc_threshold.limited.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.
Require Export prosa.analysis.facts.priority.fifo.
Require Export prosa.analysis.facts.priority.fifo_ahep_bound.
Require Export prosa.analysis.facts.model.sbf.average.

(** * RTA for FIFO Scheduling on Uniprocessors under the Average Resource Model *)

(** In the following, we derive a response-time analysis for FIFO schedulers,
    assuming a workload of sporadic real-time tasks, characterized by arbitrary
    arrival curves, executing upon a uniprocessor under the average resource
    model (inspired by the paper "Periodic Resource Model for Compositional Real-Time Guarantees"
    by Shin & Lee, RTSS 2003). To this end, we instantiate the
    sequential variant of _abstract Restricted-Supply Analysis_ (aRSA) as
    provided in the [prosa.analysis.abstract.restricted_supply] module. *)
Section RTAforFIFOModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is needed to
      define the system model under consideration. To this end, we next
      introduce and define the following notions using Prosa's standard
      definitions and behavioral semantics:

      - tasks, jobs, and their parameters,
      - the task set and the task under analysis,
      - the processor model,
      - the sequence of job arrivals,
      - the absence of self-suspensions,
      - an arbitrary schedule of the task set, and finally,
      - the resource-supply model. *)

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

  (** *** Processor Model *)

  (** Consider any kind of fully-supply-consuming, unit-supply
      processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

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

  (** *** Absence of Self-Suspensions *)

  (** We assume the classic (i.e., Liu & Layland) model of readiness without
      jitter or self-suspensions, wherein pending jobs are always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** *** The Schedule *)

  (** Consider a work-conserving, valid uniprocessor schedule that corresponds
      to the given arrival sequence [arr_seq] (and hence the given task set
      [ts]). *)
  Variable sched : schedule PState.
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

  (** *** Average Resource Model *)

  (** Assume that the processor supply follows the *average resource
      model*. Under this model, for any interval <<[t1, t2)>>, and given a
      resource period [Π], a resource allocation time [Θ], and a supply delay
      [ν], the processor provides at least [(t2 - t1 - ν) ⋅ Θ / Π] units of
      supply. Intuitively, this means that _on_ _average_, the processor
      delivers [Θ] units of output every [Π] units of time, while the
      distribution of supply is not ideal and is subject to fluctuations bounded
      by [ν]. Furthermore, let [arm_sbf Π Θ ν] denote the SBF, which, as proven
      in [prosa.analysis.facts.model.sbf.average], is a valid SBF. *)
  Variables Π Θ ν : duration.
  Hypothesis H_average_resource_model : average_resource_model Π Θ ν sched.

  (** ** Maximum Length of a Busy Interval *)

  (** In order to apply aRSA, we require a bound on the maximum busy-window
      length. To this end, let [L] be any positive solution of the busy-interval
      "recurrence" (i.e., inequality) [arm_sbf Π Θ ν L >=
      total_request_bound_function ts L], as defined below.

      As the lemma [busy_intervals_are_bounded_rs_jlfp] shows, under [FIFO]
      scheduling, this condition is sufficient to guarantee that the maximum
      busy-window length is at most [L], i.e., the length of any busy interval
      is bounded by [L]. *)
  Definition busy_window_recurrence_solution (L : duration) :=
    L > 0
    /\ arm_sbf Π Θ ν L >= total_request_bound_function ts L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally time to
      state the claimed response-time bound [R]. *)

  (** A value [R] is a response-time bound for task [tsk] if, for any given
      offset [A] in the search space (w.r.t. the busy-window bound [L]), the
      response-time bound "recurrence" (i.e., inequality) has a solution [F] not
      exceeding [A + R]. *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space ts L A ->
      exists (F : duration),
        arm_sbf Π Θ ν F >= total_request_bound_function ts (A + ε)
        /\ A + R >= F.

  (** Finally, using the abstract restricted-supply analysis, we establish that
      any [R] that satisfies the stated equation is a sound response-time bound
      for FIFO scheduling on a unit-speed uniprocessor under the average
      resource model. *)
  Theorem uniprocessor_response_time_bound_fifo :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> L [BW_POS BW_SOL] R SOL js ARRs TSKs.
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have VBSBF : valid_busy_sbf arr_seq sched tsk (arm_sbf Π Θ ν).
    { by apply: valid_pred_sbf_switch_predicate; last apply arm_sbf_valid. }
    have US : unit_supply_bound_function (arm_sbf Π Θ ν) by exact: arm_sbf_unit.
    have POStsk: 0 < task_cost tsk
      by move: TSKs => /eqP <-; apply: leq_trans; [apply POS | apply H_valid_task_arrival_sequence].
    eapply uniprocessor_response_time_bound_restricted_supply
      with (L := L) (intra_IBF := fun A Δ => (\sum_(tsko <- ts) task_request_bound_function tsko (A + ε)) - task_cost tsk) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - eapply busy_intervals_are_bounded_rs_jlfp with (blocking_bound := fun _ => 0)=> //.
      + exact: instantiated_i_and_w_are_coherent_with_schedule.
      + by apply: FIFO_implies_no_service_inversion.
    - apply: valid_pred_sbf_switch_predicate; last first.
      + by apply arm_sbf_valid.
      + by move => ? ? ? ? [? ?]; split => //.
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
      + by exact: arm_sbf_monotone.
      + by apply: non_pathological_max_arrivals =>//; apply H_valid_task_arrival_sequence.
  Qed.

End RTAforFIFOModelwithArrivalCurves.
