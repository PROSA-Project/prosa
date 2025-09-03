Require Import prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.model.restricted_supply.schedule.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.
Require Import prosa.analysis.facts.priority.fifo.
Require Export prosa.analysis.facts.priority.fifo_ahep_bound.
Require Export prosa.model.schedule.work_conserving.


(** * RTA for FIFO Scheduling on Restricted-Supply Uniprocessors *)

(** In the following, we derive a response-time analysis for FIFO
    schedulers, assuming a workload of sporadic real-time tasks
    characterized by arbitrary arrival curves executing upon a
    uniprocessor with arbitrary supply restrictions. To this end, we
    instantiate the _abstract Restricted-Supply Response-Time
    Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)
Section RTAforFullyPreemptiveFIFOModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is
      needed to define the system model under consideration. To this
      end, we next introduce and define the following notions using
      Prosa's standard definitions and behavioral semantics:

      - processor model,
      - tasks, jobs, and their parameters,
      - the sequence of job arrivals,
      - worst-case execution time (WCET) and the absence of self-suspensions,
      - the task under analysis,
      - an arbitrary schedule of the task set, and finally,
      - a supply-bound function. *)

  (** *** Processor Model *)

  (** Consider a restricted-supply uniprocessor model. *)
  #[local] Existing Instance rs_processor_state.

  (** *** Tasks and Jobs  *)

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], an arrival curve [max_arrivals], a
      run-to-completion threshold [task_rtct], and a bound on the
      task's longest non-preemptive segment
      [task_max_nonpreemptive_segment] ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], an arrival time
      [job_arrival], and a predicate indicating when the job is
      preemptable [job_preemptable]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobPreemptable Job}.

  (** *** The Job Arrival Sequence *)

  (** Consider any arrival sequence [arr_seq] with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** *** Absence of Self-Suspensions and WCET Compliance *)

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** We further require that a job's cost cannot exceed its task's stated WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** *** The Task Set *)

  (** We consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrivals tsk] is (1) an arrival
      bound of [tsk], and ... *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** ... (2) a monotonic function that equals 0 for the empty interval [delta = 0]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** *** The Schedule *)

  (** Consider any arbitrary, work-conserving, valid restricted-supply
      uni-processor schedule of the given arrival sequence [arr_seq]
      (and hence the given task set [ts]) ... *)
  Variable sched : schedule (rs_processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and assume that the schedule respects the FIFO policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).

  (** We assume a valid preemption model with bounded non-preemptive
      segments. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** *** The Task Under Analysis *)

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** We assume that [tsk] is described by a valid task _run-to-completion
      threshold_. That is, there exists a task parameter [task_rtct] such
      that [task_rtct tsk] is
      - (1) no larger than [tsk]'s WCET, and
      - (2) for any job of task [tsk], the job's run-to-completion threshold
            [job_rtct] is bounded by [task_rtct tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** *** Supply-Bound Function *)

  (** Assume the minimum amount of supply that any job of task [tsk]
      receives is defined by a monotone unit-supply-bound function [SBF]. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_SBF_monotone : sbf_is_monotone SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  (** Next, we assume that [SBF] properly characterizes all busy
      intervals (w.r.t. task [tsk]) in [sched]. That is, (1) [SBF 0 =
      0] and (2) for any duration [Δ], at least [SBF Δ] supply is
      available in any busy-interval prefix of length [Δ]. *)
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched tsk SBF.

  (** ** Length of Busy Interval *)

  (** The next step is to establish a bound on the maximum busy-window
      length, which aRSA requires to be given. *)

  (** To this end, let [L] be any positive fixed point of the
      busy-interval recurrence. As the
      [busy_intervals_are_bounded_rs_jlfp] lemma shows, under any
      preemptive [JLFP] scheduling policy, this is sufficient to
      guarantee that all busy intervals are bounded by [L]. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.
  Hypothesis H_fixed_point : total_request_bound_function ts L <= SBF L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally
      time to state the claimed response-time bound [R]. *)

  (** A value [R] is an RTA-recurrence solution if, for any given
      offset [A] in the search space, the response-time bound
      recurrence has a solution [F] not exceeding [R]. *)
  Definition rta_recurrence_solution R :=
    forall (A : duration),
      is_in_search_space ts L A ->
      exists (F : duration),
        A <= F <= A + R
        /\ total_request_bound_function ts (A + ε) <= SBF F.

  (** Finally, using the abstract restricted-supply analysis, we
      establish that any [R] that satisfies the stated equation is a
      sound response-time bound for the FIFO scheduling with arbitrary
      supply restrictions. *)
  Theorem uniprocessor_response_time_bound_fifo :
    forall (R : duration),
      rta_recurrence_solution R ->
      task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> R SOL js ARRs TSKs.
    have [ZERO|POS] := posnP (job_cost js).
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    have READ : work_bearing_readiness arr_seq sched by done.
    eapply uniprocessor_response_time_bound_restricted_supply
      with (L := L)
           (intra_IBF  := fun A Δ => (\sum_(tsko <- ts) task_request_bound_function tsko (A + ε)) - task_cost tsk) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - eapply busy_intervals_are_bounded_rs_jlfp with (blocking_bound := fun _ => 0)=> //.
      + exact: instantiated_i_and_w_are_coherent_with_schedule.
      + by apply: FIFO_implies_no_service_inversion.
    - apply: valid_pred_sbf_switch_predicate; last by exact: H_valid_SBF.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - move => t1 t2 Δ j ARR TSK BUSY LT NCOMPL A OFF.
      move: (OFF _ _ BUSY) => EQA; subst A.
      have [ZERO|POSj] := posnP (job_cost j).
      { by exfalso; rewrite /completed_by ZERO in NCOMPL. }
      eapply leq_trans; first by eapply cumulative_intra_interference_split => //.
      rewrite -[leqRHS]add0n.
      rewrite leq_add//.
      { rewrite (leqRW (service_inversion_widen _ _ _ _ _ _ _ _ _)).
        - apply: FIFO_implies_no_service_inversion => //.
          apply instantiated_busy_interval_equivalent_busy_interval => //.
        - by done.
        - by done.
      }
      unshelve apply: bound_on_hep_workload; (try apply H_fixed_point).
      all: try apply H_L_positive.
      all: try done.
      apply instantiated_busy_interval_equivalent_busy_interval => //.
    - apply: soln_abstract_response_time_recurrence => //.
  Qed.

End RTAforFullyPreemptiveFIFOModelwithArrivalCurves.
