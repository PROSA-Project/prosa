Require Import prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.preemption.rtc_threshold.limited.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.elf.
Require Export prosa.analysis.abstract.restricted_supply.search_space.elf.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.facts.priority.elf.
Require Export prosa.analysis.facts.blocking_bound.elf.
Require Export prosa.analysis.facts.workload.elf_athep_bound.
Require Export prosa.analysis.definitions.sbf.busy.

(** * RTA for ELF Scheduling with Fixed Preemption Points on Restricted-Supply Uniprocessors *)

(** In the following, we derive a response-time analysis for ELF
    schedulers, assuming a workload of sporadic real-time tasks
    characterized by arbitrary arrival curves executing upon a
    uniprocessor with arbitrary supply restrictions. To this end, we
    instantiate the sequential variant of _abstract Restricted-Supply
    Response-Time Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)
Section RTAforLimitedPreemptiveELFModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is
      needed to define the system model under consideration. To this
      end, we next introduce and define the following notions using
      Prosa's standard definitions and behavioral semantics:

      - tasks, jobs, and their parameters,
      - processor model,
      - the sequence of job arrivals,
      - worst-case execution time (WCET) and the absence of self-suspensions,
      - the set of tasks under analysis,
      - the task under analysis,
      - an arbitrary schedule of the task set, and finally,
      - a supply-bound function. *)

  (** *** Tasks and Jobs  *)

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], relative deadline [task_deadline], an arrival curve
      [max_arrivals], a predicate indicating task's preemption
      points [task_preemption_points], and a relative priority point, ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskPreemptionPoints Task}.
  Context `{PriorityPoint Task}.

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

  (** Consider any valid arrival sequence [arr_seq]. *)
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

  (** We assume a model with fixed preemption points. I.e., each task
      is divided into a number of non-preemptive segments by inserting
      statically predefined preemption points. *)
  Hypothesis H_valid_model_with_fixed_preemption_points :
    valid_fixed_preemption_points_model arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrivals tsk] is (1) an arrival
      bound of [tsk], and ... *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** ... (2) a monotonic function that equals 0 for the empty interval [delta = 0]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** *** The Task Under Analysis *)

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** *** The Schedule *)

  (** Consider any work-conserving, valid
      uniprocessor schedule with limited preemptions of the given
      arrival sequence [arr_seq] (and hence the given task set [ts]). *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_schedule_with_limited_preemptions :
    schedule_respects_preemption_model arr_seq sched.

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation, and assume that the relation is reflexive, transitive
      and total. *)
  Context (FP : FP_policy Task).
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** Assume that the schedule respects the ELF policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched (ELF FP).

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


  (** ** Maximum Length of a Busy Interval *)

  (** In order to apply aRSA, we require a bound on the maximum busy-window
      length. To this end, let [L] be any positive solution of the busy-interval
      "recurrence" (i.e., inequality) [SBF L >= blocking_bound ts tsk A +
      total_hep_request_bound_function_FP ts tsk L] for any relative arrival
      offset [A], as defined below.

      As the lemma [busy_intervals_are_bounded_rs_elf] shows, under [ELF]
      scheduling, this condition is sufficient to guarantee that the maximum
      busy-window length is at most [L], i.e., the length of any busy interval
      is bounded by [L]. *)
  Definition busy_window_recurrence_solution (L : duration) :=
    L > 0
    /\ forall (A : duration),
        SBF L >= blocking_bound ts tsk A
                + total_hep_request_bound_function_FP ts tsk L.


  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally
      time to state the claimed response-time bound [R].

      A value [R] is a response-time bound if, for any given offset
      [A] in the search space, the response-time bound recurrence has
      a solution [F] not exceeding [A + R]. *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space ts tsk L A ->
      exists (F : duration),
        SBF F >= blocking_bound ts tsk A
                + (task_request_bound_function tsk (A + ε) - (task_last_nonpr_segment tsk - ε))
                + bound_on_athep_workload ts tsk A F
        /\ SBF (A + R) >= SBF F + (task_last_nonpr_segment tsk - ε)
        /\ A + R >= F.

  (** Finally, using the sequential variant of abstract
      restricted-supply analysis, we establish that any such [R] is a
      sound response-time bound for the concrete model of ELF
      scheduling with limited preemptions and arbitrary supply
      restrictions. *)
  Theorem uniprocessor_response_time_bound_limited_elf :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> L [BW_POS BW_FIX] R SOL js ARRs TSKs.
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have VAL1 : valid_preemption_model arr_seq sched.
    { apply valid_fixed_preemption_points_model_lemma => //.
      by apply H_valid_model_with_fixed_preemption_points. }
    have READ : work_bearing_readiness arr_seq sched by done.
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - exact: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - apply: busy_intervals_are_bounded_rs_elf => //.
      by apply: instantiated_i_and_w_are_coherent_with_schedule.
    - apply: valid_pred_sbf_switch_predicate; last by exact: H_valid_SBF.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by (apply: bound_on_athep_workload_is_valid; try apply H_fixed_point) => //.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        by apply: nonpreemptive_segments_bounded_by_blocking => //.
    - move=> A SP.
      move: (SOL A) => [].
      { by apply: search_space_sub => //; apply: search_space_switch_IBF. }
      move=> FF [EQ1 [EQ2 EQ3]].
      exists FF; split; last split.
      + lia.
      + move: EQ2; rewrite /task_intra_IBF.
        by erewrite last_segment_eq_cost_minus_rtct => //; lia.
      + by erewrite last_segment_eq_cost_minus_rtct.
  Qed.

End RTAforLimitedPreemptiveELFModelwithArrivalCurves.
