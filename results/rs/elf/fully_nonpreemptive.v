Require Import prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.model.restricted_supply.schedule.
Require Export prosa.analysis.facts.preemption.task.nonpreemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.elf.
Require Export prosa.analysis.abstract.restricted_supply.search_space.elf.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.facts.priority.elf.
Require Export prosa.analysis.facts.blocking_bound.elf.
Require Export prosa.analysis.facts.workload.elf_athep_bound.
Require Export prosa.analysis.definitions.sbf.busy.

(** * RTA for Fully Non-Preemptive ELF Scheduling on Restricted-Supply Uniprocessors *)

(** In the following, we derive a response-time analysis for ELF
    schedulers, assuming a workload of sporadic real-time tasks
    characterized by arbitrary arrival curves executing upon a
    uniprocessor with arbitrary supply restrictions. To this end, we
    instantiate the sequential variant of _abstract Restricted-Supply
    Response-Time Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)
Section RTAforFullyNonPreemptiveELFModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is
      needed to define the system model under consideration. To this
      end, we next introduce and define the following notions using
      Prosa's standard definitions and behavioral semantics:

      - processor model,
      - tasks, jobs, and their parameters,
      - the sequence of job arrivals,
      - worst-case execution time (WCET) and the absence of self-suspensions,
      - the set of tasks under analysis,
      - the task under analysis,
      - an arbitrary schedule of the task set, and finally,
      - a supply-bound function. *)

  (** *** Processor Model *)

  (** Consider a restricted-supply uniprocessor model. *)
  #[local] Existing Instance rs_processor_state.

  (** *** Tasks and Jobs  *)

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], relative deadline [task_deadline], an arrival
      curve [max_arrivals], and a relative priority point, ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{PriorityPoint Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], and an arrival
      time [job_arrival]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** Furthermore, assume that jobs and tasks are fully non-preemptive. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.
  #[local] Existing Instance fully_nonpreemptive_task_model.
  #[local] Existing Instance fully_nonpreemptive_rtc_threshold.

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

  (** Consider any non-preemptive, work-conserving, valid
      restricted-supply uni-processor schedule of the given arrival
      sequence [arr_seq] (and hence the given task set [ts]). *)
  Variable sched : schedule (rs_processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule sched.

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

  (** ** Length of Busy Interval *)

  (** The next step is to establish a bound on the maximum busy-window
      length, which aRSA requires to be given. *)

  (** To this end, let [L] be any positive fixed point of the
      busy-interval recurrence. As the
      [busy_intervals_are_bounded_rs_elf] lemma shows, under
      [ELF] scheduling policy, this is sufficient to
      guarantee that all busy intervals are bounded by [L]. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.
  Hypothesis H_fixed_point :
    forall (A : duration),
      blocking_bound ts tsk A + total_hep_request_bound_function_FP ts tsk L <= SBF L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally
      time to state the claimed response-time bound [R].

      A value [R] is a response-time bound if, for any given offset
      [A] in the search space, the response-time bound recurrence has
      a solution [F] not exceeding [R]. *)
  Definition rta_recurrence_solution R :=
    forall (A : duration),
      is_in_search_space ts tsk L A ->
      exists (F : duration),
        A <= F <= A + R
        /\ blocking_bound ts tsk A
           + (task_request_bound_function tsk (A + ε) - (task_cost tsk - ε))
           + bound_on_athep_workload ts tsk A F
           <= SBF F
        /\ SBF F + (task_cost tsk - ε) <= SBF (A + R).

  (** Finally, using the sequential variant of abstract
      restricted-supply analysis, we establish that any such [R] is a
      sound response-time bound for the concrete model of
      fully-nonpreemptive ELF scheduling with arbitrary supply
      restrictions. *)
  Theorem uniprocessor_response_time_bound_fully_nonpreemptive_elf :
    forall (R : duration),
      rta_recurrence_solution R ->
      task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> R SOL js ARRs TSKs.
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have READ : work_bearing_readiness arr_seq sched by done.
    have VPR : valid_preemption_model arr_seq sched by exact: valid_fully_nonpreemptive_model => //.
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - exact: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - apply: busy_intervals_are_bounded_rs_elf => //.
      exact: instantiated_i_and_w_are_coherent_with_schedule.
    - apply: valid_pred_sbf_switch_predicate; last by exact: H_valid_SBF.
      move => ? ? ? ? [? ?]; split => //.
      by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by (apply: bound_on_athep_workload_is_valid; try apply H_fixed_point) => //.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        by apply: nonpreemptive_segments_bounded_by_blocking => //.
    - move => A SP; move: (SOL A) => [].
      + by apply: search_space_sub => //.
      + move => F [/andP [_ LE] [FIX1 FIX2]]; exists F; split => //.
        rewrite /task_intra_IBF /task_rtct /fully_nonpreemptive_rtc_threshold /constant.
        by split; [rewrite -(leqRW FIX1) | ]; lia.
  Qed.

End RTAforFullyNonPreemptiveELFModelwithArrivalCurves.
