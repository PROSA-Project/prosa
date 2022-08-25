From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Export prosa.util.fixpoint.
Require Export prosa.results.fixed_priority.rta.fully_preemptive.

(** * RTA for Fully Preemptive FP Scheduling with Computed Fixpoints *)

(** This module refines the general response-time bound for fully preemptive
    fixed-priority scheduling in
    [prosa.results.fixed_priority.rta.fully_preemptive]. Whereas the general
    result assumes that all fixpoints are given, i.e., that they have been found
    _somehow_ without imposing any assumptions on how they have been found, here
    we _compute_ all relevant fixpoints using the procedures provided in
    [prosa.util.fixpoint].  *)

(** ** Problem Setup and Analysis Context *)

(** To begin, we must set up the context as in
    [prosa.results.fixed_priority.rta.fully_preemptive]. *)

Section RTAforFullyPreemptiveFPModelwithArrivalCurves.
  (** We assume ideal uni-processor schedules. *)
  #[local] Existing Instance ideal.processor_state.

  (** Consider any type of tasks characterized by WCETs ... *)
  Context {Task : TaskType} `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks, where each job is
      characterized by an arrival time and an execution cost. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job}.

   (** We assume that jobs and tasks are fully preemptive. *)
   #[local] Existing Instance fully_preemptive_job_model.
   #[local] Existing Instance fully_preemptive_task_model.
   #[local] Existing Instance fully_preemptive_rtc_threshold.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
   Variable arr_seq : arrival_sequence Job.
   Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Consider an arbitrary task set [ts], ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and that the cost of a job does not exceed the task's WCET . *)
  Hypothesis H_valid_job_cost: arrivals_have_valid_job_costs arr_seq.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e., for any task
      [tsk] in [ts], [max_arrival tsk] is (1) an arrival bound for [tsk], and
      (2) it is a monotonic function that equals 0 for the empty interval [delta
      = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Recall that we assume sequential readiness, i.e., jobs of the same task
      are executed in order of their arrival. *)
  #[local] Instance sequential_readiness : JobReady _ _ :=
    sequential_ready_instance arr_seq.

  (** Next, consider any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** Finally, we assume that the schedule is work-conserving ... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and that it respects a reflexive and transitive fixed-priority
          scheduling policy [FP]. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  Hypothesis H_priority_is_transitive : transitive_priorities.
  Hypothesis H_respects_policy :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** ** Computation of the Fixpoints *)

  (** In the following, we introduce the bound on the maximum busy-window length
      [L] and the response-time bound [R] and assume that they have been are
      calculated using the tools provided by [util.fixpoint]. *)

  (** Let [h] denote the horizon for the fixpoint search, i.e., an upper bound
      on the maximum relevant fixpoint. Practically speaking, this is the
      threshold at which the fixpoint search is aborted and ends in failure.
      Since we assume in the following that the fixpoint search terminated
      successfully, it implies that [h] was chosen to be "sufficiently large";
      it may hence be safely ignored in the following. *)
  Variable h : nat.

  (** We let [L] denote the bound on the maximum busy-window length ... *)
  Variable L : duration.

  (** ... and assume that it has been found by means of a successful fixpoint
      search. *)
  Hypothesis H_L_is_fixpoint :
    Some L = find_fixpoint (total_hep_request_bound_function_FP ts tsk) h.

  (** Recall the notion of the search space of the RTA for fixed-priority
      scheduling. *)
  Let is_in_search_space := is_in_search_space tsk L.

  (** We let [R] denote [tsk]'s response-time bound ... *)
  Variable R : duration.

  (** ... and assume that it has been found by means of finding the maximum
          among the fixpoints for each element in the search space with regard
          to the following [recurrence] function. *)
  Let recurrence A F := task_request_bound_function tsk (A + ε)
                        + total_ohep_request_bound_function_FP ts tsk (A + F)
                        - A.
  Hypothesis H_R_is_max_fixpoint :
    Some R = find_max_fixpoint L is_in_search_space recurrence h.

  (** ** Correctness of the Response-Time Bound *)

  (** Using the lemmas from [util.fixpoints], we can show that all preconditions
      of the general fully preemptive fixed-priority RTA theorem are met. *)
  Theorem uniprocessor_response_time_bound_fully_preemptive_fp :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    (* First, eliminate the trivial case of no higher- or equal-priority
       interference. *)
    case: (ltnP 0 (total_hep_request_bound_function_FP ts tsk ε));
      last by rewrite leqn0 => /eqP ZERO; apply: pathological_total_hep_rbf_any_bound; rt_eauto.
    move=> GT0.
    (* Second, apply the general result. *)
    try (eapply uniprocessor_response_time_bound_fully_preemptive_fp
          with (L0 := L) (ts0 := ts) => //)
        ||
        (eapply uniprocessor_response_time_bound_fully_preemptive_fp
          with (L := L) (ts := ts) => //).
    { apply: ffp_finds_positive_fixpoint; eauto.
      exact: total_hep_rbf_monotone. }
    { by apply: ffp_finds_fixpoint; eauto. }
    { move=> A.
      rewrite /bounded_pi.is_in_search_space =>  /andP[LT IN_SP].
      have IN_SP' : (A < L) && is_in_search_space A
        by repeat (apply /andP; split).
      move: (fmf_is_maximum _ _ H_R_is_max_fixpoint IN_SP') => [F FIX BOUND].
      exists F; split => //.
      have: F = recurrence A F
        by apply: ffp_finds_fixpoint; eauto.
      by rewrite /recurrence; lia. }
  Qed.

End RTAforFullyPreemptiveFPModelwithArrivalCurves.
