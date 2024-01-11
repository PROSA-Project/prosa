Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.abstract.IBF.supply_task.
Require Export prosa.analysis.abstract.restricted_supply.abstract_rta.

(** * Abstract Response-Time Analysis for Restricted-Supply Processors with Sequential Tasks *)
(** In this section we propose a general framework for response-time
    analysis (RTA) for real-time tasks with arbitrary arrival models
    and _sequential_ _tasks_ under uni-processor scheduling subject to
    supply restrictions, characterized by a given [SBF]. *)

(** In this section, we assume tasks to be sequential. This allows us
    to establish a more precise response-time bound, since jobs of the
    same task will be executed strictly in the order they arrive. *)
Section AbstractRTARestrictedSupplySequential.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context {jc : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any kind of fully-supply-consuming, unit-supply
      processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Consider any restricted supply uniprocessor schedule of this
      arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Consider a task set [ts] ... *)
  Variable ts : list Task.

  (** ... and a task [tsk] of [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model ... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ... with valid task run-to-completion thresholds. That is,
      [task_rtc tsk] is (1) no bigger than [tsk]'s cost and (2) for
      any job [j] of task [tsk] [job_rtct j] is bounded by [task_rtct
      tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts], [max_arrival tsk] is (1) an arrival
      bound of [tsk], and (2) it is a monotonic function that equals
      [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Assume we are provided with functions characterizing
      interference and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Let's define a local name for clarity. *)
  Let task_rbf := task_request_bound_function tsk.

  (** We assume that the scheduler is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Unlike the more general, underlying theorem
      [uniprocessor_response_time_bound_restricted_supply], we assume
      that tasks are sequential. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.
  Hypothesis H_interference_and_workload_consistent_with_sequential_tasks :
    interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk.

  (** Let [L] be a constant that bounds any busy interval of task [tsk]. *)
  Variable L : duration.
  Hypothesis H_busy_interval_exists :
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** Consider a unit SBF valid in busy intervals. That is, (1) [SBF 0
      = 0], (2) for any duration [Δ], the supply produced during a
      busy-interval prefix of length [Δ] is at least [SBF Δ], and (3)
      [SBF] makes steps of at most one. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  (** Next, we assume that [task_intra_IBF] is a bound on intra-supply
      interference incurred by task [tsk]. That is, [task_intra_IBF]
      bounds interference ignoring interference due to lack of supply
      _and_ due to self-interference. *)
  Variable task_intra_IBF : Task -> duration -> duration -> duration.
  Hypothesis H_interference_inside_reservation_is_bounded :
    task_intra_interference_is_bounded_by arr_seq sched tsk task_intra_IBF.

  (** We use the function [task_intra_IBF], which satisfies the
      hypothesis [task_intra_interference_is_bounded_by], to construct
      a new function [intra_IBF := (task_rbf (A + ε) - task_cost tsk)
      + task_intra_IBF tsk A Δ] that satisfies the hypothesis
      [intra_interference_is_bounded_by]. This is needed to later
      apply the lemma [uniprocessor_response_time_bound_restricted_supply]
      from file [restricted_supply/abstract_rta] (recall that it
      requires [intra_IBF], not [task_intra_IBF]). *)

  (** The logic behind [intra_IBF] is quite simple. Consider a job [j]
      of task [tsk] that arrives exactly [A] units after the beginning
      of the busy interval. Then the bound on the total interference
      incurred by [j] within an interval of length [Δ] is no greater
      than [task_rbf (A + ε) - task_cost tsk + task_intra_IBF A
      Δ]. Note that, for sequential tasks, the bound consists of two
      parts: (1) the part that bounds the interference received from
      other jobs of task [tsk] -- [task_rbf (A + ε) - task_cost tsk]
      -- and (2) any other interference that is bounded by
      [task_intra_IBF(tsk, A, Δ)]. *)
  Let intra_IBF (tsk : Task) (A Δ : duration) :=
    (task_rbf (A + ε) - task_cost tsk) + task_intra_IBF tsk A Δ.

  (** For clarity, let's define a local name for the search space. *)
  Let is_in_search_space_rs := is_in_search_space tsk L intra_IBF.

  (** We use the following equation to bound the response-time of a
      job of task [tsk]. Consider any value [R] that upper-bounds the
      solution of each response-time recurrence, i.e., for any
      relative arrival time [A] in the search space, there exists a
      corresponding solution [F] such that
      (1) [F <= A + R],
      (2) [(task_rbf (A + ε) - (task_cost tsk - task_rtct tsk)) + task_intra_IBF tsk A F <= SBF F],
      (3) and [SBF F + (task_cost tsk - task_rtct tsk) <= SBF (A + R)]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum_seq_rs :
    forall (A : duration),
      is_in_search_space_rs A ->
      exists (F : duration),
        F <= A + R
        /\ (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk)) + task_intra_IBF tsk A F <= SBF F
        /\ SBF F + (task_cost tsk - task_rtct tsk) <= SBF (A + R).

  (** In the following section we prove that all the premises of
      [aRSA] are satisfied. *)
  Section aRSAPremises.

    (** First, we show that [intra_IBF] correctly upper-bounds
        interference in the preemptive stage of execution. *)
    Lemma IBF_P_bounds_interference :
      intra_interference_is_bounded_by arr_seq sched tsk intra_IBF.
    Proof.
      move=> t1 t2 Δ j ARR TSK BUSY LT NCOM A PAR; move: (PAR _ _ BUSY) => EQ.
      have [ZERO|POS] := posnP (@job_cost _ jc j).
      { exfalso; move: NCOM => /negP NCOM; apply: NCOM.
        by rewrite /service.completed_by ZERO. }
      rewrite (cumul_cond_interference_ID _ (nonself arr_seq sched)).
      rewrite /intra_IBF addnC leq_add; first by done.
      { rewrite -(leq_add2r (cumul_task_interference arr_seq sched j t1 (t1 + Δ))).
        eapply leq_trans; first last.
        { rewrite EQ; apply: task.cumulative_job_interference_bound => //.
          by apply unit_supply_is_unit_service. }
        { rewrite -big_split //= leq_sum // /cond_interference  => t _.
          by case (interference j t), (has_supply sched t), (nonself arr_seq sched j t) => //. } }
      { rewrite (cumul_cond_interference_pred_eq _ (nonself_intra arr_seq sched)) => //.
        by move=> s t; split=> //; rewrite andbC. }
    Qed.


    (** Consider any job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.

    (** To later apply the theorem
        [uniprocessor_response_time_bound_restricted_supply], we need
        to provide the IBF, which bounds the total interference. *)
    Let IBF tsk A Δ := Δ - SBF Δ + intra_IBF tsk A Δ.

    (** Next we prove that [H_R_is_maximum_seq_rs] implies
        [H_R_is_maximum_rs] from file ([.../restricted_supply/abstract_rta.v]).
        In other words, a solution to the response-time recurrence for
        restricted-supply processor models with sequential tasks can
        be translated to a solution for the same processor model with
        non-necessarily sequential tasks. *)
    Lemma sol_seq_rs_equation_impl_sol_rs_equation :
      forall (A : duration),
        is_in_search_space tsk L IBF  A ->
        exists F : duration,
          F <= A + R
          /\ task_rtct tsk + intra_IBF tsk A F <= SBF F
          /\ SBF F + (task_cost tsk - task_rtct tsk) <= SBF (A + R).
    Proof.
      rewrite /IBF; move=> A SP.
      move: (H_R_is_maximum_seq_rs A) => T.
      feed T.
      { move: SP => [ZERO|[POS [x [LT NEQ]]]]; first by left.
        by right; split => //; exists x; split => //. }
      have [F [EQ0 [EQ1 EQ2]]] := T; clear T.
      exists F; split => //; split => //.
      rewrite /intra_IBF -(leqRW EQ1) addnA leq_add2r.
      rewrite addnBA; last first.
      { apply leq_trans with (task_rbf 1).
        - by apply: task_rbf_1_ge_task_cost => //.
        - by eapply task_rbf_monotone => //; rewrite addn1. }
      { rewrite subnBA.
        - by rewrite addnC.
        - by apply H_valid_run_to_completion_threshold. }
    Qed.

  End aRSAPremises.

  (** Finally, we apply the
      [uniprocessor_response_time_bound_restricted_supply] theorem,
      and using the lemmas above, prove that all its requirements are
      satisfied. Hence, [R] is a response-time bound for task [tsk]. *)
  Theorem uniprocessor_response_time_bound_restricted_supply_seq :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => j ARR TSK.
    eapply uniprocessor_response_time_bound_restricted_supply => //.
    { exact: IBF_P_bounds_interference. }
    { exact: sol_seq_rs_equation_impl_sol_rs_equation. }
  Qed.

End AbstractRTARestrictedSupplySequential.
