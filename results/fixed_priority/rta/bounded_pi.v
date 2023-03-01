Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.abstract.ideal.iw_instantiation.
Require Export prosa.analysis.facts.busy_interval.busy_interval.

(** * Abstract RTA for FP-schedulers with Bounded Priority Inversion *)
(** In this module we instantiate the Abstract Response-Time analysis
    (aRTA) to FP-schedulers for ideal uni-processor model of
    real-time tasks with arbitrary arrival models. *)

(** Given FP priority policy and an ideal uni-processor scheduler
    model, we can explicitly specify [interference],
    [interfering_workload], and [interference_bound_function]. In this
    settings, we can define natural notions of service, workload, busy
    interval, etc. The important feature of this instantiation is that
    we can induce the meaningful notion of priority
    inversion. However, we do not specify the exact cause of priority
    inversion (as there may be different reasons for this, like
    execution of a non-preemptive segment or blocking due to resource
    locking). We only assume that that a priority inversion is
    bounded. *)
Section AbstractRTAforFPwithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context {Arrival : JobArrival Job}.
  Context {Cost : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider an FP policy that indicates a higher-or-equal priority relation,
     and assume that the relation is reflexive. Note that we do not relate
     the FP policy with the scheduler. However, we define functions for
     Interference and Interfering Workload that actively use the concept of
     priorities. We require the FP policy to be reflexive, so a job cannot
     cause lower-priority interference (i.e. priority inversion) to itself. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities (FP_to_JLFP FP).

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any ideal uni-processor schedule of this arrival sequence, ... *)
  Variable sched : schedule (ideal.processor_state Job).

  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context `{@JobReady Job (ideal.processor_state Job) Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid.  *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** ** Instantiation of Interference *)
  (** We say that job [j] incurs interference at time [t] iff it
      cannot execute due to a higher-or-equal-priority job being
      scheduled, or if it incurs a priority inversion. *)
  #[local] Instance ideal_jlfp_interference : Interference Job :=
    ideal_jlfp_interference arr_seq sched.

  (** ** Instantiation of Interfering Workload *)
  (** The interfering workload, in turn, is defined as the sum of the
      priority inversion function and interfering workload of jobs
      with higher or equal priority. *)
  #[local] Instance ideal_jlfp_interfering_workload : InterferingWorkload Job :=
    ideal_jlfp_interfering_workload arr_seq sched.

  (** Note that we differentiate between abstract and classical
      notions of work conserving schedule. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is a work-conserving schedule in the
      _classical_ sense, and later prove that the hypothesis about
      abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** Assume we have sequential tasks, i.e, jobs from the
      same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.

  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
      any task [tsk] in ts [max_arrival tsk] is (1) an arrival bound
      of [tsk], and (2) it is a monotonic function that equals 0 for
      the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtct tsk] is (1) no bigger than [tsk]'s cost, (2) for
      any job of task [tsk] [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** For clarity, let's define some local names. *)
  Let job_pending_at := pending sched.
  Let job_scheduled_at := scheduled_at sched.
  Let job_completed_by := completed_by sched.
  Let job_backlogged_at := backlogged sched.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.

  (** We introduce [task_rbf] as an abbreviation of the task request
      bound function, which is defined as [task_cost(tsk) ×
      max_arrivals(tsk,Δ)]. *)
  Let task_rbf := task_request_bound_function tsk.

  (** Using the sum of individual request bound functions, we define
      the request bound function of all tasks with higher-or-equal
      priority (with respect to [tsk]). *)
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.

  (** Similarly, we define the request bound function of all tasks
      other than [tsk] with higher-or-equal priority (with respect to
      [tsk]). *)
  Let total_ohep_rbf :=
    total_ohep_request_bound_function_FP ts tsk.

  (** Assume that there exists a constant [priority_inversion_bound]
      that bounds the length of any priority inversion experienced by
      any job of [tsk].  Since we analyze only task [tsk], we ignore
      the lengths of priority inversions incurred by any other
      tasks. *)
  Variable priority_inversion_bound : duration.
  Hypothesis H_priority_inversion_is_bounded :
    priority_inversion_is_bounded_by_constant
      arr_seq sched tsk priority_inversion_bound.

  (** Let [L] be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point :
    L = priority_inversion_bound + total_hep_rbf L.

  (** To reduce the time complexity of the analysis, recall the notion
      of search space. Intuitively, this corresponds to all
      "interesting" arrival offsets that the job under analysis might
      have with regard to the beginning of its busy-window. *)
  Definition is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).

  (** Let [R] be a value that upper-bounds the solution of each
      response-time recurrence, i.e., for any relative arrival time
      [A] in the search space, there exists a corresponding solution
      [F] such that [R >= F + (task cost - task lock-in service)]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum :
    forall (A : duration),
      is_in_search_space A ->
      exists (F : duration),
        A + F >= priority_inversion_bound
                + (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk))
                + total_ohep_rbf (A + F) /\
        R >= F + (task_cost tsk - task_rtct tsk).

  (** Finally, we define the interference bound function
      ([IBF_other]). [IBF_other] bounds the interference if tasks are
      sequential. Since tasks are sequential, we exclude interference
      from other jobs of the same task. For FP, we define [IBF_other]
      as the sum of the priority interference bound and the
      higher-or-equal-priority workload. *)
  Let IBF_other (R : duration) := priority_inversion_bound + total_ohep_rbf R.

  (** ** Filling Out Hypotheses Of Abstract RTA Theorem *)
  (** In this section we prove that all preconditions necessary to use
      the abstract theorem are satisfied. *)
  Section FillingOutHypothesesOfAbstractRTATheorem.

    (** Recall that [L] is assumed to be a fixed point of the busy
        interval recurrence. Thanks to this fact, we can prove that
        every busy interval (according to the concrete definition) is
        bounded. In addition, we know that the conventional concept of
        busy interval and the one obtained from the abstract
        definition (with the interference and interfering workload)
        coincide. Thus, it follows that any busy interval (in the
        abstract sense) is bounded. *)
    Lemma instantiated_busy_intervals_are_bounded :
      busy_intervals_are_bounded_by arr_seq sched tsk L.
    Proof.
      move => j ARR TSK POS.
      edestruct (exists_busy_interval) with (delta := L) as [t1 [t2 [T1 [T2 BI]]]]; rt_eauto.
      {
        intros; rewrite {2}H_fixed_point leq_add //.
        rewrite /workload_of_higher_or_equal_priority_jobs /total_hep_rbf
          /total_hep_request_bound_function_FP
          /workload_of_jobs /hep_job /FP_to_JLFP.
        move: (TSK) =>  /eqP ->.
        by apply: sum_of_jobs_le_sum_rbf; eauto. }
      exists t1, t2; split; first by done. split; first by done.
      eapply instantiated_busy_interval_equivalent_busy_interval; rt_eauto.
    Qed.

    (** Next, we prove that [IBF_other] is indeed an interference
        bound.

        Recall that in module abstract_seq_RTA hypothesis
        [task_interference_is_bounded_by] expects to receive a
        function that maps some task [tsk], the relative arrival time of
        a job [j] of task [tsk], and the length of the interval to the
        maximum amount of interference.

        However, in this module we analyze only one task -- [tsk],
        therefore it is “hard-coded” inside the interference bound
        function [IBF_other]. Moreover, in case of a model with fixed
        priorities, interference that some job [j] incurs from
        higher-or-equal priority jobs does not depend on the relative
        arrival time of job [j]. Therefore, in order for the
        [IBF_other] signature to match the required signature in
        module [abstract_seq_RTA], we wrap the [IBF_other] function in
        a function that accepts, but simply ignores, the task and the
        relative arrival time. *)
    Lemma instantiated_task_interference_is_bounded :
      task_interference_is_bounded_by arr_seq sched tsk (fun t A R => IBF_other R).
    Proof.
      intros j R0 t1 t2 ARR TSK ? NCOMPL BUSY; simpl.
      move: (posnP (@job_cost _ Cost j)) => [ZERO|POS].
      { by exfalso; rewrite /completed_by ZERO in  NCOMPL. }
      eapply instantiated_busy_interval_equivalent_busy_interval in BUSY; rt_eauto.
      rewrite /ideal_jlfp_interference; erewrite cumulative_task_interference_split; rt_eauto; last first.
      { by move: BUSY => [[_ [_ [_ /andP [GE LT]]]] _]; eapply arrived_between_implies_in_arrivals; rt_eauto. }
      rewrite /IBF_other leq_add; try done.
      { apply leq_trans with (cumulative_priority_inversion arr_seq sched j t1 (t1 + R0)); first by done.
        apply leq_trans with (cumulative_priority_inversion arr_seq sched j t1 t2); last first.
        { by apply H_priority_inversion_is_bounded; rt_eauto; move: BUSY => [PREF QT2]. }
        rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + R0)) //=.
        - by rewrite leq_addr.
        - by rewrite leq_addr.
        - by rewrite ltnW.
      }
      { erewrite cumulative_i_thep_eq_service_of_othep; rt_eauto;
          last by unfold quiet_time; move: BUSY => [[_ [T1 T2]] _].
        apply: leq_trans.
        { apply service_of_jobs_le_workload; first apply ideal_proc_model_provides_unit_service.
          by apply (valid_schedule_implies_completed_jobs_dont_execute sched arr_seq). }
        { rewrite /workload_of_jobs /total_ohep_rbf /total_ohep_request_bound_function_FP.
          rewrite /another_task_hep_job /hep_job /FP_to_JLFP.
          set (pred_task tsk_other := hep_task tsk_other tsk && (tsk_other != tsk)).
          rewrite (eq_big (fun j=> pred_task (job_task j)) job_cost) //;
            last by move=> j'; rewrite /pred_task; move: TSK => /eqP ->.
          erewrite (eq_big pred_task); [|by done|by move=> tsk'; eauto].
          by apply: sum_of_jobs_le_sum_rbf; eauto. } }
    Qed.

    (** Finally, we show that there exists a solution for the
        response-time recurrence. *)
    Section SolutionOfResponseTimeRecurrenceExists.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_job_cost_positive: job_cost_positive j.

      (** Given any job [j] of task [tsk] that arrives exactly [A]
          units after the beginning of the busy interval, the bound of
          the total interference incurred by [j] within an interval of
          length [Δ] is equal to [task_rbf (A + ε) - task_cost tsk +
          IBF_other Δ]. *)
      Let total_interference_bound tsk A Δ :=
        task_rbf (A + ε) - task_cost tsk + IBF_other Δ.

      (** Next, consider any [A] from the search space (in the
          abstract sense). *)
      Variable A : duration.
      Hypothesis H_A_is_in_abstract_search_space :
        search_space.is_in_search_space tsk L total_interference_bound A.

      (** We prove that [A] is also in the concrete search space. *)
      Lemma A_is_in_concrete_search_space :
        is_in_search_space A.
      Proof.
        move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
        - rewrite INSP.
          apply/andP; split; first by done.
          rewrite neq_ltn; apply/orP; left.
          rewrite {1}/task_rbf; erewrite task_rbf_0_zero; eauto 2; try done.
          rewrite add0n /task_rbf; apply leq_trans with (task_cost tsk).
          + by apply leq_trans with (job_cost j); eauto 2; move: (H_job_of_tsk) => /eqP <-; eauto 2.
          + by eapply task_rbf_1_ge_task_cost; rt_eauto.
        - apply/andP; split; first by done.
          apply/negP; intros EQ; move: EQ => /eqP EQ.
          apply INSP2.
          unfold total_interference_bound in *.
          rewrite subn1 addn1 prednK; last by done.
            by rewrite -EQ.
      Qed.

      (** Then, there exists a solution for the response-time
          recurrence (in the abstract sense). *)
      Corollary correct_search_space :
        exists (F : duration),
          A + F >= task_rbf (A + ε) - (task_cost tsk - task_rtct tsk) + IBF_other (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).
      Proof.
        move: (H_R_is_maximum A) => FIX.
        feed FIX; first by apply A_is_in_concrete_search_space.
        move: FIX => [F [FIX NEQ]].
        exists F; split; last by done.
        rewrite -{2}(leqRW FIX).
          by rewrite addnA [_ + priority_inversion_bound]addnC -!addnA.
      Qed.

    End SolutionOfResponseTimeRecurrenceExists.

  End FillingOutHypothesesOfAbstractRTATheorem.


  (** ** Final Theorem *)
  (** Based on the properties established above, we apply the abstract
      analysis framework to infer that [R] is a response-time bound
      for [tsk]. *)
  Theorem uniprocessor_response_time_bound_fp :
    response_time_bounded_by tsk R.
  Proof.
    intros js ARRs TSKs.
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    eapply uniprocessor_response_time_bound_seq; rt_eauto.
    - by eapply instantiated_i_and_w_are_coherent_with_schedule; rt_eauto.
    - by eapply instantiated_interference_and_workload_consistent_with_sequential_tasks; rt_eauto.
    - by apply instantiated_busy_intervals_are_bounded.
    - by apply instantiated_task_interference_is_bounded.
    - by eapply correct_search_space; eauto 2.
  Qed.

End AbstractRTAforFPwithArrivalCurves.
