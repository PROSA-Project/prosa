Require Export prosa.analysis.facts.priority.edf.
Require Export prosa.analysis.definitions.schedulability.
Require Import prosa.model.readiness.basic.
Require Import prosa.model.priority.edf.
Require Import prosa.model.task.absolute_deadline.
Require Import prosa.analysis.abstract.ideal.cumulative_bounds.
Require Import prosa.analysis.facts.busy_interval.carry_in.
Require Import prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.abstract.ideal.abstract_seq_rta.
Require Export prosa.analysis.facts.model.task_cost.

(** * Abstract RTA for EDF-schedulers with Bounded Priority Inversion *)
(** In this module we instantiate the Abstract Response-Time analysis
    (aRTA) to EDF-schedulers for ideal uni-processor model of
    real-time tasks with arbitrary arrival models. *)

(** Given EDF priority policy and an ideal uni-processor scheduler
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

Section AbstractRTAforEDFwithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.


  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context {Arrival : JobArrival Job}.
  Context {Cost : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For clarity, let's denote the relative deadline of a task as D. *)
  Let D tsk := task_deadline tsk.

  (** Consider the EDF policy that indicates a higher-or-equal
      priority relation. Note that we do not relate the EDF policy
      with the scheduler. However, we define functions for
      Interference and Interfering Workload that actively use the
      concept of priorities. *)
  Let EDF := EDF Job.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any valid ideal uni-processor schedule of this arrival sequence
      that follows the scheduling policy. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched EDF.

  (** To use the theorem [uniprocessor_response_time_bound_seq] from
      the Abstract RTA module, we need to specify functions of
      interference, interfering workload, and [task_IBF]. Next, we
      define interference and interfering workload; we return to
      [task_IBF] later. *)

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
      notions of work-conserving schedule. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is a work-conserving schedule
     in the _classical_ sense, and later prove that the hypothesis
     about abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set ts. *)
  Variable ts : list Task.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
      any task [tsk] in [ts], [max_arrival tsk] is (1) an arrival bound
      of [tsk], and (2) it is a monotonic function that equals 0 for
      the empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtct tsk] is (1) no bigger than [tsk]'s cost, (2) for
      any job of task [tsk] [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** We introduce [rbf] as an abbreviation of the task request bound
      function, which is defined as [task_cost(T) × max_arrivals(T,Δ)]
      for some task [T]. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [task_rbf] as an abbreviation of the task
      request bound function of task [tsk]. *)
  Let task_rbf := rbf tsk.

  (** Using the sum of individual request bound functions, we define
      the request bound function of all tasks (total request bound
      function). *)
  Let total_rbf := total_request_bound_function ts.

  (** Assume that there exists a bound on the length of any priority
      inversion experienced by any job of task [tsk]. Since we analyze
      only task [tsk], we ignore the lengths of priority inversions
      incurred by any other tasks. *)
  Variable priority_inversion_bound : duration -> duration.
  Hypothesis H_priority_inversion_is_bounded :
    priority_inversion_is_bounded_by
     arr_seq sched tsk priority_inversion_bound.

  (** Let [L] be any positive fixed point of the busy interval
      recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_rbf L.

  (** Next, we define an upper bound on interfering workload received
      from jobs of other tasks with higher-than-or-equal priority. *)
  Let bound_on_total_hep_workload (A Δ : duration) :=
    \sum_(tsk_o <- ts | tsk_o != tsk)
     rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

  (** To reduce the time complexity of the analysis, we introduce the
      notion of search space for EDF. Intuitively, this corresponds to
      all "interesting" arrival offsets that the job under analysis
      might have with regard to the beginning of its busy-window. *)

  (** In the case of the search space for EDF, we consider three
      conditions. First, we ask whether [task_rbf A ≠ task_rbf (A +
      ε)]. *)
  Definition task_rbf_changes_at (A : duration) := task_rbf A != task_rbf (A + ε).

  (** Second, we ask whether there exists a task [tsko] from [ts] such
      that [tsko ≠ tsk] and [rbf(tsko, A + D tsk - D tsko) ≠ rbf(tsko,
      A + ε + D tsk - D tsko)]. Note that we use a slightly uncommon
      notation [has (λ tsko ⇒ P tskₒ) ts], which can be interpreted as
      follows: the task set [ts] contains a task [tsko] such that a
      predicate [P] holds for [tsko]. *)
  Definition bound_on_total_hep_workload_changes_at A :=
    has (fun tsko =>
           (tsk != tsko)
             && (rbf tsko (A + D tsk - D tsko)
                     != rbf tsko ((A + ε) + D tsk - D tsko))) ts.

  (** Third, we ask whether [priority_inversion_bound (A - ε) ≠
      priority_inversion_bound A]. *)
  Definition priority_inversion_changes_at (A : duration) :=
    priority_inversion_bound (A - ε) != priority_inversion_bound A.

  (** The final search space for EDF is a set of offsets that are less
      than [L] and where [priority_inversion_bound], [task_rbf], or
      [bound_on_total_hep_workload] changes in value. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && (priority_inversion_changes_at A
                || task_rbf_changes_at A
                || bound_on_total_hep_workload_changes_at A).

  (** Let [R] be a value that upper-bounds the solution of each
      response-time recurrence, i.e., for any relative arrival time
      [A] in the search space, there exists a corresponding solution
      [F] such that [R >= F + (task cost - task lock-in service)]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum :
    forall (A : duration),
      is_in_search_space A ->
      exists (F : duration),
        A + F >= priority_inversion_bound A
                + (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk))
                + bound_on_total_hep_workload  A (A + F) /\
        R >= F + (task_cost tsk - task_rtct tsk).

  
  (** Finally, we define the interference bound function
      ([task_IBF]). [task_IBF] bounds the interference if tasks are
      sequential. Since tasks are sequential, we exclude interference
      from other jobs of the same task. For EDF, we define [task_IBF]
      as the sum of the priority interference bound and the
      higher-or-equal-priority workload. *)
  Let task_IBF (A R : duration) := priority_inversion_bound A + bound_on_total_hep_workload A R.

  (** ** Filling Out Hypothesis Of Abstract RTA Theorem *)
  (** In this section we prove that all hypotheses necessary to use
      the abstract theorem are satisfied. *)
  Section FillingOutHypothesesOfAbstractRTATheorem.

    (** First, we prove that [task_IBF] is indeed an interference bound. *)
    Section TaskInterferenceIsBoundedBytask_IBF.

      Section HepWorkloadBound.

        (** Consider an arbitrary job [j] of [tsk]. *)
        Variable j : Job.
        Hypothesis H_j_arrives : arrives_in arr_seq j.
        Hypothesis H_job_of_tsk : job_of_task tsk j.
        Hypothesis H_job_cost_positive: job_cost_positive j.

        (** Consider any busy interval <<[t1, t2)>> of job [j]. *)
        Variable t1 t2 : duration.
        Hypothesis H_busy_interval : definitions.busy_interval sched j t1 t2.

        (** Let's define A as a relative arrival time of job j (with respect to time t1). *)
        Let A := job_arrival j - t1.

        (** Consider an arbitrary shift Δ inside the busy interval ...  *)
        Variable Δ : duration.
        Hypothesis H_Δ_in_busy : t1 + Δ < t2.

        (** ... and the set of all arrivals between [t1] and [t1 + Δ]. *)
        Let jobs := arrivals_between arr_seq t1 (t1 + Δ).

        (** We define a predicate [EDF_from tsk]. Predicate [EDF_from
            tsk] holds true for any job [jo] of task [tsk] such that
            [job_deadline jo <= job_deadline j]. *)
        Let EDF_from (tsk : Task) := fun (jo : Job) => EDF jo j && (job_task jo == tsk).

        (** Now, consider the case where [A + ε + D tsk - D tsk_o ≤ Δ]. *)
        Section ShortenRange.

          (** Consider an arbitrary task [tsk_o ≠ tsk] from [ts]. *)
          Variable tsk_o : Task.
          Hypothesis H_tsko_in_ts: tsk_o \in ts.
          Hypothesis H_neq: tsk_o != tsk.

          (** And assume that [A + ε + D tsk - D tsk_o ≤ Δ]. *)
          Hypothesis H_Δ_ge : A + ε + D tsk - D tsk_o <= Δ.
          
          (** Then we prove that the total workload of jobs with
              higher-or-equal priority from task [tsk_o] over time
              interval [t1, t1 + Δ] is bounded by workload over time
              interval [t1, t1 + A + ε + D tsk - D tsk_o].  The
              intuition behind this inequality is that jobs which
              arrive after time instant [t1 + A + ε + D tsk - D tsk_o]
              have lower priority than job [j] due to the term [D tsk
              - D tsk_o]. *)
          Lemma total_workload_shorten_range:
            workload_of_jobs (EDF_from tsk_o) (arrivals_between arr_seq t1 (t1 + Δ))
            <= workload_of_jobs (EDF_from tsk_o) (arrivals_between arr_seq t1 (t1 + (A + ε + D tsk - D tsk_o))).
          Proof.
            have BOUNDED: t1 + (A + ε + D tsk - D tsk_o) <= t1 + Δ by lia.
            rewrite (workload_of_jobs_nil_tail _ _ BOUNDED) // => j' IN'.
            rewrite /EDF_from  => ARR'.
            case: (eqVneq (job_task j') tsk_o) => TSK';
              last by rewrite andbF.
            rewrite andbT; apply: contraT  => /negPn.
            rewrite /EDF/edf.EDF/job_deadline/job_deadline_from_task_deadline.
            move: H_job_of_tsk; rewrite TSK' /job_of_task => /eqP -> HEP.
            have LATEST: job_arrival j' <= t1 + A + D tsk - D tsk_o by rewrite /D/A; lia.
            have EARLIEST: t1 <= job_arrival j' by apply: job_arrival_between_ge.
            by case: (leqP (A + 1 + D tsk) (D tsk_o)); [rewrite /D/A|]; lia.
          Qed.

        End ShortenRange.

        (** Using the above lemma, we prove that the total workload of the
            tasks is at most [bound_on_total_hep_workload(A, Δ)]. *)
        Corollary sum_of_workloads_is_at_most_bound_on_total_hep_workload :
          \sum_(tsk_o <- ts | tsk_o != tsk) workload_of_jobs (EDF_from tsk_o) jobs
          <= bound_on_total_hep_workload A Δ.
        Proof.
          apply leq_sum_seq => tsko INtsko NEQT.
          edestruct (leqP Δ (A + ε + D tsk - D tsko)) as [NEQ|NEQ]; [ | apply ltnW in NEQ].
          - exact: (workload_le_rbf' arr_seq tsko).
          - eapply leq_trans; first by eapply total_workload_shorten_range; eauto 2.
            exact: workload_le_rbf'.
        Qed.

      End HepWorkloadBound.

      (** The above lemma, in turn, implies that [task_IBF] is a valid
          bound on the cumulative task interference. *)
      Corollary instantiated_task_interference_is_bounded :
        task_interference_is_bounded_by arr_seq sched tsk task_IBF.
      Proof.
        move => t1 t2 R2 j ARR TSK BUSY LT NCOMPL A OFF.
        move: (OFF _ _ BUSY) => EQA; subst A.
        move: (posnP (@job_cost _ Cost j)) => [ZERO|POS].
        - exfalso; move: NCOMPL => /negP COMPL; apply: COMPL.
          by rewrite /completed_by /completed_by ZERO.
        - rewrite -/(cumul_task_interference _ _ _ _ _).
          rewrite (leqRW (cumulative_task_interference_split _ _ _ _ _ _ _ _ _ _ _ _ _ )) //=.
          rewrite /I leq_add //; first exact: cumulative_priority_inversion_is_bounded.
          eapply leq_trans; first exact: cumulative_interference_is_bounded_by_total_service.
          eapply leq_trans; first exact: service_of_jobs_le_workload.
          eapply leq_trans.
          + eapply reorder_summation.
            move => j' IN _.
            apply H_all_jobs_from_taskset. eapply in_arrivals_implies_arrived. exact IN.
          + move : TSK => /eqP TSK.
            rewrite TSK.
            apply: sum_of_workloads_is_at_most_bound_on_total_hep_workload => //.
            by apply /eqP.
      Qed.

    End TaskInterferenceIsBoundedBytask_IBF.

    (** Finally, we show that there exists a solution for the response-time recurrence. *)
    Section SolutionOfResponseTimeReccurenceExists.

      (** To rule out pathological cases with the concrete search
          space, we assume that the task cost is positive and the
          arrival curve is non-pathological. *)
      Hypothesis H_task_cost_pos : 0 < task_cost tsk.
      Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

      (** Given any job [j] of task [tsk] that arrives exactly [A] units
          after the beginning of the busy interval, the bound of the
          total interference incurred by [j] within an interval of
          length [Δ] is equal to [task_rbf (A + ε) - task_cost tsk +
          task_IBF(A, Δ)]. *)
      Let total_interference_bound (A Δ : duration) :=
        task_rbf (A + ε) - task_cost tsk + task_IBF A Δ.

      (** Next, consider any [A] from the search space (in the abstract sense). *)
      Variable A : duration.
      Hypothesis H_A_is_in_abstract_search_space :
        search_space.is_in_search_space L total_interference_bound A.

      (** We prove that A is also in the concrete search space. *)
      Lemma A_is_in_concrete_search_space:
        is_in_search_space A.
      Proof.
        move: H_A_is_in_abstract_search_space => [-> | [/andP [POSA LTL] [x [LTx INSP2]]]]; apply/andP; split => //.
        { apply/orP; left; apply/orP; right.
          rewrite /task_rbf_changes_at /task_rbf /rbf task_rbf_0_zero // eq_sym -lt0n add0n.
          by apply task_rbf_epsilon_gt_0 => //.
        }
        { apply contraT; rewrite !negb_or => /andP [/andP [/negPn/eqP PI /negPn/eqP RBF]  WL].
          exfalso; apply INSP2.
          rewrite /total_interference_bound subnK // RBF.
          apply /eqP; rewrite eqn_add2l /task_IBF PI eqn_add2l.
          rewrite /bound_on_total_hep_workload subnK //.
          apply /eqP; rewrite big_seq_cond [RHS]big_seq_cond.
          apply eq_big => // tsk_i /andP [TS OTHER].
          move: WL; rewrite /bound_on_total_hep_workload_changes_at => /hasPn WL.
          move: {WL} (WL tsk_i TS) =>  /nandP [/negPn/eqP EQ|/negPn/eqP WL];
            first by move: OTHER; rewrite EQ => /neqP.
          case: (ltngtP (A + ε + D tsk - D tsk_i) x) => [ltn_x|gtn_x|eq_x]; rewrite /minn.
          { by rewrite ifT //; lia. }
          { rewrite ifF //.
            by move: gtn_x; rewrite leq_eqVlt  => /orP [/eqP EQ|LEQ]; lia. }
          { case: (A + D tsk - D tsk_i < x).
            - by rewrite WL.
            - by rewrite eq_x. } }
      Qed.

      (** Then, there exists solution for response-time recurrence (in the abstract sense). *)
      Corollary correct_search_space:
        exists F,
          A + F >= task_rbf (A + ε) - (task_cost tsk - task_rtct tsk) + task_IBF A (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).
      Proof.
        edestruct H_R_is_maximum as [F [FIX NEQ]]; first by apply A_is_in_concrete_search_space.
        exists F; split=> [|//].
        rewrite -{2}(leqRW FIX).
        by rewrite addnA [_ + priority_inversion_bound A]addnC -!addnA.
      Qed.

      End SolutionOfResponseTimeReccurenceExists.

  End FillingOutHypothesesOfAbstractRTATheorem.

  (** ** Final Theorem *)
  (** Based on the properties established above, we apply the abstract
      analysis framework to infer that [R] is a response-time bound for
      [tsk]. *)
  Theorem uniprocessor_response_time_bound_edf:
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => js ARRs TSKs.
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    eapply uniprocessor_response_time_bound_seq with
      (task_IBF := task_IBF) (L := L) => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - exact: EDF_implies_sequential_tasks.
    - exact: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - exact: instantiated_busy_intervals_are_bounded.
    - exact: instantiated_task_interference_is_bounded.
    - exact: correct_search_space.
  Qed.

End AbstractRTAforEDFwithArrivalCurves.
