From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Import prosa.model.readiness.basic.
Require Import prosa.model.priority.fifo.
Require Import prosa.analysis.facts.priority.fifo.
Require Import prosa.analysis.abstract.ideal_jlfp_rta.
Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Export prosa.analysis.facts.busy_interval.ideal.inequalities.

(** * Abstract RTA for FIFO-schedulers *)
(** In this module we instantiate the Abstract Response-Time analysis
    (aRTA) to FIFO schedulers for real-time tasks with arbitrary arrival models
     assuming an ideal uni-processor model. *)

(** Given the FIFO priority policy and an ideal uni-processor scheduler
    model, we can explicitly specify [interference],
    [interfering_workload], and [interference_bound_function]. In this
    settings, we can define natural notions of service, workload, busy
    interval, etc. *)

Section AbstractRTAforFIFOwithArrivalCurves.

  (** Consider any type of tasks, each characterized by a WCET, a relative
      deadline, and a run-to-completion threshold, ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks, where each
       each job has an arrival time, a cost, and a preemption-point predicate. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context {Arrival : JobArrival Job}.
  Context {Cost : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** Next, consider any valid ideal uni-processor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Note that we differentiate between abstract and
      classical notions of work-conserving schedules. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is a work-conserving schedule
      in the _classical_ sense, and later prove that the hypothesis
      about abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** Assume that a job's cost cannot be larger than its task's WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in [ts]
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) a monotonic function
     that equals 0 for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtct tsk] is (1) no larger than [tsk]'s cost, (2) for
      any job of task [tsk], [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold : valid_task_run_to_completion_threshold arr_seq tsk.

  (** We also assume that the schedule respects the policy defined by the preemption model. *)
  Hypothesis H_respects_policy_at_preemption_point : respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).

  (** We introduce [rbf] as an abbreviation of the task request bound function,
      which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a given task [T]. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [task_rbf] as an abbreviation
      of the task request bound function of task [tsk]. *)
   Let task_rbf := rbf tsk.

  (** For simplicity, let's define some local names. *)
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.
  Let number_of_task_arrivals := number_of_task_arrivals arr_seq.

  (** Let L be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_request_bound_function ts L.

  (** To reduce the time complexity of the analysis, we introduce the notion of search space for FIFO.
      Intuitively, this corresponds to all "interesting" arrival offsets that the job under
      analysis might have with regard to the beginning of its busy-window. *)

  (** In the case of FIFO, the final search space is the set of offsets less than [L]
      such that there exists a task [tsko] from [ts] such that [rbf tsko (A) ≠ rbf tsko (A + ε)]. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && has (fun tsko => rbf tsko (A) != rbf tsko ( A + ε )) ts.

  (** Let [R] be a value that upper-bounds the solution of each
      response-time equation, i.e., for any relative arrival time [A]
      in the search space, there exists a corresponding solution [F]
      such that [R >= F]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum:
    forall (A : duration),
      is_in_search_space A ->
      exists (F : nat),
        A + F >= \sum_(tsko <- ts) rbf tsko (A + ε) /\
        F <= R.

  (** To use the theorem [uniprocessor_response_time_bound] from the Abstract RTA module,
      we need to specify functions that concretely define the abstract concepts
      interference, interfering workload, and [IBF]. *)

  (** ** Instantiation of Interference *)
  (** We say that job [j] incurs interference at time [t] iff it cannot execute due to
     a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
  Let interference (j : Job) (t : instant) := ideal_jlfp_rta.interference arr_seq sched j t.

  (** ** Instantiation of Interfering Workload *)
  (** The interfering workload, in turn, is defined as the sum of the priority inversion
      function and interfering workload of jobs with higher or equal priority. *)
  Let interfering_workload (j : Job) (t : instant) := ideal_jlfp_rta.interfering_workload arr_seq sched j t.

  (** Finally, we define the interference bound function ([IBF]). [IBF] bounds the cumulative
      interference incurred by a job. For FIFO, we define [IBF] as the sum of [RBF] for all tasks
      in the interval [A + ε] minus the WCET of [tsk]. *)
  Let IBF tsk (A R : duration) := (\sum_(tsko <- ts) rbf tsko (A + ε)) - task_cost tsk.

  (** ** Filling Out Hypotheses Of Abstract RTA Theorem *)
  (** In this section we prove that all hypotheses necessary to use the abstract theorem are satisfied. *)
  Section FillingOutHypothesesOfAbstractRTATheorem.

    (** In this section, we prove that, under FIFO scheduling, the cumulative priority inversion experienced
        by a job [j] in any interval within its busy window is always [0]. We later use this fact to prove the bound on
        the cumulative interference. *)
    Section PriorityInversion.

      (** Consider any job [j] of the task under consideration [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.

      (** Assume that the job has a positive cost. *)
      Hypothesis H_job_cost_positive: job_cost_positive j.

      (** Assume the busy interval of the job is given by <<[t1,t2)>>. *)
      Variable t1 t2 : duration.
      Hypothesis H_busy_interval :
        definitions.busy_interval sched interference interfering_workload j t1 t2.

      (** Consider any interval <<[t1,t1 + Δ)>> in the busy interval of [j]. *)
      Variable Δ : duration.
      Hypothesis H_Δ_in_busy : t1 + Δ < t2.

      (** We prove that the cumulative priority inversion in the interval
          <<[t1, t1 + Δ)>> is [0]. *)
      Lemma no_priority_inversion :
        cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) = 0.
      Proof.
        apply /eqP; rewrite -leqn0.
        pose zf : nat -> nat := (fun=> 0).
        have: cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) <= zf (job_arrival j - t1);
          last by apply.
        apply: cumulative_priority_inversion_is_bounded; rt_eauto.
        have -> : priority_inversion_is_bounded_by arr_seq sched tsk zf
                 = priority_inversion_is_bounded_by_constant arr_seq sched tsk 0;
          by try apply: FIFO_implies_no_pi; rt_eauto.
      Qed.

    End PriorityInversion.

    (** Using the above lemma, we prove that IBF is indeed an interference bound. *)
    Lemma instantiated_interference_is_bounded :
      job_interference_is_bounded_by arr_seq sched tsk interference interfering_workload  IBF.
    Proof.
      move => t1 t2 Δ j ARRj TSKj BUSY IN_BUSY NCOMPL.
      rewrite /cumul_interference cumulative_interference_split; rt_eauto.
      have JPOS: job_cost_positive j by rewrite -ltnNge in NCOMPL; unfold job_cost_positive; lia.
      move: (BUSY) => [ [ /andP [LE GT] [QUIETt1 _ ] ] [QUIETt2 EQNs]].
      have CPIB := no_priority_inversion j ARRj TSKj _ t1 t2.
      rewrite /cumulative_priority_inversion in CPIB; rewrite /ideal_jlfp_rta.cumulative_priority_inversion CPIB //= add0n.
      rewrite (cumulative_i_ohep_eq_service_of_ohep arr_seq) //=;
              try by (try rewrite instantiated_quiet_time_equivalent_quiet_time); rt_eauto.
      eapply leq_trans; first by apply service_of_jobs_le_workload; rt_eauto.
      rewrite (leqRW (workload_equal_subset _ _ _ _ _ _  _)); rt_eauto.
      specialize (workload_minus_job_cost j) => ->.
      { rewrite /workload_of_jobs /IBF (big_rem tsk) //= (addnC (rbf tsk (job_arrival j - t1 + ε))).
        rewrite -addnBA; last first.
        { apply leq_trans with (task_rbf ε).
          ( try ( apply (task_rbf_1_ge_task_cost arr_seq) with (j0 := j) => //= ) ||
          apply (task_rbf_1_ge_task_cost arr_seq) with (j := j) => //=); first by auto.
          by apply task_rbf_monotone; [apply H_valid_arrival_curve | lia]. }
        eapply leq_trans; last first.
        by erewrite leq_add2l; eapply task_rbf_excl_tsk_bounds_task_workload_excl_j; eauto 1.
        rewrite addnBA.
        { rewrite leq_sub2r //; eapply leq_trans.
          - apply sum_over_partitions_le => j' inJOBS.
            by apply H_all_jobs_from_taskset, (in_arrivals_implies_arrived _ _ _ _ inJOBS).
          - rewrite (big_rem tsk) //= addnC leq_add //; last by rewrite subnKC.
            rewrite big_seq_cond [in X in _ <= X]big_seq_cond big_mkcond [in X in _ <= X]big_mkcond //=.
            apply leq_sum => tsk' _; rewrite andbC //=.
            destruct (tsk' \in rem (T:=Task) tsk ts) eqn:IN; last by [].
            apply rem_in in IN.
            eapply leq_trans; last first.
            + by apply (task_workload_le_task_rbf _ _ _ IN H_valid_job_cost H_is_arrival_curve t1).
            + by rewrite addnBAC //= subnKC //= addn1; apply leqW. }
        rewrite /task_workload_between /task_workload /workload_of_jobs (big_rem j) //=.
        - by rewrite TSKj; apply leq_addr.
        - by apply job_in_arrivals_between => //; apply /andP; split; [| rewrite subnKC; [rewrite addn1 |]].  }
      apply: arrivals_uniq => //.
      apply: job_in_arrivals_between => //.
      by apply /andP; split; [ | rewrite addn1].
    Qed.

    (** Finally, we show that there exists a solution for the response-time equation. *)
    Section SolutionOfResponseTimeReccurenceExists.

      (** Consider any job j of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_positive_cost : 0 < task_cost tsk.

      (** Next, consider any [A] from the search space (in the abstract sense). *)
      Variable A : nat.
      Hypothesis H_A_is_in_abstract_search_space:
        search_space.is_in_search_space tsk L IBF A.

      (** We prove that [A] is also in the concrete search space. In other words,
          we prove that the abstract search space is a subset of the concrete search space. *)
      Lemma A_is_in_concrete_search_space:
        is_in_search_space A.
      Proof.
        move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
        unfold is_in_search_space.
        { subst A.
          apply/andP; split; [by done |].
          apply /hasP. exists tsk; first by done.
          rewrite neq_ltn;apply/orP; left.
          rewrite /task_rbf /rbf; erewrite task_rbf_0_zero; eauto 2.
          rewrite add0n /task_rbf; apply leq_trans with (task_cost tsk).
          - by eapply leq_trans; eauto 2.
          - by eapply task_rbf_1_ge_task_cost; eauto. }
        { apply /andP; split; first by done.
          apply /hasPn.
          move => EQ2. unfold IBF in INSP2.
          rewrite subnK in INSP2; try by done.
          apply INSP2; clear INSP2.
          have -> : \sum_(tsko <- ts) rbf tsko A = \sum_(tsko <- ts) rbf tsko (A + ε); last by done.
          apply eq_big_seq => //= task IN.
          by move: (EQ2 task IN) => /negPn /eqP. }
      Qed.

      (** Then, there exists a solution for the response-time recurrence (in the abstract sense). *)
      Corollary exists_solution_for_abstract_response_time_recurrence:
        exists (F : nat),
          A + F >= task_rtct tsk + IBF tsk A (A + F) /\
          F + (task_cost tsk - task_rtct tsk) <= R.
      Proof.
        move : H_R_is_maximum => ABC.
        move: (H_valid_arrival_curve _ H_tsk_in_ts) => VARR.
        move: (H_is_arrival_curve _ H_tsk_in_ts) => RESP.
        move : H_job_of_tsk => /eqP EQj.
        specialize (ABC 0); feed ABC.
        { apply /andP; split;  [by done| apply /hasP; exists tsk; first by done].
          rewrite /task_rbf /rbf task_rbf_0_zero //= (add0n ε) neq_ltn.
          apply /orP; left.
          by apply (task_rbf_epsilon_gt_0 arr_seq H_arrival_times_are_consistent tsk RESP  j). }
        move : ABC => [F [LE1 LE2]].
        edestruct H_R_is_maximum as [F' [FIX NEQ]]; first by apply A_is_in_concrete_search_space.
        exists (R - (task_cost tsk - task_rtct tsk)); split.
        { unfold IBF.
          rewrite (leqRW FIX) addnC -subnA; first last.
          - rewrite -(leqRW FIX).
            apply (task_cost_le_sum_rbf _ H_arrival_times_are_consistent _ VARR RESP j) => //.
            by rewrite addn1.
          - destruct H_valid_run_to_completion_threshold as [TASKvalid JOBvalid].
            by apply TASKvalid.
          - rewrite addnBA; first by rewrite leq_sub2r // leq_add2l.
            have GE: task_cost tsk <= R; last by lia.
            rewrite !add0n in LE1.
            rewrite -(leqRW LE2) -(leqRW LE1).
            by eapply (task_cost_le_sum_rbf arr_seq); rt_eauto. }
        { rewrite subnK; first by done.
          rewrite !add0n in LE1. apply leq_trans with F; last by done.
          apply leq_trans with (\sum_(tsko <- ts) rbf tsko ε); last by done.
          apply leq_trans with (task_cost tsk); first by lia.
          eapply task_cost_le_sum_rbf; rt_eauto. }
      Qed.

    End SolutionOfResponseTimeReccurenceExists.

  End FillingOutHypothesesOfAbstractRTATheorem.

  (** ** Final Theorem *)
  (** Based on the properties established above, we apply the abstract analysis
      framework to infer that [R] is a response-time bound for [tsk]. *)
  Theorem uniprocessor_response_time_bound_FIFO:
    response_time_bounded_by tsk R.
  Proof.
    intros js ARRs TSKs.
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    ( try ( eapply uniprocessor_response_time_bound with
      (interference0 := interference) (interfering_workload0 := interfering_workload)
      (interference_bound_function := fun tsk A R => IBF tsk A R) (L0 := L) ) ||
    eapply uniprocessor_response_time_bound with
      (interference := interference) (interfering_workload := interfering_workload)
      (interference_bound_function := fun tsk A R => IBF tsk A R) (L := L)); rt_eauto.
    - by eapply instantiated_i_and_w_are_coherent_with_schedule; rt_eauto.
    - by eapply instantiated_busy_intervals_are_bounded; rt_eauto.
    - by apply instantiated_interference_is_bounded.
    - eapply (exists_solution_for_abstract_response_time_recurrence js) => //=.
      apply leq_trans with (job_cost js) => //.
      move: TSKs; rewrite /job_of_task => /eqP <-.
      by eapply H_valid_job_cost.
  Qed.

End AbstractRTAforFIFOwithArrivalCurves.
