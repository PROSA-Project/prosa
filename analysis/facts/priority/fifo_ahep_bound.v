Require Export prosa.analysis.facts.interference.
Require Export prosa.analysis.facts.model.restricted_supply.schedule.
Require Import prosa.analysis.facts.priority.fifo.
Require Import prosa.analysis.facts.model.rbf.


(** * Higher-or-Equal-Priority Interference Bound under FIFO *)

(** In this file, we introduce a bound on the cumulative interference
    from higher- and equal-priority under FIFO scheduling. *)
Section RTAforFullyPreemptiveFIFOModelwithArrivalCurves.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost] and an arrival curve [max_arrivals] ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], and an arrival
      time [job_arrival]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** Consider any kind of unit-supply uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.

  (** Consider any arrival sequence [arr_seq] with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** We further require that a job's cost cannot exceed its task's stated WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

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

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider any schedule ... *)
  Variable sched : schedule PState.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Next, we establish a bound on the interference produced by higher- and
      equal-priority jobs. *)

  (** Consider a job [j] of the task under analysis [tsk] with a positive cost. *)
  Variable j : Job.
  Hypothesis H_job_of_task : job_of_task tsk j.
  Hypothesis H_j_in_arrivals : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider the busy window of [j] and denote it as <<[t1, t2)>>. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_window : classical.busy_interval arr_seq sched j t1 t2.

  (** Consider any arbitrary sub-interval <<[t1, Δ)>> within the busy
      window of [j]. *)
  Variable Δ : instant.
  Hypothesis H_in_busy : t1 + Δ < t2.

  (** The cumulative interference from higher- and equal-priority jobs
      during <<[t1, Δ)>> is bounded as follows. *)
  Lemma bound_on_hep_workload :
    cumulative_another_hep_job_interference arr_seq sched j t1 (t1 + Δ) <=
      \sum_(tsko <- ts) task_request_bound_function tsko (job_arrival j - t1 + ε) - task_cost tsk.
  Proof.
    move: (H_busy_window) => [[_ [_ [_ /andP [ARR1 ARR2]]]] _].
    rewrite (cumulative_i_ohep_eq_service_of_ohep _ arr_seq) => //; last  eauto 6 with basic_rt_facts; last first.
    { by move: (H_busy_window) => [[_ [Q _]] _]. }
    eapply leq_trans; first by apply service_of_jobs_le_workload => //.
    rewrite (leqRW (workload_equal_subset _ _ _ _ _ _  _)) => //.
    rewrite (workload_minus_job_cost j)//;
            last by apply job_in_arrivals_between => //; last by rewrite addn1.
    rewrite /workload_of_jobs (big_rem tsk) //=
            (addnC (task_request_bound_function tsk (job_arrival j - t1 + ε))).
    rewrite -addnBA; last first.
    - apply leq_trans with (task_request_bound_function tsk ε).
      { by apply: task_rbf_1_ge_task_cost; exact: non_pathological_max_arrivals. }
      { by apply task_rbf_monotone; [apply H_valid_arrival_curve | lia]. }
    - eapply leq_trans; last first.
      { by erewrite leq_add2l; apply task_rbf_without_job_under_analysis; (try apply ARR1) => //; lia. }
      rewrite addnBA.
      + rewrite leq_sub2r //; eapply leq_trans.
        * apply sum_over_partitions_le => j' inJOBS => _.
          by apply H_all_jobs_from_taskset, (in_arrivals_implies_arrived _ _ _ _ inJOBS).
        * rewrite (big_rem tsk) //= addnC leq_add //; last by rewrite addnA subnKC.
          rewrite big_seq_cond [in X in _ <= X]big_seq_cond big_mkcond [in X in _ <= X]big_mkcond //=.
          apply leq_sum => tsk' _; rewrite andbC //=.
          destruct (tsk' \in rem (T:=Task) tsk ts) eqn:IN; last by [].
          apply rem_in in IN.
          rewrite addnBAC //=.
          apply: leq_trans; last by apply rbf_spec with (t := t1) (Δ := job_arrival j + 1 - t1).
          by rewrite subnKC //= addn1; apply leqW.
      + move : H_job_of_task => TSKj.
        rewrite /task_workload_between /task_workload /workload_of_jobs (big_rem j) //=;
                first by rewrite TSKj; apply leq_addr.
        apply job_in_arrivals_between => //.
        by lia.
  Qed.

End RTAforFullyPreemptiveFIFOModelwithArrivalCurves.
