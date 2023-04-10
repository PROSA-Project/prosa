Require Export analysis.abstract.ideal.iw_instantiation.

(** In this file, we prove some inequalities that always
    hold inside the busy interval of a job. Throughout this file we
    assume the ideal uniprocessor model. *)
Section BusyIntervalInequalities.

  (** Consider any kind of tasks and their jobs, each characterized by
      an arrival time, a cost, and an arbitrary notion of readiness. *)
  Context {Task : TaskType} {Job : JobType} `{JobTask Job Task}.
  Context `{JobArrival Job} `{JobCost Job} {JR :JobReady Job (ideal.processor_state Job)}.

  (** Consider a JLFP policy that is reflexive and respects sequential tasks. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_policy_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_policy_respecsts_sequential_tasks : policy_respects_sequential_tasks JLFP.

  (** Consider a consistent arrival sequence that does not contain duplicates. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Consider any valid ideal uniprocessor schedule defined over this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched  arr_seq.

  (** Consider a set of tasks [ts] that contains all the jobs in the
      arrival sequence. *)
  Variable ts : list Task.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Consider a task [tsk]. *)
  Variable tsk : Task.

  (** Consider a job [j] of the task [tsk] that has a positive job cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_of_task tsk j.
  Hypothesis H_job_cost_positive: job_cost_positive j.
  
  (** Consider the ideal JLFP definitions of interference and
      interfering workload. *)
  #[local] Instance ideal_jlfp_interference : Interference Job :=
    ideal_jlfp_interference arr_seq sched.

  #[local] Instance ideal_jlfp_interfering_workload : InterferingWorkload Job :=
    ideal_jlfp_interfering_workload arr_seq sched.

  (** Consider the busy interval for j is given by <<[t1,t2)>>. *)
  Variable t1 t2 : duration.
  Hypothesis H_busy_interval : definitions.busy_interval sched j t1 t2.

  (** Let us denote the relative arrival time by [A]. *)
  Let A := job_arrival j - t1.

  (** Consider any arbitrary time [Δ] inside the busy interval. *)
  Variable  Δ : duration.
  Hypothesis H_Δ_in_busy : t1 + Δ < t2.

  (** First, we prove that if the priority inversion is bounded then,
      the cumulative priority inversion is also bounded. *)
  Section PIBound.

    (** Consider the priority inversion in any given interval
        is bounded by a constant. *)
    Variable priority_inversion_bound : duration -> duration.
    Hypothesis H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by arr_seq sched tsk priority_inversion_bound.

    (** Then, the cumulative priority inversion in any interval
        is also bounded. *)
    Lemma cumulative_priority_inversion_is_bounded:
      cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ)
      <= priority_inversion_bound (job_arrival j - t1).
    Proof.
      apply leq_trans with (cumulative_priority_inversion arr_seq sched j t1 t2).
      - rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1  + Δ)) //=; try by lia.
        by rewrite /priority_inversion leq_addr.
      - apply H_priority_inversion_is_bounded; try done.
        eapply instantiated_busy_interval_equivalent_busy_interval in H_busy_interval; rt_eauto.
        by move: H_busy_interval => [PREF _].
    Qed.

  End PIBound.

  (** Let [jobs] denote the arrivals in the interval [Δ]. *)
  Let jobs := arrivals_between arr_seq t1 (t1 + Δ).

  (** Next, we prove that the cumulative interference from higher priority
      jobs of other tasks in an interval is bounded by the total service
      received by the higher priority jobs of those tasks. *)
  Lemma cumulative_interference_is_bounded_by_total_service:
    cumulative_another_task_hep_job_interference arr_seq sched j t1 (t1 + Δ)
    <= service_of_jobs sched (fun jo => another_task_hep_job jo j) jobs t1 (t1 + Δ).
  Proof.
    move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
    erewrite cumulative_i_thep_eq_service_of_othep; rt_eauto.
    - move: (H_job_of_tsk) => /eqP TSK.
      by rewrite instantiated_quiet_time_equivalent_quiet_time; rt_eauto.
  Qed.

End BusyIntervalInequalities.
