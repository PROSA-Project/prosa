Require Export prosa.model.priority.edf.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.definitions.workload.bounded.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.definitions.workload.edf_athep_bound.

(** * Bound on Higher-or-Equal Priority Workload under EDF Scheduling is Valid *)

(** In this file, we prove that the upper bound on interference
    incurred by a job from jobs with higher-or-equal priority that
    come from other tasks under EDF scheduling (defined in
    [prosa.analysis.definitions.workload.edf_athep_bound]) is
    valid. *)
Section ATHEPWorkloadBoundIsValidForEDF.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], a relative deadline [task_deadline], and an arrival
      curve [max_arrivals], ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{MaxArrivals Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], and an arrival
      time [job_arrival]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** For brevity, let's denote the relative deadline of a task as [D]. *)
  Let D tsk := task_deadline tsk.

  (** Consider any valid arrival sequence [arr_seq] ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... with valid job costs. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** We consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrival tsk] is an arrival bound of
      [tsk]. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Before we prove the main result, we establish some auxiliary lemmas. *)
  Section HepWorkloadBound.

    (** Consider an arbitrary job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Consider the busy interval <<[t1, t2)>> of job [j]. *)
    Variable t1 t2 : duration.
    Hypothesis H_busy_interval : busy_interval arr_seq sched j t1 t2.

    (** Let's define [A] as a relative arrival time of job [j] (with
        respect to time [t1]). *)
    Let A := job_arrival j - t1.

    (** Consider an arbitrary shift [Δ] inside the busy interval ...  *)
    Variable Δ : duration.
    Hypothesis H_Δ_in_busy : t1 + Δ < t2.

    (** ... and the set of all arrivals between [t1] and [t1 + Δ]. *)
    Let jobs := arrivals_between arr_seq t1 (t1 + Δ).

    (** We define a predicate [EDF_from tsk]. Predicate [EDF_from tsk]
        holds true for any job [jo] of task [tsk] such that
        [job_deadline jo <= job_deadline j]. *)
    Let EDF_from (tsk : Task) (jo : Job) := EDF Job jo j && (job_task jo == tsk).

    (** Now, consider the case where [A + ε + D tsk - D tsk_o ≤ Δ]. *)
    Section ShortenRange.

      (** Consider an arbitrary task [tsk_o ≠ tsk] from [ts]. *)
      Variable tsk_o : Task.
      Hypothesis H_tsko_in_ts : tsk_o \in ts.
      Hypothesis H_neq : tsk_o != tsk.

      (** And assume that [A + ε + D tsk - D tsk_o ≤ Δ]. *)
      Hypothesis H_Δ_ge : A + ε + D tsk - D tsk_o <= Δ.

      (** Then we prove that the total workload of jobs with
          higher-or-equal priority from task [tsk_o] over the interval
          [[t1, t1 + Δ]] is bounded by workload over the interval
          [[t1, t1 + A + ε + D tsk - D tsk_o]]. The intuition behind
          this inequality is that jobs that arrive after time instant
          [t1 + A + ε + D tsk - D tsk_o] have lower priority than job
          [j] due to the term [D tsk - D tsk_o]. *)
      Lemma total_workload_shorten_range :
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
      <= bound_on_athep_workload ts tsk A Δ.
    Proof.
      apply: leq_sum_seq => tsko INtsko NEQT; fold (D tsk) (D tsko).
      have [LEQ|LT] := leqP Δ (A + ε + D tsk - D tsko);
        last (apply: leq_trans; first by apply: total_workload_shorten_range).
      all: by apply: rbf_spec' => // ? /andP[].
    Qed.

  End HepWorkloadBound.

  (** The validity of [bound_on_athep_workload] then easily follows
      from lemma [sum_of_workloads_is_at_most_bound_on_total_hep_workload]. *)
  Corollary bound_on_athep_workload_is_valid :
    athep_workload_is_bounded arr_seq sched tsk (bound_on_athep_workload ts tsk).
  Proof.
    move=> j t1 Δ POS TSK QT.
    eapply leq_trans.
    + eapply reorder_summation => j' IN _.
      by apply H_all_jobs_from_taskset; eapply in_arrivals_implies_arrived; exact IN.
    + move : TSK => /eqP TSK; rewrite TSK.
      by apply: sum_of_workloads_is_at_most_bound_on_total_hep_workload => //; apply /eqP.
  Qed.

End ATHEPWorkloadBoundIsValidForEDF.
