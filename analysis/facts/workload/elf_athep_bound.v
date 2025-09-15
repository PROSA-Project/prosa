Require Export prosa.model.priority.elf.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.definitions.workload.bounded.
Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.definitions.workload.elf_athep_bound.
Require Export prosa.analysis.facts.model.rbf.

(** * Bound on Higher-or-Equal Priority Workload under ELF Scheduling is Valid *)

(** In this file, we prove that the upper bound on interference
    incurred by a job from jobs with higher-or-equal priority that
    come from other tasks under ELF scheduling (defined in
    [prosa.analysis.definitions.workload.elf_athep_bound]) is
    valid. *)
Section ATHEPWorkloadBoundIsValidForELF.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], a relative deadline [task_deadline], an arrival
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
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

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

  (* Consider any fixed-priority scheduling policy. *)
  Context (FP : FP_policy Task).

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

    (** Consider an arbitrary shift [delta] inside the busy interval ...  *)
    Variable delta : duration.
    Hypothesis H_delta_in_busy : t1 + delta < t2.

    (** ... and the set of all arrivals between [t1] and [t1 + delta]. *)
    Let jobs := arrivals_between arr_seq t1 (t1 + delta).

    (** Now, we define a predicate to identify jobs from a given task that have
        priority higher than or equal to [j]. *)
    Let hep_job_from_tsk (tsk_o : Task) (jo : Job) := hep_job jo j && (job_task jo == tsk_o).

    Section ShortenRange.

      (** Consider an arbitrary task [tsk_o ≠ tsk] from [ts]. *)
      Variable tsk_o : Task.
      Hypothesis H_tsko_in_ts : tsk_o \in ts.
      Hypothesis H_neq : tsk_o != tsk.

      (** And assume that [ep_task_interfering_interval_length tsk tsk_o A] is bounded by delta. *)
      Hypothesis H_delta_ge : ((ep_task_interfering_interval_length tsk tsk_o A) <= delta%:R)%R.

      (** Then we prove that the total workload of jobs with higher-or-equal priority
          from task [tsk_o] over the interval [[t1, t1 + Δ]] is bounded by the workload
          over the interval [[t1, t1 + ep_task_interfering_interval_length tsk tsk_o A]].
          The intuition behind this inequality is that jobs that arrive after time instant
          [t1 + ep_task_interfering_interval_length tsk tsk_o A] have lower priority
          than job [j]. *)
      Lemma total_ep_tsk_workload_shorten_range :
        ep_task tsk tsk_o ->
        workload_of_jobs (hep_job_from_tsk tsk_o) (arrivals_between arr_seq t1 (t1 + delta))
        <= workload_of_jobs (hep_job_from_tsk tsk_o)
          (arrivals_between arr_seq t1 `|Num.max 0%R (t1%:R + ep_task_interfering_interval_length tsk tsk_o A)%R|).
        Proof.
          move => EP_tsk.
          have BOUNDED: `|Num.max 0%R (t1%:R + (ep_task_interfering_interval_length tsk tsk_o A))%R| <= t1 + delta
            by clear - H_delta_ge; lia.
          rewrite /hep_job_from_tsk /hep_job /ELF.
          rewrite (workload_of_jobs_nil_tail _ _ BOUNDED) //.
          move => j' IN' ARR'.
          apply /contraT => /negPn /andP [/orP [/negP+ | /andP [_ HEP]] /eqP TSKo].
          { rewrite /ep_task in EP_tsk.
            rewrite /hp_task TSKo.
            move: H_job_of_tsk.
            rewrite /job_of_task => /eqP ->.
            by move: EP_tsk => /andP [-> ->]. }
          move: ARR'; rewrite /ep_task_interfering_interval_length -TSKo.
          move: H_job_of_tsk => /eqP <-.
          move: HEP; rewrite /hep_job /GEL /job_priority_point.
          by clear; lia.
        Qed.

    End ShortenRange.

    (** Consider the jobs that have priority higher than or equal to [j] released
        by any task in the same priority band as [tsk] (excluding [tsk]).

        We prove that the workload of these jobs is at most [bound_on_ep_task_workload]. *)
    Corollary sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload :
      \sum_(tsk_o <- ts |  (ep_task tsk tsk_o) && (tsk_o != tsk)) workload_of_jobs (hep_job_from_tsk tsk_o) jobs
      <= bound_on_ep_task_workload ts tsk A delta.
    Proof.
      rewrite /bound_on_ep_task_workload.
      apply leq_sum_seq => tsk_o INtsko /andP [EP_tsk NEQT].
      have [LEQ|GT] := leqP delta `|Num.max 0%R (ep_task_interfering_interval_length tsk tsk_o A)%R|; [| apply ltnW in GT].
      { apply: leq_trans; last by apply rbf_spec with (t := t1).
        by apply: workload_of_jobs_weaken => ? /andP[]. }
      { eapply leq_trans; first by apply total_ep_tsk_workload_shorten_range => //; clear - GT H_delta_in_busy; lia.
        rewrite (workload_of_jobs_equiv_pred _ _ (fun jo : Job => hep_job jo j && (job_task jo == tsk_o))) => //.
        { case: (boolP (0 <= ep_task_interfering_interval_length tsk tsk_o A)%R) => EQ;
              last by rewrite arrivals_between_geq; [rewrite workload_of_jobs0 | clear - EQ; lia].
          have -> : `|Num.max 0%R (t1%:R + ep_task_interfering_interval_length tsk tsk_o A)%R|
                     = t1 + `|Num.max 0%R (ep_task_interfering_interval_length tsk tsk_o A)| by clear -EQ; lia.
          by apply: rbf_spec' => // ? /andP[].
        }
      }
    Qed.

    (** Next, consider a workload of all jobs with priority higher
        than [j] released by any task in higher priority band.

        we establish that this workload is at most [bound_on_hp_task_workload]. *)
    Corollary sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload :
      \sum_(tsk_o <- ts |  hp_task tsk_o tsk) workload_of_jobs (hep_job_from_tsk tsk_o) jobs
      <= bound_on_hp_task_workload ts tsk delta.
    Proof.
      rewrite /bound_on_hp_task_workload.
      rewrite /total_hp_request_bound_function_FP.
      apply leq_sum_seq => tsk' IN' HP_TSK.
      by apply: rbf_spec' => // ? /andP[].
    Qed.

    (** To help with further analysis, we establish a useful lemma on partitioning
        higher-or-equal priority workloads. *)
    Lemma sum_of_hep_workloads_partitioned :
      \sum_(tsk_o <- ts | tsk_o != tsk) workload_of_jobs (hep_job_from_tsk tsk_o) jobs
      = \sum_(tsk_o <- ts |  (ep_task tsk tsk_o) && (tsk_o != tsk)) workload_of_jobs (hep_job_from_tsk tsk_o) jobs
        + \sum_(tsk_o <- ts |  hp_task tsk_o tsk) workload_of_jobs (hep_job_from_tsk tsk_o) jobs.
    Proof.
      rewrite (bigID (fun (tsk_o : Task) => hep_task tsk_o tsk)) //=.
      rewrite (bigID (fun (tsk_o : Task) => hep_task tsk tsk_o)) //=.
      under eq_bigl.
      { move => tsk'.
        rewrite -andbA andbC.
        rewrite (@andbC (hep_task tsk' tsk) (hep_task tsk tsk')).
        over. }
      have ->:  \sum_(i <- ts | (i != tsk) && ~~ hep_task i tsk)
        workload_of_jobs (hep_job_from_tsk i) jobs = 0.
      { under eq_bigr.
        { move => tsk' /andP [NEQ HEP].
          rewrite /workload_of_jobs.
          under big_pred0.
          { move=> j'.
            rewrite /hep_job_from_tsk /hep_job /ELF /hp_task.
            elim Tsk_j' : (job_task j' == tsk'); last by rewrite andbF.
            move: Tsk_j' => /eqP ->.
            move: H_job_of_tsk.
            rewrite /job_of_task => /eqP ->.
            by move: HEP => /negbTE ->. }
          over. }
        apply /eqP.
        by rewrite big_const_idem.
      }
      rewrite addn0 /ep_task.
      apply /eqP.
      rewrite eqn_add2l /hp_task.
      rewrite (eq_bigl (fun (tsk_o : Task) => hep_task tsk_o tsk && ~~ hep_task tsk tsk_o)) //=.
      rewrite /eqfun => tsk'.
      elim NEQ: (tsk' != tsk) => //=.
      move: NEQ => /idP /idP /eqP NEQ.
      rewrite NEQ.
      by rewrite andbN.
  Qed.

  (** Finally, we establish that the workload of jobs with priority higher than or equal to
      [j] is at most [bound_on_athep_workload]. *)
  Corollary sum_of_workloads_is_at_most_bound_on_total_hep_workload :
    \sum_(tsk_o <- ts | tsk_o != tsk) workload_of_jobs (hep_job_from_tsk tsk_o) jobs
    <= bound_on_athep_workload ts tsk A delta.
  Proof.
    rewrite sum_of_hep_workloads_partitioned.
    rewrite /bound_on_athep_workload.
    move: sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload => LT_HP.
    move: sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload => LT_EP.
    by lia.
  Qed.

  End HepWorkloadBound.

  (** The validity of [bound_on_athep_workload] then easily follows
      from lemma [sum_of_workloads_is_at_most_bound_on_total_hep_workload]. *)
  Corollary bound_on_athep_workload_is_valid :
    athep_workload_is_bounded arr_seq sched tsk (bound_on_athep_workload ts tsk).
  Proof.
    move=> j t1 delta POS TSK QT.
    eapply leq_trans.
    + eapply reorder_summation => j' IN _.
      by apply H_all_jobs_from_taskset; eapply in_arrivals_implies_arrived; exact IN.
    + move : TSK => /eqP TSK; rewrite TSK.
      by apply: sum_of_workloads_is_at_most_bound_on_total_hep_workload => //; apply /eqP.
  Qed.

End ATHEPWorkloadBoundIsValidForELF.
