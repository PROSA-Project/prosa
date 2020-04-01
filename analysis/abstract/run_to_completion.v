Require Export prosa.analysis.facts.model.service_of_jobs.
Require Export prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.
Require Export prosa.analysis.abstract.definitions.

(** * Run-to-Completion Threshold of a job *)
(** In this module, we provide a sufficient condition under which a job
    receives enough service to become non-preemptive. *)
(** Previously we defined the notion of run-to-completion threshold (see file
   abstract.run_to_completion_threshold.v). Run-to-completion threshold is the
   amount of service after which a job cannot be preempted until its completion.
   In this section we prove that if cumulative interference inside a busy interval
   is bounded by a certain constant then a job executes long enough to reach its
   run-to-completion threshold and become non-preemptive. *)
Section AbstractRTARunToCompletionThreshold.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume existence of a function
     mapping jobs to their preemption points. *)
  Context `{JobPreemptable Job}.

  (** Consider any kind of uni-service ideal processor state model. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.
  Hypothesis H_ideal_progress_proc_model : ideal_progress_proc_model PState.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** Consider any arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  
  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_jobs_respect_taskset_costs : arrivals_have_valid_job_costs arr_seq.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk : Task.

  (** Assume we are provided with abstract functions for interference and interfering workload. *)
  Variable interference : Job -> instant -> bool.
  Variable interfering_workload : Job -> instant -> duration.

  (** For simplicity, let's define some local names. *)
  Let work_conserving := work_conserving arr_seq sched tsk.
  Let cumul_interference := cumul_interference interference.
  Let cumul_interfering_workload := cumul_interfering_workload interfering_workload.
  Let busy_interval := busy_interval sched interference interfering_workload.

  (** We assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving: work_conserving interference interfering_workload.

  (** Let [j] be any job of task [tsk] with positive cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_task j = tsk.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Next, consider any busy interval <<[t1, t2)>> of job [j]. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval : busy_interval j t1 t2.

  (** First, we prove that job [j] completes by the end of the busy interval.
     Note that the busy interval contains the execution of job j, in addition
     time instant t2 is a quiet time. Thus by the definition of a quiet time
     the job should be completed before time t2. *)
  Lemma job_completes_within_busy_interval:
    completed_by sched j t2.
  Proof.
    move: (H_busy_interval) => [[/andP [_ LT] [_ _]] [_ QT2]].
    unfold pending, has_arrived in QT2.
    move: QT2; rewrite  /pending negb_and; move => /orP [QT2|QT2].
    { by move: QT2 => /negP QT2; exfalso; apply QT2, ltnW. }
      by rewrite Bool.negb_involutive in QT2.
  Qed.

  (** In this section we show that the cumulative interference is a complement to
     the total time where job [j] is scheduled inside the busy interval. *)
  Section InterferenceIsComplement.

    (** Consider any sub-interval <<[t, t + delta)>> inside the busy interval [t1, t2). *)
    Variables (t : instant) (delta : duration).
    Hypothesis H_greater_than_or_equal : t1 <= t.
    Hypothesis H_less_or_equal: t + delta <= t2.

    (** We prove that sum of cumulative service and cumulative interference
       in the interval <<[t, t + delta)>> is equal to delta. *)
    Lemma interference_is_complement_to_schedule:
      service_during sched j t (t + delta) + cumul_interference j t (t + delta) = delta.
    Proof.
      rewrite /service_during /cumul_interference/service_at.
      rewrite -big_split //=.
      rewrite -{2}(sum_of_ones t delta).
      rewrite big_nat [in RHS]big_nat.
      apply: eq_bigr=> x /andP[Lo Hi].
      move: (H_work_conserving j t1 t2 x) => Workj.
      feed_n 5 Workj; try done.
      { by apply/andP; split; eapply leq_trans; eauto 2. }
      destruct interference.
      - replace (service_in _ _) with 0; auto; symmetry.
        apply no_service_not_scheduled; auto.
        now apply/negP; intros SCHED; apply Workj in SCHED; apply SCHED.
      - replace (service_in _ _) with 1; auto; symmetry.
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        + apply H_unit_service_proc_model.
        + now apply H_ideal_progress_proc_model, Workj.
    Qed.

  End InterferenceIsComplement.

  (** In this section, we prove a sufficient condition under which job [j] receives enough service. *)
  Section InterferenceBoundedImpliesEnoughService.

    (** Let progress_of_job be the desired service of job j. *)
    Variable progress_of_job : duration.
    Hypothesis H_progress_le_job_cost : progress_of_job <= job_cost j.

    (** Assume that for some delta, the sum of desired progress and cumulative
       interference is bounded by delta (i.e., the supply). *)
    Variable delta : duration.
    Hypothesis H_total_workload_is_bounded:
      progress_of_job + cumul_interference j t1 (t1 + delta) <= delta.

    (** Then, it must be the case that the job has received no less service than progress_of_job. *)
    Theorem j_receives_at_least_run_to_completion_threshold:
      service sched j (t1 + delta) >= progress_of_job.
    Proof.
      case NEQ: (t1 + delta <= t2); last first.
      { intros.
        have L8 := job_completes_within_busy_interval.
        apply leq_trans with (job_cost j); first by done.
        rewrite /service.
        rewrite -(service_during_cat _ _ _ t2).
        apply leq_trans with (service_during sched j 0 t2); [by done | by rewrite leq_addr].
          by apply/andP; split; last (apply negbT in NEQ; apply ltnW; rewrite ltnNge).
      }
      {  move: H_total_workload_is_bounded => BOUND.
         apply subh3 in BOUND.
         apply leq_trans with (delta - cumul_interference j t1 (t1 + delta)); first by done.
         apply leq_trans with (service_during sched j t1 (t1 + delta)).
         { rewrite -{1}[delta](interference_is_complement_to_schedule t1) //.
           rewrite -addnBA // subnn addn0 //.
         }
         { rewrite /service -[X in _ <= X](service_during_cat _ _ _ t1).
           rewrite leq_addl //.
             by apply/andP; split; last rewrite leq_addr.
         }
      }
    Qed.

  End InterferenceBoundedImpliesEnoughService.

  (** In this section we prove a simple lemma about completion of
     a job after is reaches run-to-completion threshold. *)
  Section CompletionOfJobAfterRunToCompletionThreshold.

    (** Assume that completed jobs do not execute ... *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute sched.

    (** .. and the preemption model is valid. *)
    Hypothesis H_valid_preemption_model:
      valid_preemption_model arr_seq sched.

    (** Then, job [j] must complete in [job_cost j - job_run_to_completion_threshold j] time
       units after it reaches run-to-completion threshold. *)
    Lemma job_completes_after_reaching_run_to_completion_threshold:
      forall t,
        job_run_to_completion_threshold j <= service sched j t ->
        completed_by sched j (t + (job_cost j - job_run_to_completion_threshold j)).
    Proof.
      move => t ES.
      set (job_cost j - job_run_to_completion_threshold j) as job_last.
      have LSNP := @job_nonpreemptive_after_run_to_completion_threshold
                     Job H2 H3 _ _ arr_seq sched _ j _ t.
      apply negbNE; apply/negP; intros CONTR.
      have SCHED: forall t', t <= t' <= t + job_last -> scheduled_at sched j t'.
      { move => t' /andP [GE LT].
        rewrite -[t'](@subnKC t) //.
        eapply LSNP; eauto 2; first by rewrite leq_addr.
        rewrite subnKC //.
        apply/negP; intros COMPL.
        move: CONTR => /negP Temp; apply: Temp.
        apply completion_monotonic with (t0 := t'); try done.
      }
      have SERV: job_last + 1 <= \sum_(t <= t' < t + (job_last + 1)) service_at sched j t'.
      { rewrite -{1}[job_last + 1]addn0  -{2}(subnn t) addnBA // addnC.
        rewrite -{1}[_+_-_]addn0 -[_+_-_]mul1n -iter_addn -big_const_nat.
        rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
        rewrite leq_sum //.
        move => t' /andP [NEQ _].
        apply H_ideal_progress_proc_model; apply SCHED.
          by rewrite addn1 addnS ltnS in NEQ.
      }
      eapply service_at_most_cost with (j0 := j) (t0 := t + job_last.+1) in H_completed_jobs_dont_execute; auto.
      move: H_completed_jobs_dont_execute; rewrite leqNgt; move => /negP T; apply: T.
      rewrite /service -(service_during_cat _ _ _ t); last by (apply/andP; split; last rewrite leq_addr).
      apply leq_trans with (job_run_to_completion_threshold j + service_during sched j t (t + job_last.+1));
        last by rewrite leq_add2r.
      apply leq_trans with  (job_run_to_completion_threshold j + job_last.+1); last by rewrite leq_add2l /service_during -addn1.
        by rewrite addnS ltnS subnKC //; eapply job_run_to_completion_threshold_le_job_cost; eauto.
    Qed.

  End CompletionOfJobAfterRunToCompletionThreshold.

End AbstractRTARunToCompletionThreshold.
