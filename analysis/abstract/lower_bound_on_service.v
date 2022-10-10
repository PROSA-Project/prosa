Require Export prosa.analysis.facts.model.service_of_jobs.
Require Export prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.
Require Export prosa.analysis.abstract.definitions.
Require Export prosa.analysis.abstract.busy_interval.

(** * Lower Bound On Job Service *)
(** In this section we prove that if the cumulative interference
    inside a busy interval is bounded by a certain constant then a job
    executes long enough to reach a specified amount of service. *)
Section LowerBoundOnService.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume existence of a function mapping jobs to
      their preemption points. *)
  Context `{JobPreemptable Job}.

  (** Consider _any_ kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_jobs_respect_taskset_costs : arrivals_have_valid_job_costs arr_seq.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk : Task.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** We assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Let [j] be any job of task [tsk] with positive cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_of_task tsk j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** In this section, we show that the cumulative interference is a
      complement to the total time where job [j] is scheduled inside a
      busy interval prefix. *)
  Section InterferenceIsComplement.

    (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_interval : busy_interval_prefix sched j t1 t2.

    (** Consider any sub-interval <<[t, t + δ)>> inside the busy interval <<[t1, t2)>>. *)
    Variables (t : instant) (δ : duration).
    Hypothesis H_t1_le_t : t1 <= t.
    Hypothesis H_tδ_le_t2 : t + δ <= t2.

    (** We prove that sum of cumulative service and cumulative
        interference in the interval <<[t, t + δ)>> is equal to
        [δ]. *)
    Lemma interference_is_complement_to_schedule :
      service_during sched j t (t + δ) + cumulative_interference j t (t + δ) >= δ.
    Proof.
      rewrite /service_during /cumulative_interference /service_at.
      rewrite -big_split //= -{1}(sum_of_ones t δ) big_nat [in X in _ <= X]big_nat leq_sum // => x /andP[Lo Hi].
      move: (H_work_conserving j t1 t2 x) => Workj.
      feed_n 4 Workj; rt_eauto.
      { by apply/andP; split; eapply leq_trans; rt_eauto. }
      destruct interference; first by lia.
      by rewrite // addn0; apply Workj.
    Qed.
    
    (** Also, note that under the unit-service processor model
        assumption, the sum of service within the interval <<[t, t + δ)>> 
        and the cumulative interference within the same interval
        is bounded by the length of the interval (i.e., [δ]).  *) 
    Remark service_and_interference_bounded :
      unit_service_proc_model PState ->
      service_during sched j t (t + δ) + cumulative_interference j t (t + δ) <= δ.
    Proof.
      move => UNIT.
      rewrite /service_during /cumulative_interference/service_at -big_split //=.
      rewrite -{2}(sum_of_ones t δ).
      rewrite big_nat [in X in _ <= X]big_nat; apply leq_sum => x /andP[Lo Hi].
      move: (H_work_conserving j t1 t2 x) => Workj.
      feed_n 4 Workj; try done.
      { by apply/andP; split; lia. }
      destruct interference.
      - rewrite addn1 ltnS.
        by move_neq_up NE; apply Workj.
      - by rewrite addn0; apply UNIT.
    Qed.
    
  End InterferenceIsComplement.

  (** In this section, we prove a sufficient condition under which job
      [j] receives enough service. *)
  Section InterferenceBoundedImpliesEnoughService.

    (** Consider any busy interval <<[t1, t2)>> of job [j]. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_interval : busy_interval sched j t1 t2.

    (** Let [progress_of_job] be the desired service of job [j]. *)
    Variable progress_of_job : duration.
    Hypothesis H_progress_le_job_cost : progress_of_job <= job_cost j.

    (** Assume that for some [δ] the sum of desired progress and
        cumulative interference is bounded by [δ]. *)
    Variable δ : duration.
    Hypothesis H_total_workload_is_bounded :
      progress_of_job + cumulative_interference j t1 (t1 + δ) <= δ.

    (** Then, it must be the case that the job has received no less
        service than [progress_of_job]. *)
    Theorem j_receives_enough_service :
      service sched j (t1 + δ) >= progress_of_job.
    Proof.
      destruct (leqP (t1 + δ) t2) as [NEQ|NEQ]; last first.
      { move: (job_completes_within_busy_interval _ _ _ _ H_busy_interval) => COMPL.
        apply leq_trans with (job_cost j); first by done.
        rewrite /service -(service_during_cat _ _ _ t2); last by apply/andP; split; last apply ltnW.
        by apply leq_trans with (service_during sched j 0 t2); [done | rewrite leq_addr].
      }
      { move: H_total_workload_is_bounded => BOUND.
        rewrite addnC in BOUND; apply leq_subRL_impl in BOUND.
        apply leq_trans with (δ - cumulative_interference j t1 (t1 + δ)); first by done.
        apply leq_trans with (service_during sched j t1 (t1 + δ)).
        - eapply leq_trans.
          + by apply leq_sub2r, (interference_is_complement_to_schedule t1 t2);
              [apply H_busy_interval | apply leqnn | apply NEQ].
          + by rewrite -addnBA // subnn addn0 //.
        - rewrite /service -[X in _ <= X](service_during_cat _ _ _ t1); first by rewrite leq_addl //.
          by apply/andP; split; last rewrite leq_addr.
      }
    Qed.

  End InterferenceBoundedImpliesEnoughService.

End LowerBoundOnService.
