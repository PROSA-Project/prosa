Require Export prosa.analysis.facts.suspension.
Require Export prosa.model.task.suspension.dynamic.
Require Export prosa.analysis.facts.model.arrival_curves.

(** In this file, we prove some facts related to the dynamic self-suspension model. *)

Section TotalSuspensionBounded.

  (** Consider any type of tasks each characterized by a WCET [task_cost],
      an arrival curve [max_arrivals], and a bound on the maximum total
      self-suspension duration exhibited by any job of the task
      [task_total_suspension]. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskTotalSuspension Task}.

  (** Consider any kind of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Here we consider that the jobs can exhibit self-suspensions. *)
  Context `{JobSuspension Job}.

  (** Assume that all jobs respect the bound on the maximum total self-suspension duration. *)
  Hypothesis H_valid_dynamic_suspensions : valid_dynamic_suspensions.

  (** Consider any valid arrival sequence of jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and assume the notion of readiness for self-suspending jobs. *)
  #[local] Existing Instance suspension_ready_instance.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any valid schedule. *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** Consider any arbitrary time interval <<[t1, t1 + Δ)>>. *)
  Variable t1 : instant.
  Variable Δ : duration.

  (** We first prove a bound on the total self-suspension duration of a job. *)
  Section JobSuspensionBounded.

    (** Consider any job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_job_tsk : job_of_task tsk j.

    (** Now we prove an upper bound on the total duration a job remains suspended
        in the interval <<[t1, t1 + Δ)>>. *)
    Lemma job_suspension_bounded :
      \sum_(t1 <= t < t1 + Δ) suspended sched j t <= task_total_suspension tsk.
    Proof.
      move: H_job_tsk; rewrite /job_of_task => /eqP <-.
      apply: leq_trans; last by apply H_valid_dynamic_suspensions.
      rewrite /total_suspension.
      apply leq_trans with (n := \sum_(0 <= r < service sched j (t1 + Δ) + 1)
        \sum_(t1 <= t < (t1 + Δ) | service sched j t == r) suspended sched j t).
      { apply: sum_over_partitions_le => [t INt _].
        rewrite mem_index_iota in INt.
        rewrite mem_index_iota; apply /andP; split => //=.
        have ->: service sched j (t1 + Δ) = service sched j t + service_during sched j t (t1 + Δ)
          by rewrite service_cat; lia.
        by lia. }
      have [GEQ | LT] := boolP(service sched j (t1 + Δ) + 1 >= job_cost j).
      { erewrite big_cat_nat with (n := job_cost j) => //=.
        have ->: \sum_(job_cost j <= r < service sched j (t1 + Δ) + 1)
          \sum_(t1 <= t < t1 + Δ | service sched j t == r) suspended sched j t = 0.
        { apply /eqP; rewrite sum_nat_eq0_nat.
          apply /allP => [r INr].
          move: INr; rewrite mem_filter andTb mem_index_iota => INr.
          rewrite sum_nat_eq0_nat; apply /allP => [to INto].
          move: INto; rewrite mem_filter => /andP[/eqP SERVto INto].
          rewrite /suspended.
          have /negPf ->: ~~ pending sched j to; last by rewrite andbF.
          rewrite /pending negb_and negbK; apply /orP; right.
          rewrite /completed_by; by lia. }
        rewrite addn0.
        rewrite leq_sum_seq //= => r _ _.
        by apply : suspension_bounded_in_interval. }
      { apply leq_trans with (n := \sum_(0 <= r < job_cost j)
          \sum_(t1 <= t < t1 + Δ | service sched j t == r) suspended sched j t).
        { rewrite -ltnNge in LT.
          rewrite [in leqRHS](@big_cat_nat _ _ _ (service sched j (t1 + Δ) + 1)) => //=.
          by lia. }
        rewrite leq_sum_seq //= => r _ _.
        by apply: suspension_bounded_in_interval.
      }
    Qed.

  End JobSuspensionBounded.

  (** Next, assume that [tsk] respects the arrival curve defined by [max_arrivals]. *)
  Hypothesis H_tsk_respects_max_arrivals : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  (** Now we establish a bound on the total duration the jobs of task [tsk] remain suspended in the interval
      <<[t1, t2)>>. *)
  Lemma suspension_of_task_bounded :
    \sum_(t1 <= t < t1 + Δ) \sum_(j <- task_arrivals_between arr_seq tsk t1 (t1 + Δ)) suspended sched j t
    <= max_arrivals tsk Δ * task_total_suspension tsk.
  Proof.
    apply leq_trans with
      (n := number_of_task_arrivals arr_seq tsk t1 (t1 + Δ) * task_total_suspension tsk); last first.
    { rewrite leq_mul2r; apply /orP; right.
      rewrite -{2}[Δ](addKn t1).
      apply: H_tsk_respects_max_arrivals; by lia. }
    rewrite /number_of_task_arrivals -sum1_size big_distrl //=.
    rewrite exchange_big_idem //=.
    apply leq_sum_seq => jo INjo _; rewrite mul1n.
    apply job_suspension_bounded.
    by move: INjo; rewrite mem_filter => /andP[? ?].
  Qed.

End TotalSuspensionBounded.
