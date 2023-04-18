Require Export prosa.model.task.arrival.periodic_as_sporadic.
Require Export prosa.analysis.facts.sporadic.arrival_times.

(** In this section we show that the separation between job
    arrivals of a periodic task is some multiple of their
    corresponding task's period. *)
Section JobArrivalSeparation.

  (** Consider periodic tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{PeriodicModel Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any task [tsk] that is to be analyzed. *)
  Variable tsk : Task.

  (** Assume all tasks have a valid period and respect the periodic task model. *)
  Hypothesis H_periodic_model: respects_periodic_task_model arr_seq tsk.
  Hypothesis H_valid_period: valid_period tsk.

  (** In this section we show that two consecutive jobs of a periodic
      task have their arrival times separated by their task's
      period. *)
  Section ConsecutiveJobSeparation.

    (** Consider any two _consecutive_ jobs [j1] and [j2] of task [tsk]. *)
    Variable j1 : Job.
    Variable j2 : Job.
    Hypothesis H_j1_from_arr_seq: arrives_in arr_seq j1.
    Hypothesis H_j2_from_arr_seq: arrives_in arr_seq j2.
    Hypothesis H_j1_of_task: job_task j1 = tsk.
    Hypothesis H_j2_of_task: job_task j2 = tsk.
    Hypothesis H_consecutive_jobs: job_index arr_seq j2 = job_index arr_seq j1 + 1.

    (** We show that if job [j1] and [j2] are consecutive jobs with [j2]
        arriving after [j1], then their arrival times are separated by
        their task's period. *)
    Lemma consecutive_job_separation:
      job_arrival j2 = job_arrival j1 + task_period tsk.
    Proof.
      move : (H_periodic_model j2) => PERIODIC.
      feed_n 3 PERIODIC => //; first by rewrite H_consecutive_jobs; lia.
      move : PERIODIC => [pj' [ARR_IN_PJ' [INDPJ'J' [TSKPJ' ARRPJ']]]].
      rewrite H_consecutive_jobs addnK in INDPJ'J'.
      apply equal_index_implies_equal_jobs in INDPJ'J' => //; last by rewrite TSKPJ'.
      by rewrite INDPJ'J' in ARRPJ'; lia.
    Qed.

  End ConsecutiveJobSeparation.

  (** In this section we show that for two unequal jobs of a task,
      there exists a non-zero multiple of their task's period which separates
      their arrival times. *)
  Section ArrivalSeparationWithGivenIndexDifference.

    (** Consider any two _consecutive_ jobs [j1] and [j2] of task [tsk]
        that stem from the arrival sequence. *)
    Variable j1 j2 : Job.
    Hypothesis H_j1_from_arr_seq: arrives_in arr_seq j1.
    Hypothesis H_j2_from_arr_seq: arrives_in arr_seq j2.
    Hypothesis H_j1_of_task: job_task j1 = tsk.
    Hypothesis H_j2_of_task: job_task j2 = tsk.

    (** We'll assume that job [j1] arrives before [j2] and that
     their indices differ by an integer [k]. *)
    Variable k : nat.
    Hypothesis H_index_difference_k:  job_index arr_seq j1 + k = job_index arr_seq j2 .
    Hypothesis H_job_arrival_lt: job_arrival j1 < job_arrival j2.

    (** We prove that arrival of unequal jobs of a task [tsk] are
        separated by a non-zero multiple of [task_period tsk] provided
        their index differs by a number [k]. *)
    Lemma job_arrival_separation_when_index_diff_is_k:
      exists n,
        n > 0 /\
        job_arrival j2 = job_arrival j1 + n * task_period tsk.
    Proof.
      move: j1 j2 H_j1_of_task H_j2_of_task H_index_difference_k H_job_arrival_lt H_j2_from_arr_seq H_j1_from_arr_seq;
        clear H_index_difference_k H_job_arrival_lt H_j2_from_arr_seq H_j1_from_arr_seq H_j1_of_task H_j2_of_task j1 j2.
      move: k => s.
      elim: s => [|s IHs].
      { intros j1 j2 TSKj1 TSKj2 STEP LT ARRj1 ARRj2; exfalso.
        specialize (earlier_arrival_implies_lower_index arr_seq H_valid_arrival_sequence j1 j2) => LT_IND.
        feed_n 4 LT_IND => //; first by rewrite TSKj2.
        by lia.
      }
      { intros j1 j2 TSKj1 TSKj2 STEP LT ARRj2 ARRj1.
        specialize (exists_jobs_before_j
                      arr_seq H_valid_arrival_sequence j2 ARRj2 (job_index arr_seq j2 - s)) => BEFORE.
        destruct s as [|s].
        - exists 1; repeat split.
          by rewrite (consecutive_job_separation j1) //; lia.
        - feed BEFORE; first by lia.
          move : BEFORE => [nj [NEQNJ [TSKNJ [ARRNJ INDNJ]]]]; rewrite TSKj2 in TSKNJ.
          specialize (IHs nj j2); feed_n 6 IHs => //; first by lia.
          { by apply (lower_index_implies_earlier_arrival _ H_valid_arrival_sequence tsk) => //; lia.
          }
          move : IHs => [n [NZN ARRJ'NJ]].
          move: (H_periodic_model nj) => PERIODIC; feed_n 3 PERIODIC => //; first by lia.
          move : PERIODIC => [sj [ARR_IN_SJ [INDSJ [TSKSJ ARRSJ]]]]; rewrite ARRSJ in ARRJ'NJ.
          have INDJ : (job_index arr_seq j1 = job_index arr_seq j2 - s.+2) by lia.
          rewrite INDNJ -subnDA addn1 -INDJ in INDSJ.
          apply equal_index_implies_equal_jobs in INDSJ => //; last by rewrite TSKj1 => //.
          exists (n.+1); split; try by lia.
          rewrite INDSJ in ARRJ'NJ; rewrite mulSnr.
          by lia.
      }
    Qed.

  End ArrivalSeparationWithGivenIndexDifference.

  (** Consider any two _distinct_ jobs [j1] and [j2] of task [tsk]
      that stem from the arrival sequence. *)
  Variable j1 j2 : Job.
  Hypothesis H_j1_neq_j2: j1 <> j2.
  Hypothesis H_j1_from_arr_seq: arrives_in arr_seq j1.
  Hypothesis H_j2_from_arr_seq: arrives_in arr_seq j2.
  Hypothesis H_j1_of_task: job_task j1 = tsk.
  Hypothesis H_j2_of_task: job_task j2 = tsk.

  (** Without loss of generality, we assume that
      job [j1] arrives before job [j2]. *)
  Hypothesis H_j1_before_j2: job_arrival j1 <= job_arrival j2.

  (** We generalize the above lemma to show that any two unequal
      jobs of task [tsk] are separated by a non-zero multiple
      of [task_period tsk]. *)
  Lemma job_sep_periodic:
    exists n,
      n > 0 /\
      job_arrival j2 = job_arrival j1 + n * task_period tsk.
  Proof.
    apply job_arrival_separation_when_index_diff_is_k with (k := (job_index arr_seq j2 - job_index arr_seq j1)) => //.
    - apply subnKC.
      move_neq_up IND.
      eapply lower_index_implies_earlier_arrival in IND => //.
      by move_neq_down IND.
    - case: (boolP (job_index arr_seq j1 == job_index arr_seq j2)) => [/eqP EQ_IND|NEQ_IND].
      + by apply equal_index_implies_equal_jobs in EQ_IND => //; rewrite H_j1_of_task.
      + move: NEQ_IND; rewrite neq_ltn => /orP [LT|LT].
        * by eapply (lower_index_implies_earlier_arrival) in LT.
        * eapply (lower_index_implies_earlier_arrival) in LT => //.
          by move_neq_down LT.
  Qed.

End JobArrivalSeparation.
