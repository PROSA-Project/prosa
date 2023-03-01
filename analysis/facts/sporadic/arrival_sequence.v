Require Export analysis.facts.sporadic.arrival_times.

(** * Job Arrival Sequence in the Sporadic Model *)

(** In this file, we prove basic facts about a task's arrival sequence
    in the sporadic task model. *)
Section SporadicArrivals.

  (** Consider sporadic tasks  ... *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any sporadic task [tsk] to be analyzed. *)
  Variable tsk : Task.

  (** Assume all tasks have valid minimum inter-arrival times, valid offsets, and respect the
      sporadic task model. *)
  Hypothesis H_sporadic_model: respects_sporadic_task_model arr_seq tsk.
  Hypothesis H_valid_inter_min_arrival: valid_task_min_inter_arrival_time tsk.

  (** Consider any two jobs from the arrival sequence that stem
      from task [tsk]. *)
  Variable j1 j2 : Job.
  Hypothesis H_j1_from_arrival_sequence: arrives_in arr_seq j1.
  Hypothesis H_j2_from_arrival_sequence: arrives_in arr_seq j2.
  Hypothesis H_j1_task: job_task j1 = tsk.
  Hypothesis H_j2_task: job_task j2 = tsk.

  (** We show that a sporadic task with valid min inter-arrival time cannot
      have more than one job arriving at any time. *)
  Lemma size_task_arrivals_at_leq_one:
    (exists j,
        size (task_arrivals_at_job_arrival arr_seq j) > 1 /\
        respects_sporadic_task_model arr_seq (job_task j) /\
        valid_task_min_inter_arrival_time (job_task j)) ->
      False.
  Proof.
    move => [j [SIZE_G [PERIODIC VALID_TMIA]]].
    specialize (exists_two (task_arrivals_at_job_arrival arr_seq j)) => EXISTS_TWO.
    move : H_valid_arrival_sequence => [CONSISTENT UNIQ].
    destruct EXISTS_TWO as [a [b [NEQ [A_IN B_IN]]]]; [by done | by apply filter_uniq | ].
    rewrite mem_filter in A_IN; rewrite mem_filter in B_IN.
    move: A_IN B_IN => /andP [/eqP TSKA ARRA] /andP [/eqP TSKB ARRB].
    move: (ARRA); move: (ARRB); rewrite /arrivals_at => A_IN B_IN.
    apply in_arrseq_implies_arrives in A_IN; apply in_arrseq_implies_arrives in B_IN.
    have EQ_ARR_A : (job_arrival a = job_arrival j) by rt_eauto.
    have EQ_ARR_B : (job_arrival b = job_arrival j) by rt_eauto.
    try ( apply uneq_job_uneq_arr with (arr_seq0 := arr_seq) (tsk0 := job_task j) in NEQ => // ) ||
    apply uneq_job_uneq_arr with (arr_seq := arr_seq) (tsk := job_task j) in NEQ => //.
    by rewrite EQ_ARR_A EQ_ARR_B in NEQ.
  Qed.

  (** We show that no jobs of the task [tsk] other than [j1] arrive at
      the same time as [j1], and thus the task arrivals at [job arrival j1]
      consists only of job [j1]. *)
  Lemma only_j_in_task_arrivals_at_j:
    task_arrivals_at_job_arrival arr_seq j1 = [::j1].
  Proof.
    set (task_arrivals_at_job_arrival arr_seq j1) as seq in *.
    have J_IN_FILTER : (j1 \in seq) by apply arrives_in_task_arrivals_at; rt_auto.
    have SIZE_CASE : size seq = 0 \/ size seq = 1 \/ size seq > 1
      by intros; now destruct (size seq) as [ | [ | ]]; try auto.
    move: SIZE_CASE => [Z|[ONE|GTONE]].
    - apply size0nil in Z.
      by rewrite Z in J_IN_FILTER.
    - case: seq ONE J_IN_FILTER => [//| s [|//]] J_ONE.
      by rewrite mem_seq1 => /eqP ->.
    - exfalso.
      apply size_task_arrivals_at_leq_one.
      exists j1.
      by repeat split => //; try rewrite H_j1_task.
  Qed.

  (** We show that no jobs of the task [tsk] other than [j1] arrive at
      the same time as [j1], and thus the task arrivals at [job arrival j1]
      consists only of job [j1]. *)
  Lemma only_j_at_job_arrival_j:
    forall t,
      job_arrival j1 = t ->
      task_arrivals_at arr_seq tsk t = [::j1].
  Proof.
    intros t ARR.
    rewrite -ARR.
    specialize (only_j_in_task_arrivals_at_j) => J_AT.
    by rewrite /task_arrivals_at_job_arrival H_j1_task in J_AT.
  Qed.

  (** We show that a job [j1] is the first job that arrives
      in task arrivals at [job_arrival j1] by showing that the
      index of job [j1] in [task_arrivals_at_job_arrival arr_seq j1] is 0. *)
  Lemma index_j_in_task_arrivals_at:
    index j1 (task_arrivals_at_job_arrival arr_seq j1) = 0.
  Proof.
    by rewrite only_j_in_task_arrivals_at_j //= eq_refl.
  Qed.

  (** We observe that for any job [j] the arrival time of [prev_job j] is
      strictly less than the arrival time of [j] in context of periodic tasks. *)
  Lemma prev_job_arr_lt:
    job_index arr_seq j1 > 0 ->
    job_arrival (prev_job arr_seq j1) < job_arrival j1.
  Proof.
    intros IND.
    have PREV_ARR_LTE : job_arrival (prev_job arr_seq j1) <= job_arrival j1 by apply prev_job_arr_lte => //.
    rewrite ltn_neqAle; apply /andP.
    split => //; apply /eqP.
    try ( apply uneq_job_uneq_arr with (arr_seq0 := arr_seq) (tsk0 := job_task j1) => //; try by rewrite H_j1_task ) ||
    apply uneq_job_uneq_arr with (arr_seq := arr_seq) (tsk := job_task j1) => //; try by rewrite H_j1_task.
    - by apply prev_job_arr.
    - by apply prev_job_task.
    - intro EQ.
      have SM_IND: job_index arr_seq j1 - 1 = job_index arr_seq j1 by rewrite -prev_job_index // EQ.
      by lia.
  Qed.

  (** We show that task arrivals at [job_arrival j1] is the
      same as task arrivals that arrive between [job_arrival j1]
      and [job_arrival j1 + 1]. *)
  Lemma task_arrivals_at_as_task_arrivals_between:
    task_arrivals_at_job_arrival arr_seq j1 = task_arrivals_between arr_seq tsk (job_arrival j1) (job_arrival j1).+1.
  Proof.
    rewrite /task_arrivals_at_job_arrival /task_arrivals_at /task_arrivals_between /arrivals_between.
    by rewrite big_nat1 H_j1_task.
  Qed.

  (** We show that the task arrivals up to the previous job [j1] concatenated with
      the sequence [::j1] (the sequence containing only the job [j1]) is same as
      task arrivals up to [job_arrival j1]. *)
  Lemma prev_job_cat:
    job_index arr_seq j1 > 0 ->
    task_arrivals_up_to_job_arrival arr_seq (prev_job arr_seq j1) ++ [::j1] = task_arrivals_up_to_job_arrival arr_seq j1.
  Proof.
    intros JIND.
    rewrite -only_j_in_task_arrivals_at_j task_arrivals_at_as_task_arrivals_between.
    rewrite /task_arrivals_up_to_job_arrival prev_job_task => //.
    rewrite [in X in _ = X] (task_arrivals_cat _ _ (job_arrival (prev_job arr_seq j1))); last by
        apply ltnW; apply prev_job_arr_lt.
    rewrite [in X in _ = _ ++ X] (task_arrivals_between_cat _ _ _ (job_arrival j1) _) => //; last by apply prev_job_arr_lt.
    rewrite no_jobs_between_consecutive_jobs => //.
    by rewrite cat0s H_j1_task.
  Qed.

End SporadicArrivals.
