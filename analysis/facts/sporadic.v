Require Export prosa.model.task.arrival.periodic.
Require Export prosa.analysis.facts.job_index.

(** * The Sporadic Model *)

(** In this section we prove a few basic properties involving 
    job indices in context of the sporadic model. *)
Section SporadicModelIndexLemmas.
        
  (** Consider sporadic tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{TaskMaxInterArrival Task}.
  Context `{SporadicModel Task}.
  
  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arrseq: arrival_sequence_uniq arr_seq.
  
  (** ... and any sporadic task [tsk] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_sporadic_model: respects_sporadic_task_model arr_seq tsk.
  Hypothesis H_valid_inter_min_arrival: valid_task_min_inter_arrival_time tsk.

  (** Consider any two jobs from the arrival sequence that stem 
      from task [tsk]. *)  
  Variable j1 : Job.
  Variable j2 : Job.
  Hypothesis H_j1_from_arrseq: arrives_in arr_seq j1.
  Hypothesis H_j2_from_arrseq: arrives_in arr_seq j2.
  Hypothesis H_j1_task: job_task j1 = tsk.
  Hypothesis H_j2_task: job_task j2 = tsk.
  
  (** We first show that for any two jobs [j1] and [j2], [j2] arrives after [j1] 
   provided [job_index] of [j2] strictly exceeds the [job_index] of [j1]. *)
  Lemma lower_index_implies_earlier_arrival:
      job_index arr_seq j1 < job_index arr_seq j2 ->
      job_arrival j1 < job_arrival j2.
  Proof.
    intro IND.
    move: (H_sporadic_model j1 j2) => SPORADIC; feed_n 6 SPORADIC => //. 
    - rewrite -> diff_jobs_iff_diff_indices => //; eauto.
       + now ssrlia.
       + now rewrite H_j1_task. 
    - apply (index_lte_implies_arrival_lte arr_seq); try eauto.
      now rewrite H_j1_task.
    - have POS_IA : task_min_inter_arrival_time tsk > 0 by auto.
      now ssrlia.
  Qed.

End SporadicModelIndexLemmas.

(** ** Different jobs have different arrival times. *) 
Section DifferentJobsImplyDifferentArrivalTimes.

  (** Consider sporadic tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{TaskMaxInterArrival Task}.
  Context `{SporadicModel Task}.
  
  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arrseq: arrival_sequence_uniq arr_seq.
  
  (** ... and any sporadic task [tsk] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_sporadic_model: respects_sporadic_task_model arr_seq tsk.
  Hypothesis H_valid_inter_min_arrival: valid_task_min_inter_arrival_time tsk.

  (** Consider any two jobs from the arrival sequence that stem 
      from task [tsk]. *)  
  Variable j1 : Job.
  Variable j2 : Job.
  Hypothesis H_j1_from_arrseq: arrives_in arr_seq j1.
  Hypothesis H_j2_from_arrseq: arrives_in arr_seq j2.
  Hypothesis H_j1_task: job_task j1 = tsk.
  Hypothesis H_j2_task: job_task j2 = tsk.

  (** We observe that distinct jobs cannot have equal arrival times. *)
  Lemma uneq_job_uneq_arr:
      j1 <> j2 ->
      job_arrival j1 <> job_arrival j2.
  Proof.
    intros UNEQ EQ_ARR.
    rewrite -> diff_jobs_iff_diff_indices in UNEQ => //; eauto; last by rewrite H_j1_task.
    move /neqP: UNEQ; rewrite neq_ltn => /orP [LT|LT].
    all: now apply lower_index_implies_earlier_arrival with (tsk0 := tsk) in LT => //; ssrlia.
  Qed.

  (** We prove a stronger version of the above lemma by showing 
   that jobs [j1] and [j2] are equal if and only if they arrive at the
   same time. *)
  Lemma same_jobs_iff_same_arr:
    j1 = j2 <->
    job_arrival j1 = job_arrival j2.
  Proof.
    split; first by apply congr1.
    intro EQ_ARR.
    case: (boolP (j1 == j2)) => [/eqP EQ | /eqP NEQ]; first by auto.
    rewrite -> diff_jobs_iff_diff_indices in NEQ => //; eauto; last by rewrite H_j1_task.
    move /neqP: NEQ; rewrite neq_ltn => /orP [LT|LT].
    all: now apply lower_index_implies_earlier_arrival with (tsk0 := tsk) in LT => //; ssrlia.
  Qed.
    
End DifferentJobsImplyDifferentArrivalTimes.

(** In this section we prove a few properties regarding task arrivals
    in context of the sporadic task model. *)
Section SporadicArrivals.

  (** Consider sporadic tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{SporadicModel Task}.
  Context `{TaskMaxInterArrival Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arr_seq: arrival_sequence_uniq arr_seq.

  (** ... and any sporadic task [tsk] to be analyzed. *)
  Variable tsk : Task.
  
  (** Assume all tasks have valid minimum inter-arrival times, valid offsets, and respect the 
      sporadic task model. *)
  Hypothesis H_sporadic_model: respects_sporadic_task_model arr_seq tsk.
  Hypothesis H_valid_inter_min_arrival: valid_task_min_inter_arrival_time tsk.
  Hypothesis H_valid_offset: valid_offset arr_seq tsk.

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
    specialize (exists_two Job (task_arrivals_at_job_arrival arr_seq j)) => EXISTS_TWO.
    destruct EXISTS_TWO as [a [b [NEQ [A_IN B_IN]]]]; [by done | by apply filter_uniq | ].
    rewrite mem_filter in A_IN; rewrite mem_filter in B_IN.
    move: A_IN B_IN => /andP [/eqP TSKA ARRA] /andP [/eqP TSKB ARRB].
    move: (ARRA); move: (ARRB); rewrite /arrivals_at => A_IN B_IN.
    apply in_arrseq_implies_arrives in A_IN; apply in_arrseq_implies_arrives in B_IN.
    have EQ_ARR_A : (job_arrival a = job_arrival j) by apply H_consistent_arrivals.
    have EQ_ARR_B : (job_arrival b = job_arrival j) by apply H_consistent_arrivals.
    apply uneq_job_uneq_arr with (arr_seq0 := arr_seq) (tsk0 := job_task j) in NEQ => //.
    now rewrite EQ_ARR_A EQ_ARR_B in NEQ.
  Qed.

  (** We show that no jobs of the task [tsk] other than [j1] arrive at
      the same time as [j1], and thus the task arrivals at [job arrival j1]
      consists only of job [j1]. *) 
  Lemma only_j_in_task_arrivals_at_j:
    task_arrivals_at_job_arrival arr_seq j1 = [::j1].
  Proof.
    set (task_arrivals_at_job_arrival arr_seq j1) as seq in *.
    have J_IN_FILTER : (j1 \in seq) by apply arrives_in_task_arrivals_at.
    have SIZE_CASE : size seq = 0 \/ size seq = 1 \/ size seq > 1
      by intros; now destruct (size seq) as [ | [ | ]]; try auto.
    move: SIZE_CASE => [Z|[ONE|GTONE]].
    - apply size0nil in Z.
      now rewrite Z in J_IN_FILTER. 
    - repeat (destruct seq; try by done).
      rewrite mem_seq1 in J_IN_FILTER; move : J_IN_FILTER => /eqP J1_S.
      now rewrite J1_S.
    - exfalso.
      apply size_task_arrivals_at_leq_one.
      exists j1.
      now repeat split => //; try rewrite H_j1_task.
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
    now rewrite /task_arrivals_at_job_arrival H_j1_task in J_AT.
  Qed.
  
  (** We show that a job [j1] is the first job that arrives 
      in task arrivals at [job_arrival j1] by showing that the 
      index of job [j1] in [task_arrivals_at_job_arrival arr_seq j1] is 0. *)
  Lemma index_j_in_task_arrivals_at:
    index j1 (task_arrivals_at_job_arrival arr_seq j1) = 0.
  Proof.
    now rewrite only_j_in_task_arrivals_at_j //= eq_refl.
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
    apply uneq_job_uneq_arr with (arr_seq0 := arr_seq) (tsk0 := job_task j1) => //; try by rewrite H_j1_task.
    - now apply prev_job_arr.
    - now apply prev_job_task.
    - intro EQ.
      have SM_IND: job_index arr_seq j1 - 1 = job_index arr_seq j1 by rewrite -prev_job_index // EQ.
      now ssrlia.
  Qed.

  (** We show that task arrivals at [job_arrival j1] is the 
      same as task arrivals that arrive between [job_arrival j1] 
      and [job_arrival j1 + 1]. *)
  Lemma task_arrivals_at_as_task_arrivals_between:
    task_arrivals_at_job_arrival arr_seq j1 = task_arrivals_between arr_seq tsk (job_arrival j1) (job_arrival j1).+1.
  Proof.
    rewrite /task_arrivals_at_job_arrival /task_arrivals_at /task_arrivals_between /arrivals_between.
    now rewrite big_nat1 H_j1_task.
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
    now rewrite cat0s H_j1_task.
  Qed.
    
End SporadicArrivals.
