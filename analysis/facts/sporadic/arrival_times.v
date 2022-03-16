Require Export prosa.model.task.arrival.sporadic.
Require Export prosa.analysis.facts.job_index.

(** * Job Arrival Times in the Sporadic Model *)

(** In this file, we prove a few basic facts about the arrival times
    of jobs in the sporadic task model. *)
Section SporadicModelIndexLemmas.

  (** Consider sporadic tasks ... *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

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
    move=> LT_IND.
    move: (H_sporadic_model j1 j2) => SPORADIC; feed_n 6 SPORADIC => //.
    - rewrite -> diff_jobs_iff_diff_indices => //; eauto; first by lia.
      by subst.
    - apply (index_lte_implies_arrival_lte arr_seq); try eauto.
      by subst.
    - have POS_IA : task_min_inter_arrival_time tsk > 0 by auto.
      by lia.
  Qed.

End SporadicModelIndexLemmas.

(** ** Different jobs have different arrival times. *)
Section DifferentJobsImplyDifferentArrivalTimes.

  (** Consider sporadic tasks ... *)
  Context {Task : TaskType} `{SporadicModel Task}.

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
    all: try ( now apply lower_index_implies_earlier_arrival with (tsk0 := tsk) in LT => //; lia ) ||
             now apply lower_index_implies_earlier_arrival with (tsk := tsk) in LT => //; lia.
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
    all: try ( now apply lower_index_implies_earlier_arrival with (tsk0 := tsk) in LT => //; lia ) || now apply lower_index_implies_earlier_arrival with (tsk := tsk) in LT => //; lia.
  Qed.

End DifferentJobsImplyDifferentArrivalTimes.

