Require Export prosa.model.task.arrival.sporadic.
Require Export prosa.analysis.facts.job_index.

(** * Job Arrival Times in the Sporadic Model *)

(** In this file, we prove basic facts about the arrival times of jobs
    in the sporadic task model. *)
Section ArrivalTimes.

  (** Consider sporadic tasks ... *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any sporadic task [tsk] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_sporadic_model : respects_sporadic_task_model arr_seq tsk.
  Hypothesis H_valid_inter_min_arrival : valid_task_min_inter_arrival_time tsk.

  (** We first show that for any two jobs [j1] and [j2], [j2] arrives after [j1]
      provided [job_index] of [j2] strictly exceeds the [job_index] of [j1]. *)
  Lemma lower_index_implies_earlier_arrival :
    forall j1 j2,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      job_task j1 = tsk ->
      job_task j2 = tsk ->
      job_index arr_seq j1 < job_index arr_seq j2 ->
      job_arrival j1 < job_arrival j2.
  Proof.
    move=> j1 j2 ARR1 ARR2 TSK1 TSK2 LT_IND.
    move: (H_sporadic_model j1 j2) => SPORADIC; feed_n 6 SPORADIC => //.
    - rewrite -> diff_jobs_iff_diff_indices => //; eauto; first by lia.
      by subst.
    - apply (index_lte_implies_arrival_lte arr_seq); try eauto.
      by subst.
    - have POS_IA : task_min_inter_arrival_time tsk > 0 by auto.
      by lia.
  Qed.

  (** In the following, consider (again) any two jobs from the arrival
      sequence that stem from task [tsk].

      NB: The following variables and hypotheses match the premises of
          the preceding lemma. However, we cannot move these
          declarations before the prior lemma because we need
          [lower_index_implies_earlier_arrival] to be ∀-quantified in
          the next proof. *)
  Variable j1 : Job.
  Variable j2 : Job.
  Hypothesis H_j1_from_arrseq : arrives_in arr_seq j1.
  Hypothesis H_j2_from_arrseq : arrives_in arr_seq j2.
  Hypothesis H_j1_task : job_task j1 = tsk.
  Hypothesis H_j2_task : job_task j2 = tsk.

  (** We prove that jobs [j1] and [j2] are equal if and only if they
      arrive at the same time. *)
  Lemma same_jobs_iff_same_arr :
    j1 = j2 <->
    job_arrival j1 = job_arrival j2.
  Proof.
    split; first by move=> ->.
    move=> EQ_ARR.
    case: (boolP (j1 == j2)) => [/eqP EQ | /eqP NEQ] //; exfalso.
    rewrite -> diff_jobs_iff_diff_indices in NEQ => //; eauto; last by rewrite H_j1_task.
    move /neqP: NEQ; rewrite neq_ltn => /orP [LT|LT].
    all: by apply lower_index_implies_earlier_arrival in LT => //; lia.
  Qed.

  (** As a corollary, we observe that distinct jobs cannot have equal arrival times. *)
  Corollary uneq_job_uneq_arr :
      j1 <> j2 ->
      job_arrival j1 <> job_arrival j2.
  Proof. by rewrite -same_jobs_iff_same_arr. Qed.

End ArrivalTimes.

