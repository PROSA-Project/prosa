Require Export prosa.analysis.facts.model.task_arrivals.

(** In this section, we prove some properties related to [job_index]. *)
Section JobIndexLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any jobs associated with the tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any arrival sequence with consistent and non-duplicate arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any two jobs [j1] and [j2] from this arrival sequence
   that stem from the same task. *)
  Variable j1 j2 : Job.
  Hypothesis H_j1_from_arrival_sequence : arrives_in arr_seq j1.
  Hypothesis H_j2_from_arrival_sequence : arrives_in arr_seq j2.
  Hypothesis H_same_task : job_task j1 = job_task j2.

  (** In the next section, we prove some basic properties about jobs with equal indices. *)
  Section EqualJobIndex.

    (** Assume that the jobs [j1] and [j2] have the same [job_index]
     in the arrival sequence. *)
    Hypothesis H_equal_index : job_index arr_seq j1 = job_index arr_seq j2.

    (** To show that jobs [j1] and [j2] are equal, we'll perform case
     analysis on the relation between their arrival times. *)

    (** Jobs with equal indices have to be equal regardless of their
     arrival times because of the way [job_index] is defined (i.e.,
     jobs are first ordered according to their arrival times and ties are
     broken arbitrarily due to which no two unequal jobs have the same
     [job_index]). *)

    (** In case job [j2] arrives after or at the same time as [j1] arrives, we
        show that the jobs are equal. *)
    Lemma case_arrival_lte_implies_equal_job :
      job_arrival j1 <= job_arrival j2 -> j1 = j2.
    Proof.
      move => ARR_LT.
      move: H_equal_index => IND.
      apply task_arrivals_up_to_prefix_cat with (arr_seq := arr_seq) in ARR_LT => //.
      move : ARR_LT => [xs ARR_CAT].
      apply eq_ind_in_seq with (xs := task_arrivals_up_to_job_arrival arr_seq j2) => //.
      - by rewrite -/(job_index _ _) -IND -ARR_CAT index_cat ifT;
          try apply arrives_in_task_arrivals_up_to.
      - rewrite -ARR_CAT mem_cat; apply /orP.
        by left; apply arrives_in_task_arrivals_up_to.
      - by apply arrives_in_task_arrivals_up_to.
    Qed.

    (** And similarly if [j1] arrives after [j2], we show that
        the jobs are equal. *)
    Lemma case_arrival_gt_implies_equal_job :
      job_arrival j1 > job_arrival j2 -> j1 = j2.
    Proof.
      move=> LT.
      move: H_equal_index => IND.
      apply ltnW, (task_arrivals_up_to_prefix_cat arr_seq) in LT => //.
      move: LT => [xs ARR_CAT].
      apply (eq_ind_in_seq _ _ (task_arrivals_up_to_job_arrival arr_seq j1)) => //.
      - by rewrite -/(job_index _ _) IND -ARR_CAT index_cat ifT;
          try apply arrives_in_task_arrivals_up_to.
      - by apply arrives_in_task_arrivals_up_to.
      - rewrite -ARR_CAT mem_cat; apply /orP.
        by left; apply arrives_in_task_arrivals_up_to.
    Qed.

    (** And finally we show that irrespective of the relation between the arrival
       of job [j1] and [j2], [j1] must be equal to [j2]. *)
    Lemma equal_index_implies_equal_jobs :
      j1 = j2.
    Proof.
      case: (ltngtP (job_arrival j1) (job_arrival j2)) => [LT|GT|EQ].
      - by apply case_arrival_lte_implies_equal_job; lia.
      - by apply case_arrival_gt_implies_equal_job; lia.
      - by apply case_arrival_lte_implies_equal_job; lia.
    Qed.

  End EqualJobIndex.

  (** We show that jobs of a task are different if and only if they
   have different indices. *)
  Lemma diff_jobs_iff_diff_indices :
    j1 <> j2 <->
    job_index arr_seq j1 <> job_index arr_seq j2.
  Proof.
    split.
    + move => NEQJ EQ.
      by apply equal_index_implies_equal_jobs in EQ.
    + move => NEQ EQ.
      by move: EQ NEQ => ->.
  Qed.

  (** We show that [job_index j] can be written as a sum of [size (task_arrivals_before_job_arrival j)]
      and [index j (task_arrivals_at arr_seq (job_task j) (job_arrival j))]. *)
  Lemma index_as_sum_size_and_index :
    job_index arr_seq j1
    = size (task_arrivals_before_job_arrival arr_seq j1)
      + index j1 (task_arrivals_at_job_arrival arr_seq j1).
  Proof.
    rewrite /task_arrivals_at_job_arrival /job_index task_arrivals_up_to_cat //.
    rewrite index_cat ifF; first by reflexivity.
    apply Bool.not_true_is_false; intro T.
    move : T; rewrite mem_filter => /andP [/eqP SM_TSK JB_IN_ARR].
    apply mem_bigcat_nat_exists in JB_IN_ARR; move : JB_IN_ARR => [ind [JB_IN IND_INTR]].
    have ARR : job_arrival j1 =  ind by [].
    lia.
  Qed.

  (** Given jobs [j1] and [j2] in [arrivals_between_P arr_seq P t1 t2], the fact that
      [j2] arrives strictly before [j1] implies that [j2] also belongs in the sequence
      [arrivals_between_P arr_seq P t1 (job_arrival j1)]. *)
  Lemma arrival_lt_implies_job_in_arrivals_between_P :
    forall (P : Job -> bool) (t1 t2 : instant),
      (j1 \in arrivals_between_P arr_seq P t1 t2) ->
      (j2 \in arrivals_between_P arr_seq P t1 t2) ->
      job_arrival j2 < job_arrival j1 ->
      j2 \in arrivals_between_P arr_seq P t1 (job_arrival j1).
  Proof.
    intros * J1_IN J2_IN ARR_LT.
    rewrite mem_filter in J2_IN; move : J2_IN => /andP [PJ2 J2ARR] => //.
    rewrite mem_filter; apply /andP; split => //.
    apply mem_bigcat_nat_exists in J2ARR; move : J2ARR => [i [J2_IN INEQ]].
    apply mem_bigcat_nat with (j := i) => //.
    apply job_arrival_at in J2_IN => //.
    lia.
  Qed.

  (** We show that jobs in the sequence [arrivals_between_P] are ordered by their arrival times, i.e.,
      if index of a job [j2] is greater than or equal to index of any other job [j1] in the sequence,
      then [job_arrival j2] must be greater than or equal to [job_arrival j1]. *)
  Lemma index_lte_implies_arrival_lte_P :
    forall (P : Job -> bool) (t1 t2 : instant),
      (j1 \in arrivals_between_P arr_seq P t1 t2) ->
      (j2 \in arrivals_between_P arr_seq P t1 t2) ->
      index j1 (arrivals_between_P arr_seq P t1 t2) <= index j2 (arrivals_between_P arr_seq P t1 t2) ->
      job_arrival j1 <= job_arrival j2.
  Proof.
    intros * IN1 IN2 LE.
    move_neq_up LT; move_neq_down LE.
    rewrite -> arrivals_P_cat with (t := job_arrival j1); last by apply job_arrival_between_P in IN1 => //.
    rewrite !index_cat ifT; last by eapply arrival_lt_implies_job_in_arrivals_between_P; eauto.
    rewrite ifF.
    - eapply leq_trans; [ | by erewrite leq_addr].
      rewrite index_mem.
      by eapply arrival_lt_implies_job_in_arrivals_between_P; eauto.
    - apply Bool.not_true_is_false; intro T.
      by apply job_arrival_between_P in T; try lia.
  Qed.

  (** We observe that index of job [j1] is same in the
   sequences [task_arrivals_up_to_job_arrival j1] and [task_arrivals_up_to_job_arrival j2]
   provided [j2] arrives after [j1]. *)
  Lemma job_index_same_in_task_arrivals :
    job_arrival j1 <= job_arrival j2 ->
    index j1 (task_arrivals_up_to_job_arrival arr_seq j1) = index j1 (task_arrivals_up_to_job_arrival arr_seq j2).
  Proof.
    rewrite leq_eqVlt => /orP [/eqP LT|LT]; first by rewrite /task_arrivals_up_to_job_arrival LT H_same_task.
    have CONSISTENT : consistent_arrival_times arr_seq by [].
    specialize (arrival_lt_implies_strict_prefix arr_seq CONSISTENT (job_task j1) j1 j2) => SUB.
    feed_n 5 SUB => //; move: SUB => [xs2 [NEMPT2 CAT2]].
    rewrite -CAT2 index_cat ifT //=.
    by apply arrives_in_task_arrivals_up_to.
  Qed.

  (** We show that the [job_index] of a job [j1] is strictly less than
   the size of [task_arrivals_up_to_job_arrival arr_seq j1]. *)
  Lemma index_job_lt_size_task_arrivals_up_to_job :
    job_index arr_seq j1 < size (task_arrivals_up_to_job_arrival arr_seq j1).
  Proof.
    by rewrite /job_index index_mem; apply: arrives_in_task_arrivals_up_to.
  Qed.

  (** Finally, we show that a lower job index implies an earlier arrival time. *)
  Lemma index_lte_implies_arrival_lte :
    job_index arr_seq j2 <= job_index arr_seq j1 ->
    job_arrival j2 <= job_arrival j1.
  Proof.
    intros IND_LT.
    rewrite /job_index in IND_LT.
    move_neq_up ARR_GT; move_neq_down IND_LT.
    rewrite job_index_same_in_task_arrivals /task_arrivals_up_to_job_arrival; try lia.
    rewrite -> task_arrivals_cat with (t_m := job_arrival j1); try lia.
    rewrite -H_same_task !index_cat ifT; try by apply arrives_in_task_arrivals_up_to => //.
    rewrite ifF.
    - by eapply leq_trans;
        [apply index_job_lt_size_task_arrivals_up_to_job | rewrite leq_addr].
    - apply Bool.not_true_is_false; intro T.
      by apply job_arrival_between_P in T; try lia.
  Qed.

  (** We show that if job [j1] arrives earlier than job [j2]
   then [job_index arr_seq j1] is strictly less than [job_index arr_seq j2]. *)
  Lemma earlier_arrival_implies_lower_index :
    job_arrival j1 < job_arrival j2 ->
    job_index arr_seq j1 < job_index arr_seq j2.
  Proof.
    intros ARR_LT.
    move_neq_up IND_LT; move_neq_down ARR_LT.
    by apply index_lte_implies_arrival_lte.
  Qed.

  (** We prove a weaker version of the lemma [index_job_lt_size_task_arrivals_up_to_job],
      given that the [job_index] of [j] is positive. *)
  Lemma job_index_minus_one_lt_size_task_arrivals_up_to :
    job_index arr_seq j1 - 1 < size (task_arrivals_up_to_job_arrival arr_seq j1).
  Proof.
    apply leq_ltn_trans with (n := job_index arr_seq j1); try lia.
    by apply index_job_lt_size_task_arrivals_up_to_job.
  Qed.

  (** Since [task_arrivals_up_to_job_arrival arr_seq j] has at least the job
      [j] in it, its size has to be positive. *)
  Lemma positive_job_index_implies_positive_size_of_task_arrivals :
    size (task_arrivals_up_to_job_arrival arr_seq j1) > 0.
  Proof.
    rewrite lt0n; apply /eqP; intro Z.
    apply size0nil in Z.
    have J_IN : (j1 \in task_arrivals_up_to_job_arrival arr_seq j1)
                  by apply arrives_in_task_arrivals_up_to.
    by rewrite Z in J_IN.
  Qed.

End JobIndexLemmas.

(** In this section, we prove a few basic properties of
    function [prev_job]. *)
Section PreviousJob.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any jobs associated with the tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any unique arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and an arbitrary job with a positive [job_index]. *)
  Variable j : Job.
  Hypothesis H_arrives_in_arr_seq : arrives_in arr_seq j.
  Hypothesis H_positive_job_index : job_index arr_seq j > 0.

  (** We observe that the fact that job [j] is in the arrival sequence
      implies that job [prev_job j] is in the arrival sequence. *)
  Lemma prev_job_arr :
    arrives_in arr_seq (prev_job arr_seq j).
  Proof.
    destruct (default_or_in (job_index arr_seq j - 1) j (task_arrivals_up_to_job_arrival arr_seq j)) as [EQ|IN].
    + by rewrite /prev_job EQ.
    + apply in_arrivals_implies_arrived with (t1 := 0) (t2 := (job_arrival j).+1).
      by move: IN; rewrite mem_filter => /andP [_ IN].
  Qed.

  (** We show that the index of [prev_job j] in task arrivals up to [j] is one less
      than [job_index arr_seq j]. *)
  Lemma prev_job_index :
    index (prev_job arr_seq j) (task_arrivals_up_to_job_arrival arr_seq j) = job_index arr_seq j - 1.
  Proof.
    apply index_uniq; last by exact: uniq_task_arrivals.
    apply leq_ltn_trans with (n := job_index arr_seq j); try lia.
    by apply index_job_lt_size_task_arrivals_up_to_job.
  Qed.

  (** Observe that job [j] and [prev_job j] stem from the same task. *)
  Lemma prev_job_task :
    job_task (prev_job arr_seq j) = job_task j.
  Proof.
    specialize (job_index_minus_one_lt_size_task_arrivals_up_to arr_seq H_valid_arrival_sequence j H_arrives_in_arr_seq) => SIZEL.
    rewrite -prev_job_index index_mem mem_filter in SIZEL.
    by move : SIZEL => /andP [/eqP TSK PREV_IN].
  Qed.

  (** We show that [prev_job arr_seq j] belongs in [task_arrivals_up_to_job_arrival arr_seq j]. *)
  Lemma prev_job_in_task_arrivals_up_to_j :
    prev_job arr_seq j \in task_arrivals_up_to_job_arrival arr_seq j.
  Proof.
    rewrite /prev_job -index_mem index_uniq;
      try by apply job_index_minus_one_lt_size_task_arrivals_up_to.
    by apply uniq_task_arrivals.
  Qed.

  (** We observe that for any job [j] the arrival time of [prev_job j] is
      strictly less than the arrival time of [j] in context of periodic tasks. *)
  Lemma prev_job_arr_lte :
    job_arrival (prev_job arr_seq j) <= job_arrival j.
  Proof.
    move : (prev_job_in_task_arrivals_up_to_j) => PREV_JOB_IN.
    rewrite mem_filter in PREV_JOB_IN; move : PREV_JOB_IN => /andP [TSK PREV_IN].
    apply mem_bigcat_nat_exists in PREV_IN; move : PREV_IN => [i [PREV_IN INEQ]].
    move : H_valid_arrival_sequence => [CONSISTENT UNIQ].
    apply CONSISTENT in PREV_IN; rewrite -PREV_IN in INEQ.
    lia.
  Qed.

  (** We show that for any job [j] the job index of [prev_job j] is one less
      than the job index of [j]. *)
  Lemma prev_job_index_j :
    job_index arr_seq j > 0 ->
    job_index arr_seq (prev_job arr_seq j) = job_index arr_seq j - 1.
  Proof.
    intros NZ_IND.
    rewrite -prev_job_index.
    apply: job_index_same_in_task_arrivals => //.
    - exact: prev_job_arr.
    - exact: prev_job_task.
    - exact: prev_job_arr_lte.
  Qed.

  (** We also show that for any job [j] there are no task arrivals
      between [prev_job j] and [j].*)
  Lemma no_jobs_between_consecutive_jobs :
    job_index arr_seq j > 0 ->
    task_arrivals_between arr_seq (job_task j)
                          (job_arrival (prev_job arr_seq j)).+1 (job_arrival j) = [::].
  Proof.
    move => POS_IND.
    move : (prev_job_arr_lte); rewrite leq_eqVlt; move => /orP [/eqP EQ | LT].
    - rewrite EQ.
      apply/eqP/negPn/negP; rewrite -has_filter => /hasP [j' IN /eqP TASK].
      apply mem_bigcat_nat_exists in IN; move : IN => [i [J'_IN ARR_INEQ]].
      lia.
    - apply/eqP/negPn/negP; rewrite -has_filter => /hasP [j3 IN /eqP TASK].
      apply mem_bigcat_nat_exists in IN; move : IN => [i [J3_IN ARR_INEQ]].
      have J3_ARR : (arrives_in arr_seq j3) by apply in_arrseq_implies_arrives with (t := i).
      apply job_arrival_at in J3_IN => //; rewrite -J3_IN in ARR_INEQ.
      move : ARR_INEQ => /andP [PJ_L_J3 J3_L_J].
      apply (earlier_arrival_implies_lower_index arr_seq H_valid_arrival_sequence _ _) in PJ_L_J3 => //; try by
          rewrite prev_job_task.
      + apply (earlier_arrival_implies_lower_index arr_seq H_valid_arrival_sequence _ _) in J3_L_J => //.
        by rewrite prev_job_index_j in PJ_L_J3; try lia.
      + by apply prev_job_arr.
  Qed.

  (** We show that there always exists a job of lesser [job_index] than a
   job with a positive [job_index] that arrives in the arrival sequence. *)
  Lemma exists_jobs_before_j :
    forall k,
      k < job_index arr_seq j ->
      exists j',
        j <> j'
        /\ job_task j' = job_task j
        /\ arrives_in arr_seq j'
        /\ job_index arr_seq j' = k.
  Proof.
    clear H_positive_job_index.
    intros k K_LT.
    exists (nth j (task_arrivals_up_to_job_arrival arr_seq j) k).
    set (jk := nth j (task_arrivals_up_to_job_arrival arr_seq j) k).
    have K_LT_SIZE : (k < size (task_arrivals_up_to_job_arrival arr_seq j)) by
        apply leq_trans with (n := job_index arr_seq j) => //; first by apply index_size.
    have JK_IN : (jk \in task_arrivals_up_to_job_arrival arr_seq j) by rewrite /jk; apply mem_nth => //.
    rewrite mem_filter in JK_IN; move : JK_IN => /andP [/eqP TSK JK_IN].
    apply mem_bigcat_nat_exists in JK_IN; move : JK_IN => [i [JK_IN I_INEQ]].
    have JK_ARR : (arrives_in arr_seq jk) by apply in_arrseq_implies_arrives with (t := i) => //.
    have INDJK : (index jk (task_arrivals_up_to_job_arrival arr_seq j) = k).
    { by apply: index_uniq => //; apply: uniq_task_arrivals. }
    repeat split => //.
    { rewrite -> diff_jobs_iff_diff_indices => //; eauto.
      rewrite /job_index; rewrite [in X in _ <> X] (job_index_same_in_task_arrivals _ _ jk j) => //.
      - rewrite index_uniq -/(job_index arr_seq j)=> //; last by apply uniq_task_arrivals.
        lia.
      - by apply job_arrival_at in JK_IN => //; rewrite -JK_IN in I_INEQ. }
    { rewrite /job_index; rewrite [in X in X = _] (job_index_same_in_task_arrivals _ _ jk j) => //.
      by apply job_arrival_at in JK_IN => //; rewrite -JK_IN in I_INEQ. }
  Qed.

End PreviousJob.
