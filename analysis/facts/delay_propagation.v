Require Export prosa.analysis.definitions.delay_propagation.
Require Export prosa.analysis.facts.behavior.arrivals.

(** *  Propagation of Delays in Arrival Curves *)

(** In this module, we prove properties of the generic delay propagation
    definitions provided in [prosa.analysis.definitions.delay_propagation]. *)

Section ACPropFacts.

  (** Consider two kinds of tasks... *)
  Context {Task1 Task2 : TaskType}.

  (** ... and their associated kinds of jobs. *)
  Context {Job1 Job2 : JobType}
    `{JobTask Job1 Task1} `{JobTask Job2 Task2}
    (JA1 : JobArrival Job1) (JA2 : JobArrival Job2).

  (** Suppose we are given a mapping of jobs (resp., tasks) of the second kind
      to jobs (resp., tasks) of the first kind. *)
  Variable job1_of : Job2 -> Job1.
  Variable task1_of : Task2 -> Task1.

  (** Furthermore, suppose we also have a reverse mapping from jobs of the first
      kind to the associated jobs of the second kind. *)
  Variable job2_of : Job1 -> seq Job2.

  (** The relation of the jobs is as follows: a job [j2 : Job2] arrives exactly
      [arrival_delay j2] time units after the arrival of its corresponding job
      [job1_of j2], where the maximum possible delay is bounded by [delay_bound
      (job_task j2)]. *)
  Variable arrival_delay : Job2 -> duration.
  Variable delay_bound : Task2 -> duration.

  (** Consider any set of type-two tasks. *)
  Variable ts2 : seq Task2.

  (** If the mapping of type-two tasks to type-one tasks is valid for the tasks
      in the considered task set, ... *)
  Hypothesis H_valid_mapping :
    valid_delay_propagation_mapping
      JA1 JA2 job1_of task1_of delay_bound ts2.

  (** ... and we are given an arrival curve for the first kind of tasks, ... *)
  Context {max_arrivals1 : MaxArrivals Task1}.

  (** ... then we obtain a derived (or propagated) arrival curve for tasks of
      the second kind.  *)
  #[local] Instance  max_arrivals2 : MaxArrivals Task2 :=
    propagated_arrival_curve task1_of delay_bound.

  (** Additionally, given an arbitrary arrival sequence of type-one jobs, *)
  Variable arr_seq1 : arrival_sequence Job1.

  (** ... if the mapping of type-two jobs to type-one jobs is valid, ... *)
  Hypothesis H_arr_seq_mapping :
    valid_arr_seq_propagation_mapping
      JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2.

  (** ... it induces a derived arrival sequence of type-two jobs.  *)
  Let arr_seq2 := propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay.

  (** ** Arrival Sequence Validity Properties *)

  (** In the following, we establish that the derived arrival sequence is
      structurally valid. *)

  (** First, the induced arrival sequence is consistent with the arrival times
      of type-two jobs. *)
  Lemma consistent_propagated_arrival_sequence :
    consistent_arrival_times arr_seq2.
  Proof.
    move=> j2 t.
    rewrite /arrives_at/arrivals_at/arr_seq2/propagated_arrival_sequence.
    rewrite mem_filter => /andP[/eqP <- _].
    by move: H_arr_seq_mapping => [_ _ _ {}].
  Qed.

  (** Second, the induced arrival sequence does not duplicate any jobs. *)
  Lemma propagated_arrival_sequence_uniq :
    valid_arrival_sequence arr_seq1 ->
    arrival_sequence_uniq arr_seq2.
  Proof.
    move=> VALID t.
    rewrite /arrivals_at/arr_seq2/propagated_arrival_sequence.
    apply: filter_uniq.
    rewrite /flatten foldrE big_map big_seq.
    apply: bigcat_uniq.
    - move=> j1 IN.
      move: H_arr_seq_mapping => [_ UNIQ _ _]; apply UNIQ.
      apply: in_arrivals_implies_arrived.
      exact: IN.
    - move=> j2 j1 j1'.
      move: H_arr_seq_mapping => [CON _ _ _].
      by rewrite !CON => -> ->.
    - by apply: arrivals_uniq.
  Qed.

  (** Taken together, the above two lemmas imply that the derived arrival
      sequence is valid if the reference arrival sequence is valid. *)
  Corollary valid_propagated_arrival_sequence :
    valid_arrival_sequence arr_seq1 ->
    valid_arrival_sequence arr_seq2.
  Proof.
    split; first exact: consistent_propagated_arrival_sequence.
    exact: propagated_arrival_sequence_uniq.
  Qed.

  (** A job of the second kind [j2 : Job2] is part of the derived arrival
      sequence if its associated job of the first kind [job1_of j2] is part of
      the given reference arrival sequence. *)
  Lemma arrives_in_propagated_if :
    forall j2,
      consistent_arrival_times arr_seq1 ->
      arrives_in arr_seq1 (job1_of j2) -> arrives_in arr_seq2 j2.
  Proof.
    move=> j2 CAT1 IN; move: (IN) => [t IN'].
    exists (t + arrival_delay j2).
    rewrite /arrivals_at/arr_seq2/propagated_arrival_sequence.
    rewrite mem_filter; apply/andP; split;
      first by rewrite (CAT1 _ t).
    apply/flatten_mapP.
    exists (job1_of j2).
    - apply: job_in_arrivals_between => //.
      by rewrite (CAT1 _ t) //; lia.
    - by move: H_arr_seq_mapping => [-> _].
  Qed.

  (** Conversely, a job of the second kind [j2 : Job2] is part of the derived
      arrival sequence _only if_ its associated job of the first kind [job1_of
      j2] is part of the given reference arrival sequence. *)
  Lemma arrives_in_propagated_only_if :
    forall j2,
      arrives_in arr_seq2 j2 -> arrives_in arr_seq1 (job1_of j2).
  Proof.
    move=> j2 [t2 {}].
    rewrite /arrivals_at/arr_seq2/propagated_arrival_sequence.
    rewrite mem_filter => /andP[/eqP DEF /flatten_mapP[j1 IN1 {}]].
    move: H_arr_seq_mapping => [-> _ _ _] ->.
    by apply/in_arrivals_implies_arrived/IN1.
  Qed.


  (** ** Correctness of the Propagated Arrival Curve *)

  (** Next, we establish the correctness of the propagated arrival curve. *)

  (** To this end, we first observe that the defined function satisfies the
      structural requirements for arrival curves. *)
  Lemma propagated_arrival_curve_valid :
    (forall tsk2, tsk2 \in ts2 -> monotone leq (@max_arrivals Task1 max_arrivals1 (task1_of tsk2))) ->
    valid_taskset_arrival_curve ts2 max_arrivals2.
  Proof.
    move=> MONO tsk2 IN2.
    split => // delta1 delta2 LEQ.
    case: delta1 LEQ; case: delta2 => //= delta2 delta1 LEQ.
    apply: MONO => //.
    by lia.
  Qed.

  (** In the following, let [ts1] denote the set of type-one tasks that the
      type-two tasks in [ts2] are mapped to (by [task1_of]). *)
  Let ts1 := [seq task1_of tsk2 | tsk2 <- ts2].

  (** To establish correctness, we make the assumption that each job of the
      first kind has at most one associated job of the second kind.

      Generalizations to multiple successors are possible, but the current
      definition of [propagated_arrival_curve] works only under this
      restriction. *)
  Hypothesis H_job2_of_singleton :
    (forall tsk1,
        tsk1 \in ts1 ->
        forall j1,
          job_task j1 = tsk1 ->
          size (job2_of j1) <= 1).

  (** Suppose the given type-one arrival sequence and arrival curve are
      valid. *)
  Hypothesis H_valid_arr_seq : valid_arrival_sequence arr_seq1.
  Hypothesis H_valid_ac : valid_taskset_arrival_curve ts1 max_arrivals1.

  (** In preparation of the correctness argument, we next establish a couple of
      "stepping stone" lemmas that sketch the main thrust of the correctness
      argument. *)
  Section ArrivalCurveCorrectnessSteps.

    (** Consider an interval <<[t1, t2)>> ... *)
    Variable t1 t2 : instant.
    Hypothesis H_ordered : t1 <= t2.

    (** ... and any type-two task in the given task set.  *)
    Variable tsk2 : Task2.
    Hypothesis H_in_ts : tsk2 \in ts2.

    (** Let [tsk2_arrivals] denote the jobs of [tsk2] that arrive in the
        interval <<[t1, t2)>> ... *)
    Let tsk2_arrivals := task_arrivals_between arr_seq2 tsk2 t1 t2.

    (** ... and let [trigger_jobs] denote the corresponding type-one jobs. *)
    Let trigger_jobs := [seq job1_of j2 | j2 <- tsk2_arrivals].

    (** First, note that the arrival times of the jobs in [trigger_jobs]
        necessarily fall into the window <<[t1 - delay_bound tsk2, t2)>>. *)
    Lemma trigger_job_arrival_bounded :
      forall j1,
        j1 \in trigger_jobs ->
        (t1 - delay_bound tsk2) <= job_arrival j1 < t2.
    Proof.
      move: H_arr_seq_mapping => [_ _ BOUND DEF].
      move=> j1 /mapP [j2] /[!mem_filter] /andP [SRC2 ARR2] EQ.
      move: SRC2; rewrite /job_of_task => /eqP SRC2.
      have /andP[j2t1 j2t2]:  t1 <= job_arrival j2 < t2.
      { apply: job_arrival_between; last exact: ARR2.
        exact: consistent_propagated_arrival_sequence. }
      have BARR2: job_arrival j2 = job_arrival j1 + arrival_delay j2
        by rewrite EQ; apply: DEF.
      suff: arrival_delay j2 <= delay_bound tsk2; first by lia.
      rewrite -SRC2; apply: BOUND.
      - by rewrite SRC2.
      - exact/arrives_in_propagated_only_if/in_arrivals_implies_arrived.
    Qed.

    (** Let [tsk1] denote the associated type-one task of [tsk1]... *)
    Let tsk1 := task1_of tsk2.

    (** ... and let [tsk1_arrivals] denote its jobs in the window during which
        triggering jobs may arrive. *)
    Let tsk1_arrivals := task_arrivals_between arr_seq1 tsk1 (t1 - delay_bound tsk2) t2.

    (** The triggering jobs are hence a subset of all of [tsk1]'s arrivals. *)
    Lemma subset_trigger_jobs :
      {subset trigger_jobs <= tsk1_arrivals}.
    Proof.
      move=> j1 IN.
      move: (IN) => /mapP [j2 /[!mem_filter]/andP[] TSK2 SRC2 MAP].
      apply/andP; split.
      { move: H_valid_mapping => [CONS _].
        move: TSK2; rewrite /tsk1 /job_of_task MAP => /eqP <-.
        by apply/eqP/CONS. }
      { have /andP[Hge Hlt] := trigger_job_arrival_bounded j1 IN.
        apply : job_in_arrivals_between => // /[!MAP].
        exact/arrives_in_propagated_only_if/in_arrivals_implies_arrived. }
    Qed.

    (** Additionally, from the assumption that each type-one job has at most one
        type-two successor ([H_job2_of_singleton]), we have that [job1_of] is
        injective (for the jobs in the arrival sequence).  *)
    Lemma job1_of_inj : {in tsk2_arrivals &, injective [eta job1_of]}.
    Proof.
      move=> j2 j2' IN2 IN2' EQ.
      move: H_valid_mapping => [CONS _].
      move: H_arr_seq_mapping => [CONS' _ _ _].
      have SIZE: size (job2_of (job1_of j2')) <= 1.
      { apply: (H_job2_of_singleton (task1_of (job_task j2'))).
        - rewrite /ts1 map_f //.
          by move: IN2'; rewrite mem_filter /job_of_task => /andP [/eqP-> _].
        - exact: CONS. }
      have: j2' \in job2_of (job1_of j2') by rewrite CONS'.
      move: SIZE (EQ); rewrite -CONS'.
      case: (job2_of _) => [//|j2'' tail].
      case: tail => // _.
      by rewrite !mem_seq1 => /eqP-> /eqP->.
    Qed.

    (** Finally, the sequence of triggering jobs contains no duplicates since it
        is part of the valid arrival sequence [arr_seq1]. *)
    Lemma uniq_trigger_jobs : uniq trigger_jobs.
    Proof.
      rewrite map_inj_in_uniq; last exact: job1_of_inj.
      rewrite filter_uniq //.
      apply: arrivals_uniq.
      - exact: consistent_propagated_arrival_sequence.
      - exact: propagated_arrival_sequence_uniq.
    Qed.

    (** Taken together, the above facts allow us to conclude that the magnitude
        of [trigger_jobs] is upper-bounded by the total number of jobs released
        by [tsk1] during <<[t1 - delay_bound tsk2, t2]>>, i.e., the count of
        jobs in [tsk1_arrivals]. *)
    Corollary trigger_job_size : size trigger_jobs <= size tsk1_arrivals.
    Proof.
      apply: uniq_leq_size.
      - exact: uniq_trigger_jobs.
      - exact: subset_trigger_jobs.
    Qed.

  End ArrivalCurveCorrectnessSteps.


  (** Assuming that the given arrival sequence for type-one tasks correctly
      bounds the arrivals of triggering jobs, [trigger_job_size] implies that
      the derived arrival curve correctly bounds the arrivals of type-two job
      since [size tsk1_arrivals] is then bounded by the given arrival curve
      [max_arrivals1]. *)
  Theorem propagated_arrival_curve_respected :
    taskset_respects_max_arrivals arr_seq1 ts1 ->
    taskset_respects_max_arrivals arr_seq2 ts2.
  Proof.
    move=> RESP1 tsk2 IN2 t1 t2 LEQ.
    have IN1 : task1_of tsk2 \in ts1 by rewrite /ts1 map_f.
    rewrite /max_arrivals/max_arrivals2/propagated_arrival_curve
              /number_of_task_arrivals/task_arrivals_between.
    case DELTA: (t2 - t1) => [|D];
      first by rewrite arrivals_between_geq //=; lia.
    rewrite -DELTA => {D} {DELTA}.
    rewrite -(size_map job1_of) //.
    apply: leq_trans; first exact: trigger_job_size.
    apply (@leq_trans (max_arrivals (task1_of tsk2)
                         (t2 - (t1 - delay_bound tsk2)))).
    - rewrite -/(number_of_task_arrivals _ _ (t1 - delay_bound tsk2) t2).
      by apply: (RESP1 _ IN1); lia.
    - move: (H_valid_ac _ IN1) => [_ MONO].
      by apply: MONO; lia.
  Qed.

End ACPropFacts.

