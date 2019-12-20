Require Export prosa.behavior.all.
Require Export prosa.util.all.

(** * Arrival Sequence *)

(** In this section, we relate job readiness to [has_arrived]. *)
Section Arrived.
  
  (** Consider any kinds of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any schedule... *)
  Variable sched : schedule PState.

  (** ...and suppose that jobs have a cost, an arrival time, and a
      notion of readiness. *)
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobReady Job PState}.

  (** First, we note that readiness models are by definition consistent
      w.r.t. [pending]. *)
  Lemma any_ready_job_is_pending:
    forall j t,
      job_ready sched j t -> pending sched j t.
  Proof.
    move: H5 => [is_ready CONSISTENT].
    move=> j t READY.
    apply CONSISTENT.
    by exact READY.
  Qed.

  (** Next, we observe that a given job must have arrived to be ready... *)
  Lemma ready_implies_arrived:
    forall j t, job_ready sched j t -> has_arrived j t.
  Proof.
    move=> j t READY.
    move: (any_ready_job_is_pending j t READY).
    by rewrite /pending => /andP [ARR _].
  Qed.

  (** ...and lift this observation also to the level of whole schedules. *)
  Lemma jobs_must_arrive_to_be_ready:
    jobs_must_be_ready_to_execute sched ->
    jobs_must_arrive_to_execute sched.
  Proof.
    rewrite /jobs_must_be_ready_to_execute /jobs_must_arrive_to_execute.
    move=> READY_IF_SCHED j t SCHED.
    move: (READY_IF_SCHED j t SCHED) => READY.
    by apply ready_implies_arrived.
  Qed.

End Arrived.

(** In this section, we establish useful facts about arrival sequence prefixes. *)
Section ArrivalSequencePrefix.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** We begin with basic lemmas for manipulating the sequences. *)
  Section Composition.

    (** First, we show that the set of arriving jobs can be split
         into disjoint intervals. *)
    Lemma arrivals_between_cat:
      forall t1 t t2,
        t1 <= t ->
        t <= t2 ->
        arrivals_between arr_seq t1 t2 =
        arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2.
    Proof.
      unfold arrivals_between; intros t1 t t2 GE LE.
        by rewrite (@big_cat_nat _ _ _ t).
    Qed.

    (** Second, the same observation applies to membership in the set of
         arrived jobs. *)
    Lemma arrivals_between_mem_cat:
      forall j t1 t t2,
        t1 <= t ->
        t <= t2 ->
        j \in arrivals_between arr_seq t1 t2 =
        (j \in arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2).
    Proof.
        by intros j t1 t t2 GE LE; rewrite (arrivals_between_cat _ t).
    Qed.

    (** Third, we observe that we can grow the considered interval without
         "losing" any arrived jobs, i.e., membership in the set of arrived jobs
         is monotonic. *)
    Lemma arrivals_between_sub:
      forall j t1 t1' t2 t2',
        t1' <= t1 ->
        t2 <= t2' ->
        j \in arrivals_between arr_seq t1 t2 ->
        j \in arrivals_between arr_seq t1' t2'.
    Proof.
      intros j t1 t1' t2 t2' GE1 LE2 IN.
      move: (leq_total t1 t2) => /orP [BEFORE | AFTER];
                                  last by rewrite /arrivals_between big_geq // in IN.
      rewrite /arrivals_between.
      rewrite -> big_cat_nat with (n := t1); [simpl | by done | by apply: (leq_trans BEFORE)].
      rewrite mem_cat; apply/orP; right.
      rewrite -> big_cat_nat with (n := t2); [simpl | by done | by done].
        by rewrite mem_cat; apply/orP; left.
    Qed.

  End Composition.

  (** Next, we relate the arrival prefixes with job arrival times. *)
  Section ArrivalTimes.

    (** Assume that job arrival times are consistent. *)
    Hypothesis H_consistent_arrival_times:
      consistent_arrival_times arr_seq.

    (** First, we prove that if a job belongs to the prefix
         (jobs_arrived_before t), then it arrives in the arrival sequence. *)
    Lemma in_arrivals_implies_arrived:
      forall j t1 t2,
        j \in arrivals_between arr_seq t1 t2 ->
        arrives_in arr_seq j.
    Proof.
      rename H_consistent_arrival_times into CONS.
      intros j t1 t2 IN.
      apply mem_bigcat_nat_exists in IN.
      move: IN => [arr [IN _]].
        by exists arr.
    Qed.

    (** Next, we prove that if a job belongs to the prefix
         (jobs_arrived_between t1 t2), then it indeed arrives between t1 and
         t2. *)
    Lemma in_arrivals_implies_arrived_between:
      forall j t1 t2,
        j \in arrivals_between arr_seq t1 t2 ->
        arrived_between j t1 t2.
    Proof.
      rename H_consistent_arrival_times into CONS.
      intros j t1 t2 IN.
      apply mem_bigcat_nat_exists in IN.
      move: IN => [t0 [IN /= LT]].
        by apply CONS in IN; rewrite /arrived_between IN.
    Qed.

    (** Similarly, if a job belongs to the prefix (jobs_arrived_before t),
           then it indeed arrives before time t. *)
    Lemma in_arrivals_implies_arrived_before:
      forall j t,
        j \in arrivals_before arr_seq t ->
        arrived_before j t.
    Proof.
      intros j t IN.
      have: arrived_between j 0 t by apply in_arrivals_implies_arrived_between.
        by rewrite /arrived_between /=.
    Qed.

    (** Similarly, we prove that if a job from the arrival sequence arrives
         before t, then it belongs to the sequence (jobs_arrived_before t). *)
    Lemma arrived_between_implies_in_arrivals:
      forall j t1 t2,
        arrives_in arr_seq j ->
        arrived_between j t1 t2 ->
        j \in arrivals_between arr_seq t1 t2.
    Proof.
      rename H_consistent_arrival_times into CONS.
      move => j t1 t2 [a_j ARRj] BEFORE.
      have SAME := ARRj; apply CONS in SAME; subst a_j.
        by apply mem_bigcat_nat with (j := (job_arrival j)).
    Qed.

    (** Next, we prove that if the arrival sequence doesn't contain duplicate
         jobs, the same applies for any of its prefixes. *)
    Lemma arrivals_uniq :
      arrival_sequence_uniq arr_seq ->
      forall t1 t2, uniq (arrivals_between arr_seq t1 t2).
    Proof.
      rename H_consistent_arrival_times into CONS.
      unfold arrivals_up_to; intros SET t1 t2.
      apply bigcat_nat_uniq; first by done.
      intros x t t' IN1 IN2.
        by apply CONS in IN1; apply CONS in IN2; subst.
    Qed.

    (** Also note there can't by any arrivals in an empty time interval. *)
    Lemma arrivals_between_geq:
      forall t1 t2,
        t1 >= t2 ->
        arrivals_between arr_seq t1 t2  = [::].
    Proof.
        by intros ? ? GE; rewrite /arrivals_between big_geq.
    Qed.
    
  End ArrivalTimes.

End ArrivalSequencePrefix. 