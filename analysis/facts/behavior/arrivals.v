Require Export prosa.behavior.all.
Require Export prosa.util.all.
Require Export prosa.model.task.arrivals.

(** * Arrival Sequence *)

(** First, we relate the stronger to the weaker arrival predicates. *)
Section ArrivalPredicates.

  (** Consider any kinds of jobs with arrival times. *)
  Context {Job : JobType} `{JobArrival Job}.

  (** A job that arrives in some interval <<[t1, t2)>> certainly arrives before
      time [t2]. *)
  Lemma arrived_between_before:
    forall j t1 t2,
      arrived_between j t1 t2 ->
      arrived_before j t2.
  Proof.
    move=> j t1 t2.
    now rewrite /arrived_before /arrived_between => /andP [_ CLAIM].
  Qed.

  (** A job that arrives before a time [t] certainly has arrived by time
      [t]. *)
  Lemma arrived_before_has_arrived:
    forall j t,
      arrived_before j t ->
      has_arrived j t.
  Proof.
    move=> j t.
    rewrite /arrived_before /has_arrived.
    now apply ltnW.
  Qed.

End ArrivalPredicates.

(** In this section, we relate job readiness to [has_arrived]. *)
Section Arrived.
  
  (** Consider any kinds of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any schedule... *)
  Variable sched : schedule PState.

  (** ...and suppose that jobs have a cost, an arrival time, and a
      notion of readiness. *)
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

  (** First, we note that readiness models are by definition consistent
      w.r.t. [pending]. *)
  Lemma any_ready_job_is_pending:
    forall j t,
      job_ready sched j t -> pending sched j t.
  Proof.
    move: jr => [is_ready CONSISTENT].
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

  (** Furthermore, in a valid schedule, jobs must arrive to execute. *)
  Corollary valid_schedule_implies_jobs_must_arrive_to_execute:
    forall arr_seq, 
    valid_schedule sched arr_seq ->
    jobs_must_arrive_to_execute sched.
  Proof.
    move=> arr_seq [??].
    by apply jobs_must_arrive_to_be_ready.
  Qed.
  
  (** Since backlogged jobs are by definition ready, any backlogged job must have arrived. *)
  Corollary backlogged_implies_arrived:
    forall j t,
      backlogged sched j t -> has_arrived j t.
  Proof.
    rewrite /backlogged.
    move=> j t /andP [READY _].
    now apply ready_implies_arrived.
  Qed.

  (** Similarly, since backlogged jobs are by definition pending, any
      backlogged job must be incomplete. *)
  Lemma backlogged_implies_incomplete:
    forall j t,
      backlogged sched j t -> ~~ completed_by sched j t.
  Proof.
    move=> j t BACK.
    have suff: pending sched j t.
    - by move /andP => [_ INCOMP].
    - apply; move: BACK => /andP [READY _].
      by apply any_ready_job_is_pending.
  Qed.

End Arrived.

(** We add some of the above lemmas to the "Hint Database"
    [basic_facts], so the [auto] tactic will be able to use them. *)
Global Hint Resolve
       valid_schedule_implies_jobs_must_arrive_to_execute
       jobs_must_arrive_to_be_ready
  : basic_facts.

(** In this section, we establish useful facts about arrival sequence prefixes. *)
Section ArrivalSequencePrefix.

  (** Consider any kind of tasks and jobs. *)
  Context {Job: JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** We begin with basic lemmas for manipulating the sequences. *)
  Section Composition.

    (** We show that the set of arriving jobs can be split
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

    (** We also prove a stronger version of the above lemma 
     in the case of arrivals that satisfy a predicate [P]. *)
    Lemma arrivals_P_cat:
      forall P t t1 t2,
        t1 <= t < t2 -> 
        arrivals_between_P arr_seq P t1 t2 =
        arrivals_between_P arr_seq P t1 t ++ arrivals_between_P arr_seq P t t2.
    Proof.
      intros P t t1 t2 INEQ.
      rewrite -filter_cat.
      now rewrite -arrivals_between_cat => //; lia.
    Qed.
    
    (** The same observation applies to membership in the set of
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

    (** We observe that we can grow the considered interval without
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
    
    (** We also prove a weaker version of the above lemma. *)
    Lemma in_arrseq_implies_arrives:
      forall t j,
        j \in arr_seq t ->
        arrives_in arr_seq j.
    Proof.
      move => t j J_ARR.
      exists t.
      now rewrite /arrivals_at.
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
      now apply mem_bigcat_nat with (j := (job_arrival j)).
    Qed.
    
    (** Any job in arrivals between time instants [t1] and [t2] must arrive
       in the interval <<[t1,t2)>>. *)
    Lemma job_arrival_between:
      forall j P t1 t2,
        j \in arrivals_between_P arr_seq P t1 t2 ->
        t1 <= job_arrival j < t2.
    Proof.
      intros * ARR.
      move: ARR; rewrite mem_filter => /andP [PJ JARR].
      apply mem_bigcat_nat_exists in JARR.
      move : JARR => [i [ARR INEQ]].
      apply H_consistent_arrival_times in ARR.
      now rewrite ARR.
    Qed.
    
    (** Any job [j] is in the sequence [arrivals_between t1 t2] given
     that [j] arrives in the interval <<[t1,t2)>>. *)
    Lemma job_in_arrivals_between:
      forall j t1 t2,
        arrives_in arr_seq j ->
        t1 <= job_arrival j < t2 ->
        j \in arrivals_between arr_seq t1 t2.
    Proof.
      intros * ARR INEQ.
      apply mem_bigcat_nat with (j := job_arrival j) => //.
      move : ARR => [t J_IN].
      now rewrite -> H_consistent_arrival_times with (t := t).
    Qed.
    
    (** Next, we prove that if the arrival sequence doesn't contain duplicate
        jobs, the same applies for any of its prefixes. *)
    Lemma arrivals_uniq:
      arrival_sequence_uniq arr_seq ->
      forall t1 t2, uniq (arrivals_between arr_seq t1 t2).
    Proof.
      rename H_consistent_arrival_times into CONS.
      unfold arrivals_up_to; intros SET t1 t2.
      apply bigcat_nat_uniq; first by done.
      intros x t t' IN1 IN2.
        by apply CONS in IN1; apply CONS in IN2; subst.
    Qed.

    (** Also note that there can't by any arrivals in an empty time interval. *)
    Lemma arrivals_between_geq:
      forall t1 t2,
        t1 >= t2 ->
        arrivals_between arr_seq t1 t2  = [::].
    Proof.
        by intros ? ? GE; rewrite /arrivals_between big_geq.
    Qed.
    
    (** Given jobs [j1] and [j2] in [arrivals_between_P arr_seq P t1 t2], the fact that
        [j2] arrives strictly before [j1] implies that [j2] also belongs in the sequence
        [arrivals_between_P arr_seq P t1 (job_arrival j1)]. *)
    Lemma arrival_lt_implies_job_in_arrivals_between_P:
      forall (j1 j2 : Job) (P : Job -> bool) (t1 t2 : instant),
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
      apply H_consistent_arrival_times in J2_IN; rewrite J2_IN in ARR_LT.
      now lia.
    Qed.

  End ArrivalTimes.

End ArrivalSequencePrefix.
