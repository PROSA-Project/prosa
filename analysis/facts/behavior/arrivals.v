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
  Proof. by move=> ? ? ? /andP[]. Qed.

  (** A job that arrives before a time [t] certainly has arrived by time
      [t]. *)
  Lemma arrived_before_has_arrived:
    forall j t,
      arrived_before j t ->
      has_arrived j t.
  Proof. move=> ? ?; exact: ltnW. Qed.

  (** Furthermore, we restate a common hypothesis to make its
      implication easier to discover. *)
  Lemma consistent_times_valid_arrival :
    forall arr_seq,
      valid_arrival_sequence arr_seq -> consistent_arrival_times arr_seq.
  Proof. by move=> ? []. Qed.

  (** We restate another common hypothesis to make its implication
      easier to discover. *)
  Lemma uniq_valid_arrival :
    forall arr_seq,
      valid_arrival_sequence arr_seq -> arrival_sequence_uniq arr_seq.
  Proof. by move=> ? []. Qed.

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
  Proof. move: jr => [? +] /= ?; exact. Qed.

  (** Next, we observe that a given job must have arrived to be ready... *)
  Lemma ready_implies_arrived :
    forall j t, job_ready sched j t -> has_arrived j t.
  Proof. by move=> ? ? /any_ready_job_is_pending => /andP[]. Qed.

  (** ...and lift this observation also to the level of whole schedules. *)
  Lemma jobs_must_arrive_to_be_ready:
    jobs_must_be_ready_to_execute sched -> jobs_must_arrive_to_execute sched.
  Proof. move=> READY ? ? ?; exact/ready_implies_arrived/READY. Qed.

  (** Furthermore, in a valid schedule, jobs must arrive to execute. *)
  Corollary valid_schedule_implies_jobs_must_arrive_to_execute :
    forall arr_seq,
      valid_schedule sched arr_seq -> jobs_must_arrive_to_execute sched.
  Proof. move=> ? [? ?]; exact: jobs_must_arrive_to_be_ready. Qed.

  (** Since backlogged jobs are by definition ready, any backlogged job must have arrived. *)
  Corollary backlogged_implies_arrived:
    forall j t,
      backlogged sched j t -> has_arrived j t.
  Proof. move=> ? ? /andP[? ?]; exact: ready_implies_arrived. Qed.

  (** Similarly, since backlogged jobs are by definition pending, any
      backlogged job must be incomplete. *)
  Lemma backlogged_implies_incomplete:
    forall j t,
      backlogged sched j t -> ~~ completed_by sched j t.
  Proof. by move=> ? ? /andP[/any_ready_job_is_pending /andP[]]. Qed.

  (** Finally, we restate common hypotheses on the well-formedness of
      schedules to make their implications more easily
      discoverable. First, on the readiness of scheduled jobs, ... *)
  Lemma job_scheduled_implies_ready :
    jobs_must_be_ready_to_execute sched ->
    forall j t,
      scheduled_at sched j t -> job_ready sched j t.
  Proof. exact. Qed.

  (** ... second, on the origin of scheduled jobs, and ... *)
  Lemma valid_schedule_jobs_come_from_arrival_sequence :
    forall arr_seq,
      valid_schedule sched arr_seq ->
      jobs_come_from_arrival_sequence sched arr_seq.
  Proof. by move=> ? []. Qed.

  (** ... third, on the readiness of jobs in valid schedules. *)
  Lemma valid_schedule_jobs_must_be_ready_to_execute :
    forall arr_seq,
      valid_schedule sched arr_seq -> jobs_must_be_ready_to_execute sched.
  Proof. by move=> ? []. Qed.

End Arrived.

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
    Proof. by move=> ? ? ? ? ?; rewrite -big_cat_nat. Qed.

    (** We also prove a stronger version of the above lemma
     in the case of arrivals that satisfy a predicate [P]. *)
    Lemma arrivals_P_cat:
      forall P t t1 t2,
        t1 <= t < t2 ->
        arrivals_between_P arr_seq P t1 t2 =
        arrivals_between_P arr_seq P t1 t ++ arrivals_between_P arr_seq P t t2.
    Proof.
      move=> P t t1 t2.
      by move=> /andP[? ?]; rewrite -filter_cat -arrivals_between_cat// ltnW.
    Qed.

    (** The same observation applies to membership in the set of
         arrived jobs. *)
    Lemma arrivals_between_mem_cat:
      forall j t1 t t2,
        t1 <= t ->
        t <= t2 ->
        j \in arrivals_between arr_seq t1 t2 =
        (j \in arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2).
    Proof. by move=> ? ? ? ? ? ?; rewrite -arrivals_between_cat. Qed.

    (** We observe that we can grow the considered interval without
         "losing" any arrived jobs, i.e., membership in the set of arrived jobs
         is monotonic. *)
    Lemma arrivals_between_sub :
      forall j t1 t1' t2 t2',
        t1' <= t1 ->
        t2 <= t2' ->
        j \in arrivals_between arr_seq t1 t2 ->
        j \in arrivals_between arr_seq t1' t2'.
    Proof.
      move=> j t1 t1' t2 t2' t1'_le_t1 t2_le_t2' j_in.
      have /orP[t2_le_t1|t1_le_t2] := leq_total t2 t1.
      { by move: j_in; rewrite /arrivals_between big_geq. }
      rewrite (arrivals_between_mem_cat _ _ t1)// ?mem_cat.
      2:{ exact: leq_trans t2_le_t2'. }
      rewrite [X in _ || X](arrivals_between_mem_cat _ _ t2)// mem_cat.
      by rewrite j_in orbT.
    Qed.

  End Composition.

  (** Next, we relate the arrival prefixes with job arrival times. *)
  Section ArrivalTimes.

    (** Assume that job arrival times are consistent. *)
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

    (** To make the hypothesis and its implication easier to discover,
        we restate it as a trivial lemma. *)
    Lemma job_arrival_arrives_at :
      forall {j t},
        arrives_at arr_seq j t -> job_arrival j = t.
    Proof. exact: H_consistent_arrival_times. Qed.

    (** Similarly, to simplify subsequent proofs, we restate the
        [H_consistent_arrival_times] assumption as a trivial
        corollary. *)
    Lemma job_arrival_at :
      forall {j t},
        j \in arrivals_at arr_seq t -> job_arrival j = t.
    Proof. exact: H_consistent_arrival_times. Qed.

    (** Next, we  prove that if [j] is a part of the arrival sequence,
        then the converse of the above also holds. *)
    Lemma job_in_arrivals_at :
      forall j t,
        arrives_in arr_seq j ->
        job_arrival j = t ->
        j \in arrivals_at arr_seq t.
    Proof.
      move => j t [t' IN] => /eqP.
      apply contraTT => /negP NOTIN.
      apply /neqP => ARR.
      have ARR' := (H_consistent_arrival_times _ t' IN).
      by move: IN; rewrite -ARR' ARR.
    Qed.

    (** To begin with actual properties, we observe that any job in
        the set of all arrivals between time instants [t1] and [t2]
        must arrive in the interval <<[t1,t2)>>. *)
    Lemma job_arrival_between :
      forall {j t1 t2},
        j \in arrivals_between arr_seq t1 t2 -> t1 <= job_arrival j < t2.
    Proof. by move=> ? ? ? /mem_bigcat_nat_exists[i [/job_arrival_at <-]]. Qed.

    (** For convenience, we restate the left bound of the above lemma... *)
    Corollary job_arrival_between_ge :
      forall {j t1 t2},
        j \in arrivals_between arr_seq t1 t2 -> t1 <= job_arrival j.
    Proof. by move=> ? ? ? /job_arrival_between/andP[]. Qed.

    (** ... as well as the right bound separately as corollaries. *)
    Corollary job_arrival_between_lt :
      forall {j t1 t2},
        j \in arrivals_between arr_seq t1 t2 -> job_arrival j < t2.
    Proof. by move=> ? ? ? /job_arrival_between/andP[]. Qed.

    (** Consequently, if we filter the list of arrivals in an interval
        <<[t1,t2)>> with an arrival-time threshold less than [t1], we are
        left with an empty list. *)
    Lemma arrivals_between_filter_nil :
      forall t1 t2 t,
        t < t1 ->
        [seq j <- arrivals_between arr_seq t1 t2 | job_arrival j < t] = [::].
    Proof.
      move=> t1 t2 t LT.
      case: (leqP t1 t2) => RANGE;
        last by rewrite /arrivals_between big_geq //=; lia.
      rewrite filter_in_pred0 // => j IN.
      rewrite -ltnNge.
      apply: (ltn_trans LT).
      rewrite ltnS.
      by apply: job_arrival_between_ge; eauto.
    Qed.

    (** Furthermore, if we filter the list of arrivals in an interval
        <<[t1,t2)>> with an arrival-time threshold less than [t2],
        we can simply discard the tail past the threshold. *)
    Lemma arrivals_between_filter :
      forall t1 t2 t,
        t <= t2 ->
        arrivals_between arr_seq t1 t
        = [seq j <- arrivals_between arr_seq t1 t2 | job_arrival j < t].
    Proof.
      move=> t1 t2 t LE2.
      case: (leqP t1 t2) => RANGE;
        last by rewrite /arrivals_between !big_geq //=; lia.
      case: (leqP t1 t) => LE1;
        last by rewrite [LHS]/arrivals_between big_geq; try lia; rewrite arrivals_between_filter_nil.
      rewrite /arrivals_between bigcat_nat_filter_eq_filter_bigcat_nat.
      rewrite (big_cat_nat _ _ _ LE1 LE2) //=.
      rewrite !big_nat [X in _ ++ X]big1; last first.
      { move=> t' /andP[LO HI].
        rewrite filter_in_pred0 // => j IN.
        have -> : job_arrival j = t' by apply: job_arrival_at; eauto.
        rewrite -leqNgt.
        exact: LO. }
      { rewrite cats0.
        apply: eq_bigr => t' /andP[LO HI].
        apply esym.
        apply /all_filterP/allP => j IN.
        have -> : job_arrival j = t' by apply: job_arrival_at; eauto.
        exact: HI. }
    Qed.

    (** Next, we prove that if a job belongs to the prefix
        (jobs_arrived_before t), then it arrives in the arrival
        sequence. *)
    Lemma in_arrivals_implies_arrived:
      forall j t1 t2,
        j \in arrivals_between arr_seq t1 t2 ->
        arrives_in arr_seq j.
    Proof. by move=> ? ? ? /mem_bigcat_nat_exists[arr [? _]]; exists arr. Qed.

    (** We also prove a weaker version of the above lemma. *)
    Lemma in_arrseq_implies_arrives:
      forall t j,
        j \in arr_seq t ->
        arrives_in arr_seq j.
    Proof. by move=> t ? ?; exists t. Qed.

    (** Next, we prove that if a job belongs to the prefix
         (jobs_arrived_between t1 t2), then it indeed arrives between t1 and
         t2. *)
    Lemma in_arrivals_implies_arrived_between:
      forall j t1 t2,
        j \in arrivals_between arr_seq t1 t2 ->
        arrived_between j t1 t2.
    Proof. by move=> ? ? ? /mem_bigcat_nat_exists[t0 [/job_arrival_at <-]]. Qed.

    (** Similarly, if a job belongs to the prefix (jobs_arrived_before t),
           then it indeed arrives before time t. *)
    Lemma in_arrivals_implies_arrived_before:
      forall j t,
        j \in arrivals_before arr_seq t ->
        arrived_before j t.
    Proof. by move=> ? ? /in_arrivals_implies_arrived_between. Qed.

    (** Similarly, we prove that if a job from the arrival sequence arrives
        before t, then it belongs to the sequence (jobs_arrived_before t). *)
    Lemma arrived_between_implies_in_arrivals:
      forall j t1 t2,
        arrives_in arr_seq j ->
        arrived_between j t1 t2 ->
        j \in arrivals_between arr_seq t1 t2.
    Proof.
      move=> j t1 t2 [a_j arrj] before; apply: mem_bigcat_nat (arrj).
      by rewrite -(job_arrival_at arrj).
    Qed.

    (** Any job in arrivals between time instants [t1] and [t2] must arrive
       in the interval <<[t1,t2)>>. *)
    Lemma job_arrival_between_P:
      forall j P t1 t2,
        j \in arrivals_between_P arr_seq P t1 t2 ->
        t1 <= job_arrival j < t2.
    Proof.
      move=> j P t1 t2.
      rewrite mem_filter => /andP[Pj /mem_bigcat_nat_exists[i [+ iitv]]].
      by move=> /job_arrival_at ->.
    Qed.

    (** Any job [j] is in the sequence [arrivals_between t1 t2] given
     that [j] arrives in the interval <<[t1,t2)>>. *)
    Lemma job_in_arrivals_between:
      forall j t1 t2,
        arrives_in arr_seq j ->
        t1 <= job_arrival j < t2 ->
        j \in arrivals_between arr_seq t1 t2.
    Proof.
      move=> j t1 t2 [t jarr] jitv; apply: mem_bigcat_nat (jarr).
      by rewrite -(job_arrival_at jarr).
    Qed.

    (** Next, we prove that if the arrival sequence doesn't contain duplicate
        jobs, the same applies for any of its prefixes. *)
    Lemma arrivals_uniq:
      arrival_sequence_uniq arr_seq ->
      forall t1 t2, uniq (arrivals_between arr_seq t1 t2).
    Proof.
      move=> SET t1 t2; apply: bigcat_nat_uniq => // j t1' t2'.
      by move=> /job_arrival_at <- /job_arrival_at <-.
    Qed.

    (** Also note that there can't by any arrivals in an empty time interval. *)
    Lemma arrivals_between_geq:
      forall t1 t2,
        t1 >= t2 ->
        arrivals_between arr_seq t1 t2  = [::].
    Proof. by move=> ? ? ?; rewrite /arrivals_between big_geq. Qed.

    (** Conversely, if a job arrives, the considered interval is non-empty. *)
    Corollary arrivals_between_nonempty :
      forall t1 t2 j,
        j \in arrivals_between arr_seq t1 t2 -> t1 < t2.
    Proof. by move=> j1 j2 t; apply: contraPltn=> LEQ; rewrite arrivals_between_geq. Qed.

    (** Given jobs [j1] and [j2] in [arrivals_between_P arr_seq P t1 t2], the fact that
        [j2] arrives strictly before [j1] implies that [j2] also belongs in the sequence
        [arrivals_between_P arr_seq P t1 (job_arrival j1)]. *)
    Lemma arrival_lt_implies_job_in_arrivals_between_P :
      forall (j1 j2 : Job) (P : Job -> bool) (t1 t2 : instant),
        j1 \in arrivals_between_P arr_seq P t1 t2 ->
        j2 \in arrivals_between_P arr_seq P t1 t2 ->
        job_arrival j2 < job_arrival j1 ->
        j2 \in arrivals_between_P arr_seq P t1 (job_arrival j1).
    Proof.
      move=> j1 j2 P t1 t2.
      rewrite !mem_filter => /andP[_ j1arr] /andP[Pj2 j2arr] arr_lt.
      rewrite Pj2/=; apply: job_in_arrivals_between.
      - exact: in_arrivals_implies_arrived j2arr.
      - by rewrite (job_arrival_between_ge j2arr).
    Qed.


    (** We observe that, by construction, the sequence of arrivals is
        sorted by arrival times. To this end, we first define the
        order relation. *)
    Definition by_arrival_times (j1 j2 : Job) : bool := job_arrival j1 <= job_arrival j2.

    (** Trivially, the arrivals at any one point in time are ordered
        w.r.t. arrival times. *)
    Lemma arrivals_at_sorted :
      forall t,
        sorted by_arrival_times (arrivals_at arr_seq t).
    Proof.
      move=> t.
      have AT_t : forall j, j \in (arrivals_at arr_seq t) -> job_arrival j = t
        by move=> j; apply job_arrival_at.
      case: (arrivals_at arr_seq t) AT_t => // j' js AT_t.
      apply /(pathP j') => i LT.
      rewrite /by_arrival_times !AT_t //;
        last by apply mem_nth; auto.
      rewrite in_cons; apply /orP; right.
      by exact: mem_nth.
   Qed.

    (** By design, the list of arrivals in any interval is sorted. *)
    Lemma arrivals_between_sorted :
      forall t1 t2,
        sorted by_arrival_times (arrivals_between arr_seq t1 t2).
    Proof.
      move=> t1 t2.
      rewrite /arrivals_between.
      elim: t2 => [|t2 SORTED];
        first by rewrite big_nil.
      case: (leqP t1 t2) => T1T2;
        last by rewrite big_geq.
      rewrite (big_cat_nat _ _ _ T1T2 _) //=.
      case A1: (\cat_(t1<=t<t2)arrivals_at arr_seq t) => [|j js];
        first by rewrite cat0s big_nat1; exact: arrivals_at_sorted.
      have CAT : path by_arrival_times j (\cat_(t1<=t<t2)arrivals_at arr_seq t ++ \cat_(t2<=i<t2.+1)arrivals_at arr_seq i).
      { rewrite cat_path; apply /andP; split.
        { move: SORTED. rewrite /sorted A1 => PATH_js.
          by rewrite /path -/(path _ _ js) /by_arrival_times; apply /andP; split. }
        { rewrite big_nat1.
          case A2: (arrivals_at arr_seq t2) => // [j' js'].
          apply path_le with (x' := j').
          { by rewrite /transitive/by_arrival_times; lia. }
          { rewrite /by_arrival_times.
            have -> : job_arrival j' = t2
              by apply job_arrival_at; rewrite A2; apply mem_head.
            set L := (last j (\cat_(t1<=t<t2)arrivals_at arr_seq t)).
            have EX : exists t', L \in arrivals_at arr_seq t' /\ t1 <= t' < t2
              by apply mem_bigcat_nat_exists; rewrite /L A1 last_cons; exact: mem_last.
            move: EX => [t' [IN /andP [t1t' t't2]]].
            have -> : job_arrival L = t' by apply job_arrival_at.
            by lia. }
          { move: (arrivals_at_sorted t2); rewrite /sorted A2 => PATH'.
            rewrite /path -/(path _ _ js') {1}/by_arrival_times.
            by apply /andP; split => //. } } }
      by move: CAT; rewrite /sorted A1 cat_cons {1}/path -/(path _ _ (js ++ _)) => /andP [_ CAT].
   Qed.

  End ArrivalTimes.

End ArrivalSequencePrefix.

(** In this section, we establish a few auxiliary facts about the
    relation between the property of being scheduled and arrival
    predicates to facilitate automation. *)
Section ScheduledImpliesArrives.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any job arrival sequence with consistent arrivals, .... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Next, consider a job [j] ... *)
  Variable j : Job.

  (** ... which is scheduled at a time instant [t]. *)
  Variable t : instant.
  Hypothesis H_scheduled_at : scheduled_at sched j t.

  (** Then we show that [j] arrives in [arr_seq]. *)
  Lemma arrives_in_jobs_come_from_arrival_sequence :
    arrives_in arr_seq j.
  Proof.
    by apply: H_jobs_come_from_arrival_sequence H_scheduled_at.
  Qed.

  (** Job [j] has arrived by time instant [t]. *)
  Lemma arrived_between_jobs_must_arrive_to_execute :
    has_arrived j t.
  Proof.
    by apply: H_jobs_must_arrive_to_execute H_scheduled_at.
  Qed.

  (** For any future time [t'], job [j] arrives before [t']. *)
  Lemma arrivals_before_scheduled_at :
    forall t',
      t < t' ->
      j \in arrivals_before arr_seq t'.
  Proof.
    move=> t' LTtt'.
    apply: arrived_between_implies_in_arrivals => //.
    apply: leq_ltn_trans LTtt'.
    by apply: arrived_between_jobs_must_arrive_to_execute.
  Qed.

  (** Similarly, job [j] arrives up to time [t'] for any [t'] such that [t <= t']. *)
  Lemma arrivals_up_to_scheduled_at :
    forall t',
      t <= t' ->
      j \in arrivals_up_to arr_seq t'.
  Proof.
    by move=> t' LEtt'; apply arrivals_before_scheduled_at; lia.
  Qed.

End ScheduledImpliesArrives.

(** We add some of the above lemmas to the "Hint Database"
    [basic_rt_facts], so the [auto] tactic will be able to use them. *)
Global Hint Resolve
       any_ready_job_is_pending
       arrivals_before_scheduled_at
       arrivals_uniq
       arrived_between_implies_in_arrivals
       arrived_between_jobs_must_arrive_to_execute
       arrives_in_jobs_come_from_arrival_sequence
       backlogged_implies_arrived
       job_scheduled_implies_ready
       jobs_must_arrive_to_be_ready
       jobs_must_arrive_to_be_ready
       ready_implies_arrived
       valid_schedule_implies_jobs_must_arrive_to_execute
       valid_schedule_jobs_come_from_arrival_sequence
       valid_schedule_jobs_must_be_ready_to_execute
       uniq_valid_arrival
       consistent_times_valid_arrival
       job_arrival_arrives_at
  : basic_rt_facts.
