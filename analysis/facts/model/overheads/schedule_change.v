Require Export prosa.model.processor.overheads.
Require Export prosa.analysis.definitions.overheads.schedule_change.
Require Export prosa.analysis.facts.model.overheads.schedule.

(** In this section, we prove a few basic properties about the number
    of schedule changes in a given interval. *)
Section ScheduleChange.

  (** Consider any type of jobs.. *)
  Context {Job : JobType}.

  (** ... and any schedule with explicit overheads. *)
  Variable sched : schedule (overheads.processor_state Job).

  (** The number of schedule changes over <<[t1, t2)>> is equal to the
      number of changes in <<[t1, t)>> plus the number in <<[t, t2)>>. *)
  Lemma number_schedule_changes_cat :
    forall (t t1 t2 : instant),
      t1 <= t <= t2 ->
      number_schedule_changes sched t1 t2
      = number_schedule_changes sched t1 t + number_schedule_changes sched t t2.
  Proof.
    move=> t t1 t2 NEQ.
    by rewrite /number_schedule_changes (index_iota_cat t t1 t2) // count_cat.
  Qed.

  (** If there is at least one schedule change in <<[t1, t2)>>, then
      there exists the first time <<t ∈ [t1, t2)>> where the change
      occurs, and no change happens before [t]. *)
  Lemma first_schedule_change_exists :
    forall (t1 t2 : instant) (k : nat),
      k > 0 ->
      number_schedule_changes  sched t1 t2 = k ->
      exists t,
        t1 <= t < t2
        /\ schedule_change sched t
        /\ number_schedule_changes sched t1 t = 0
        /\ number_schedule_changes sched t t2 = k.
  Proof.
    move=> t1 t2 k POS EQ.
    have EX: exists t, (fun t => (t1 <= t < t2) && schedule_change sched t) t.
    { move: POS; rewrite -EQ.
      rewrite /number_schedule_changes -has_count.
      move=>/hasP [to]; rewrite mem_index_iota => NEQo SCo.
      by exists to; rewrite SCo NEQo.
    }
    apply find_ex_minn in EX; move: EX => [t /andP [NEQ SC] MIN].
    exists t; rewrite NEQ SC; do 2 split => //.
    have ZE : number_schedule_changes sched t1 t = 0.
    { apply/eqP; rewrite -leqn0; move_neq_up NUM.
      move: NUM; rewrite /number_schedule_changes -has_count.
      move=>/hasP [to]; rewrite mem_index_iota => NEQo SCo.
      by move: (MIN to ltac:(lia)) => LE2; lia.
    }
    { by rewrite ZE; split => //; move: EQ; rewrite (number_schedule_changes_cat t); lia. }
  Qed.

  (** Widening the interval can only increase the number of schedule changes. *)
  Lemma number_schedule_changes_widen :
    forall (t1 t2 t1' t2' : instant),
      t1 <= t1' ->
      t2' <= t2 ->
      number_schedule_changes sched t1' t2'
      <= number_schedule_changes sched t1 t2.
  Proof.
    move => t1 t2 t1' t2' LE1 LE2.
    rewrite /number_schedule_changes.
    have [/eqP LE|LT] := leqP t2' t1'.
    { by rewrite /index_iota LE. }
    rewrite (index_iota_cat t1' t1 t2); last by lia.
    move: LE2; rewrite leq_eqVlt => /orP [/eqP EQ|LT2].
    { by subst; rewrite count_cat; lia. }
    { rewrite (index_iota_cat t2' t1' t2); last by lia.
      by rewrite !count_cat; lia.
    }
  Qed.

End ScheduleChange.

(** In this section, we prove properties of the predicate
    [scheduled_job_invariant]. *)
Section ScheduleInterruptions.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Next, consider any schedule of the arrival sequence where jobs don't
      execute before their arrival time. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_must_arrive : jobs_must_arrive_to_execute sched.

  (** If the processor has the same scheduled state [oj1] in <<[t1,
      t)>> and the same state [oj2] in <<[t, t2)>>, and there is no
      schedule change at time [t], then both intervals must have the
      same scheduled state [oj1 = oj2]. *)
  Lemma same_scheduled_state_merge :
    forall (t1 t2 t : instant) (oj1 oj2 : option Job),
      t1 < t < t2 ->
      ~~ schedule_change sched t ->
      scheduled_job_invariant sched oj1 t1 t ->
      scheduled_job_invariant sched oj2 t t2 ->
      oj1 = oj2.
  Proof.
    move=> t1 t2 t oj1 oj2 /andP [NEQ1 NEQ2] EQ /allP SC1 /allP SC2.
    have IN1: t.-1 \in index_iota t1 t by rewrite mem_index_iota; lia.
    have IN2: t \in index_iota t t2 by rewrite mem_index_iota; lia.
    move: (SC1 _ IN1) (SC2 _ IN2) => /eqP EQ1 /eqP EQ2.
    rewrite /schedule_change EQ1 EQ2 in EQ.
    by apply/eqP/negPn.
  Qed.

  (** If there are no schedule changes in an interval <<[t1, t2)>>,
      then the scheduled job must remain the same at every instant
      within the interval. *)
  Lemma no_schedule_changes_implies_constant_schedule :
    forall (t1 t2 t : instant),
      t1 <= t < t2 ->
      number_schedule_changes sched t1 t2 = 0 ->
      ~~ schedule_change sched t.
  Proof.
    move=> t1 t2 t NEQ => /eqP.
    rewrite -leqn0 leqNgt -has_count -all_predC => /allP IN.
    rewrite /schedule_change; apply/negPn/eqP.
    specialize (IN t).
    rewrite mem_index_iota //= in IN.
    apply/eqP/negPn/negP => NEQ2.
    rewrite /schedule_change NEQ2 in IN.
    by rewrite NEQ in IN.
  Qed.

  (** If there are no schedule changes during the interval <<[t1,
      t2)>>, then [scheduled_job] remains constant throughout the
      interval. *)
  Lemma no_changes_implies_same_scheduled_job :
    forall (t1 t2 t t' : instant) (oj : option Job),
      no_schedule_changes_during sched t1 t2 ->
      t1 <= t < t2 ->
      t1 <= t' < t2 ->
      scheduled_job sched t = oj ->
      scheduled_job sched t' = oj.
  Proof.
    move=> t1 t2 t t' oj NSC NEQ1 NEQ2 SC.
    have [A1|A2] := leqP t t'.
    { interval_to_duration t t' k.
      induction k as [ | k IHk]; first by rewrite addn0.
      rewrite addnS; rewrite addnS in NEQ2.
      feed IHk; first by lia.
      move: NSC => /eqP; rewrite /number_schedule_changes.
      move=>/eqP; rewrite -leqn0 leqNgt -has_count -all_predC => /allP NSC.
      move: (NSC (t+k).+1 ltac:(rewrite mem_index_iota; lia)); clear NSC.
      rewrite /predC /schedule_change //= negbK => /eqP EQ.
      by rewrite -EQ.
    }
    { interval_to_duration t' t k.
      induction k as [ | k IHk]; first by rewrite addn0 in SC.
      rewrite addnS in SC, NEQ2.
      feed IHk; first by lia.
      apply: IHk.
      move: NSC => /eqP; rewrite /number_schedule_changes.
      move=>/eqP; rewrite -leqn0 leqNgt -has_count -all_predC => /allP NSC.
      move: (NSC (t'+k).+1 ltac:(rewrite mem_index_iota; lia)); clear NSC.
      rewrite /predC /schedule_change //= negbK => /eqP EQ.
      by rewrite EQ.
    }
  Qed.

End ScheduleInterruptions.
