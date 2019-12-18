Require Export prosa.analysis.transform.swap.
Require Export prosa.analysis.facts.behavior.completion.

(** In this file, we make a few simple observations about schedules with
    replacements. *)
Section ReplaceAtFacts.

  (** For any given type of jobs... *)
  Context {Job : JobType}.

  (** ... and any given type of processor states, ... *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ...consider any given reference schedule. *)
  Variable sched: schedule PState.

  (** Suppose we are given a specific time [t'] ... *)
  Variable t': instant.

  (** ...and a replacement state [state]. *)
  Variable nstate: PState.

  (** In the following, let [sched'] denote the schedule with replacement at time
     t'. *)
  Let sched' := replace_at sched t' nstate.

  (** We begin with the trivial observation that the schedule doesn't change at
      other times. *)
  Lemma rest_of_schedule_invariant:
    forall t, t <> t' -> sched' t = sched t.
  Proof.
    move => t DIFF.
    rewrite /sched' /replace_at.
    case (t' == t) eqn:TT; last by done.
    by move/eqP in TT; rewrite TT in DIFF; contradiction.
  Qed.

  (** As a result, the service in intervals that do not intersect with
      [t'] is invariant, too. *)
  Lemma service_at_other_times_invariant:
    forall t1 t2,
      t2 <= t' \/ t' < t1 ->
      forall j,
        service_during sched  j t1 t2
        =
        service_during sched' j t1 t2.
  Proof.
    move => t1 t2 SWAP_EXCLUDED j.
    rewrite /service_during /service_at.
    apply eq_big_nat => t /andP [le_t1t lt_tt2].
    rewrite rest_of_schedule_invariant//.
    eapply point_not_in_interval; eauto.
    apply /andP; by split.
  Qed.

  (** Next, we consider the amount of service received in intervals
      that do span across the replacement point.  We can relate the
      service received in the original and the new schedules by adding
      the service in the respective "missing" state... *)
  Lemma service_delta:
    forall t1 t2,
      t1 <= t' < t2 ->
      forall j,
        service_during sched  j t1 t2 + service_at sched' j t'
        =
        service_during sched' j t1 t2 + service_at sched  j t'.
  Proof.
    move => t1 t2 TIMES j.
    rewrite -(service_split_at_point sched  _ _ t' _) //
            -(service_split_at_point sched' _ _ t' _) //.
    by rewrite !service_at_other_times_invariant -/sched'; [ring | right | left].
  Qed.

  (** ...which we can also rewrite as follows. *)
  Corollary service_in_replaced:
    forall t1 t2,
      t1 <= t' < t2 ->
      forall j,
        service_during sched' j t1 t2
        =
        service_during sched  j t1 t2 + service_at sched' j t' - service_at sched j t'.
  Proof. move => t1 t2 ORDER j. by rewrite service_delta// addnK. Qed.

  (** As another simple invariant (useful for case analysis), we
      observe that if a job is scheduled neither in the replaced nor
      in the new state, then at any time it receives exactly the same
      amount of service in the new schedule with replacements as in
      the original schedule. *)
  Lemma service_at_of_others_invariant (j: Job):
    ~~ scheduled_in j (sched' t') ->
    ~~ scheduled_in j (sched t') ->
    forall t,
      service_at sched j t = service_at sched' j t.
  Proof.
    move=> NOT_IN_NEW NOT_IN_OLD t.
    rewrite /service_at.
    case: (boolP (t == t')) => /eqP TT.
    - rewrite !TT !service_implies_scheduled //; by apply negbTE.
    - rewrite rest_of_schedule_invariant//.
  Qed.

  (** Based on the previous observation, we can trivially lift the
      invariant that jobs not involved in the replacement receive
      equal service to the cumulative service received in any
      interval. *)
  Corollary service_during_of_others_invariant (j: Job):
    ~~ scheduled_in j (sched' t') ->
    ~~ scheduled_in j (sched t') ->
    forall t1 t2,
      service_during sched j t1 t2 = service_during sched' j t1 t2.
  Proof.
    move=> NOT_IN_NEW NOT_IN_OLD t1 t2.
    rewrite /service_during.
    apply eq_big_nat => t /andP [le_t1t lt_tt2].
    rewrite service_at_of_others_invariant //.
  Qed.

End ReplaceAtFacts.
