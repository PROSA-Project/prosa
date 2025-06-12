Require Export prosa.util.all.
Require Export prosa.model.processor.platform_properties.

(** * Supply *)
(** In this file, we establish properties of the notion of supply. *)

(** We start with a few basic facts about supply. *)
Section BasicFacts.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any kind of processor state model, ... *)
  Context `{PState : ProcessorState Job}.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** First, we leverage the property [service_on_le_supply_on] to
      show that [service_at j t] is always bounded by [supply_at
      t]. *)
  Lemma service_at_le_supply_at :
    forall j t,
      service_at sched j t <= supply_at sched t.
  Proof.
    by move=> j t; apply: leq_sum => c _; apply service_on_le_supply_on.
  Qed.

  (** As a corollary, it is easy to show that if a job receives
      service at a time instant [t], then the supply at this time
      instant is positive. *)
  Corollary pos_service_impl_pos_supply :
    forall j t,
      0 < service_at sched j t ->
      0 < supply_at sched t.
  Proof.
    by move=> j t; rewrite (leqRW (service_at_le_supply_at _ _)).
  Qed.

  (** Next, we show that, at any time instant [t], either there is
      some supply available or it is a blackout time. *)
  Lemma blackout_or_supply :
    forall t,
      is_blackout sched t \/ has_supply sched t.
  Proof.
    by rewrite /is_blackout; move=> t; case: (has_supply).
  Qed.

End BasicFacts.

(** As a common special case, we establish facts about schedules in
    which supply is either 0 or 1 at all times. *)
Section UnitService.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any kind of unit-supply processor state model, ... *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** We show that, under the unit-supply assumption, [supply_at t] is
      equal to [1 - is_blackout t] for any time instant [t]. *)
  Lemma supply_at_complement :
    forall t,
      supply_at sched t = 1 - is_blackout sched t.
  Proof.
    move=> t; have := H_unit_supply_proc_model (sched t).
    by rewrite /is_blackout /has_supply /supply_at; case: supply_in => [|[]].
  Qed.

  (** Vice versa, [is_blackout t] is equal to [1 - supply_at t], up to
      the [bool]–[nat] conversion. *)
  Lemma is_blackout_complement :
    forall t,
      nat_of_bool (is_blackout sched t) = 1 - supply_at sched t.
  Proof.
    move=> t; have := H_unit_supply_proc_model (sched t).
    by rewrite /is_blackout /has_supply /supply_at; case: supply_in => [|[]].
  Qed.

  (** We note that supply is bounded at all times by [1] ... *)
  Remark supply_at_le_1 :
    forall t,
      supply_at sched t <= 1.
  Proof. by move=> t; apply H_unit_supply_proc_model. Qed.

  (** ... and as a trivial consequence, we show that the service of
      any job is either [0] or [1]. *)
  Corollary unit_supply_proc_service_case :
    forall j t,
      service_at sched j t = 0 \/ service_at sched j t = 1.
  Proof.
    move=> j t.
    have SER := service_at_le_supply_at sched j t.
    have SUP := supply_at_le_1 t.
    by lia.
  Qed.

  (** We show that supply during an interval <<[t, t + δ)>> is bounded by [δ]. *)
  Lemma supply_during_bound :
    forall t δ,
      supply_during sched t (t + δ) <= δ.
  Proof.
    move=> t d; rewrite -[leqRHS](addKn t) -[leqRHS]muln1 -sum_nat_const_nat.
    by apply: leq_sum => t0 _;  apply supply_at_le_1.
  Qed.

  (** We show that blackout during an interval <<[t, t + δ)>> is bounded by [δ]. *)
  Lemma blackout_during_bound :
    forall t δ,
      blackout_during sched t (t + δ) <= δ.
  Proof.
    move=> t d; rewrite -[leqRHS](addKn t) -[leqRHS]muln1 -sum_nat_const_nat.
    by apply: leq_sum => t0 _; destruct is_blackout.
  Qed.

  (** We observe that the supply during an interval can be decomposed
      into the last instant and the rest of the interval. *)
  Lemma supply_during_last_plus_before :
    forall t1 t2,
      t1 <= t2 ->
      supply_during sched t1 t2.+1 = supply_during sched t1 t2 + supply_at sched t2.
  Proof. by move => t1 t2 LEQ; rewrite /supply_during big_nat_recr //=. Qed.

  (** We show a similar lemma for [blackout_during]. *)
  Lemma blackout_during_last_plus_before :
    forall t1 t2,
      t1 <= t2 ->
      blackout_during sched t1 t2.+1 = blackout_during sched t1 t2 + is_blackout sched t2.
  Proof. by move => t1 t2 LEQ; rewrite /blackout_during big_nat_recr //=. Qed.

  (** We show that the service during a time interval <<[t, t + δ)>>
      is equal to the difference between [δ] and the blackout during
      <<[t, t + δ)>>. *)
  Lemma supply_during_complement :
    forall t δ,
      supply_during sched t (t + δ) = δ - blackout_during sched t (t + δ).
  Proof.
    move=> t; elim=> [|δ IHδ]; first by rewrite addn0 [LHS]big_geq.
    rewrite addnS [LHS]big_nat_recr ?leq_addr//= [X in X + _]IHδ.
    rewrite blackout_during_last_plus_before ?leq_addr// is_blackout_complement.
    have B := supply_at_le_1 (t + δ).
    by rewrite -addn1 subnACA ?blackout_during_bound; lia.
  Qed.

  (** Similarly, we show that the blackout during a time interval
      <<[t, t + δ)>> is equal to the difference between [δ] and the
      supply during <<[t, t + δ)>>. *)
  Lemma blackout_during_complement :
    forall t δ,
      blackout_during sched t (t + δ) = δ - supply_during sched t (t + δ).
  Proof.
    move=> t; elim=> [|δ IHδ]; first by rewrite addn0 [LHS]big_geq.
    rewrite addnS [LHS]big_nat_recr ?leq_addr//= [X in X + _]IHδ.
    rewrite supply_during_last_plus_before ?leq_addr// supply_at_complement.
    by rewrite -addn1 subnACA ?supply_during_bound; lia.
  Qed.

  (** The number of blackout time instants in <<[t1, t2)>> is equal to
      the sum of blackout time instants in <<[t1, t)>> and <<[t, t2)>>. *)
  Lemma blackout_during_cat :
    forall (t1 t2 t : instant),
      t1 <= t <= t2 ->
      blackout_during sched t1 t + blackout_during sched t t2 = blackout_during sched t1 t2.
  Proof.
    move=> t1 t2 t NEQ; rewrite /blackout_during.
    rewrite (index_iota_cat t t1 t2) => //.
    by rewrite big_cat //=.
  Qed.

  (** The number of blackout time instants can increase by at most 1
      when extending the interval by one unit. *)
  Lemma blackout_during_unit_growth :
    forall (t : instant),
      unit_growth_function (blackout_during sched t).
  Proof.
    move=> t1 t2.
    have UNIT :
      forall (f : nat -> nat) (t1 t2 : instant),
        (f t2 <= 1) ->
        \sum_(t1 <= t < t2 + 1) f t <= \sum_(t1 <= t < t2) f t + 1.
    { clear; intros f t1 t2; have [LE|LT] := leqP t1 t2.
      { by rewrite addn1 big_nat_recr //= leq_add2l. }
      { by rewrite big_geq // addn1. }
    }
    by apply UNIT; destruct is_blackout.
  Qed.

End UnitService.

(** Lastly, we prove one lemma about supply in the case of the fully
    supply-consuming processor model. *)
Section ConsumedSupply.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any kind of fully supply-consuming processor state model, ... *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_supply_is_fully_consumed : fully_consuming_proc_model PState.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** The fact that a job [j] is scheduled at a time instant [t] and
      there is a supply at [t] implies that the job receives service
      at time [t]. *)
  Lemma progress_inside_supplies :
    forall (j : Job) (t : instant),
      has_supply sched t ->
      scheduled_at sched j t ->
      0 < service_at sched j t.
  Proof.
    by move => j t SUP SCHED; rewrite H_supply_is_fully_consumed.
  Qed.

End ConsumedSupply.

(** We add some of the above lemmas to the "Hint Database"
    [basic_rt_facts], so the [auto] tactic will be able to use
    them. *)
Global Hint Resolve
       supply_at_le_1
  : basic_rt_facts.
