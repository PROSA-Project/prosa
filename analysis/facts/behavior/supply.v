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

  (** We show that supply during an interval <<[t, t + δ)>> is bounded
      by [δ]. *)
  Lemma supply_at_le_1 :
    forall t,
      supply_at sched t <= 1.
  Proof. by move=> t; apply H_unit_supply_proc_model. Qed.

  (** We show that supply during an interval <<[t, t + δ)>> is bounded
      by [δ]. *)
  Lemma supply_during_bound :
    forall t δ,
      supply_during sched t (t + δ) <= δ.
  Proof.
    move=> t d; rewrite -[leqRHS](addKn t) -[leqRHS]muln1 -sum_nat_const_nat.
    by apply: leq_sum => t0 _;  apply supply_at_le_1.
  Qed.

  (** We observe that the supply during an interval can be decomposed
      into the last instant and the rest of the interval. *)
  Lemma supply_during_last_plus_before :
    forall t1 t2,
      t1 <= t2 ->
      supply_during sched t1 t2.+1 = supply_during sched t1 t2 + supply_at sched t2.
  Proof. by move => t1 t2 LEQ; rewrite /supply_during big_nat_recr //=. Qed.

  (** Finally, we show that the blackout during a time interval <<[t,
      t + δ)>> is equal to the difference between [δ] and the supply
      during <<[t, t + δ)>>. *)
  Lemma blackout_during_complement :
    forall t δ,
      blackout_during sched t (t + δ) = δ - supply_during sched t (t + δ).
  Proof.
    move=> t; elim=> [|δ IHδ]; first by rewrite addn0 [LHS]big_geq.
    rewrite addnS [LHS]big_nat_recr ?leq_addr//= [X in X + _]IHδ.
    rewrite supply_during_last_plus_before ?leq_addr// supply_at_complement.
    by rewrite -addn1 subnACA ?supply_during_bound; lia.
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
