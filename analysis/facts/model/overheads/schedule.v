Require Import prosa.model.processor.overheads.
Require Export prosa.analysis.facts.busy_interval.pi.

(** In this section, we prove a few basic properties of the processor
    model with explicit overheads. *)
Section OverheadsProceProperties.

  (** We assume schedules with explicit overheads. *)
  #[local] Existing Instance overheads.processor_state.

  Local Transparent scheduled_on service_on.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** First, we prove that the processor model with overheads is
      a uni-processor model. *)
  Lemma overheads_proc_model_is_a_uniprocessor_model :
    uniprocessor_model (overheads.processor_state Job).
  Proof.
    move=> j1 j2 sched t; rewrite /scheduled_at /scheduled_in/ scheduled_on/=.
    move=> /existsP [[] /eqP H1] /existsP [[] /eqP H2].
    by apply: Some_inj; rewrite -H1 -H2.
  Qed.

  (** The processor model with overheads is a unit-supply model. *)
  Lemma overheads_proc_model_provides_unit_supply :
    unit_supply_proc_model (overheads.processor_state Job).
  Proof.
    rewrite /unit_supply_proc_model.
    move=> s; rewrite /supply_in sum_unit1.
    by case: s.
  Qed.

  (** We also show that the processor model is fully consuming. That
      is, if a job is scheduled at time [t], then it receives the
      entire supply produced at that time as service. *)
  Lemma overheads_proc_model_fully_consuming :
    fully_consuming_proc_model (overheads.processor_state Job).
  Proof.
    move=> j sched t.
    rewrite /service_at /supply_at /service_in /supply_in.
    rewrite /scheduled_at /scheduled_in /scheduled_on /=.
    move=> /existsP [[] /eqP OH1].
    apply: eq_bigr => r _.
    move: OH1; case: (sched t) => [| oj1 oj2 | oj | j'' | j'] //= OH1.
    move: OH1; rewrite /overheads_job_on /= => /Some_inj ->.
    by rewrite eqxx /overheads_supply_on.
  Qed.

End OverheadsProceProperties.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Rocq
    will be able to apply them automatically. *)
Global Hint Resolve
       overheads_proc_model_is_a_uniprocessor_model
       overheads_proc_model_provides_unit_supply
       overheads_proc_model_fully_consuming
  : basic_rt_facts.

(** In this section, we prove basic properties of schedules with
    explicit overheads. *)
Section OverheadScheduleProperties.

  (** We assume schedules with explicit overheads. *)
  #[local] Existing Instance overheads.processor_state.

  Local Transparent scheduled_on.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any schedule with explicit overheads. *)
  Variable sched : schedule (overheads.processor_state Job).

  (** At any time [t], either the processor is idle (no job is
      scheduled), or some job is scheduled at that time. *)
  Lemma scheduled_job_dec :
    forall t,
      scheduled_job sched t = None \/ exists j, scheduled_job sched t = Some j.
  Proof.
    by intros; destruct (scheduled_job _).
  Qed.

  (** We next prove that the predicate [scheduled_at] and the function
      [scheduled_job] agree. *)
  Lemma scheduled_at_iff_scheduled_job :
    forall j t,
      scheduled_at sched j t <-> scheduled_job sched t = Some j.
  Proof.
    move=> j t; rewrite /scheduled_at /scheduled_job /scheduled_in /scheduled_on.
    split.
    - by move=> /existsP [[]] /eqP.
    - by move=> EQ; apply/existsP; exists tt; rewrite -EQ.
  Qed.

End OverheadScheduleProperties.

(** In this section, we show that, in the stated model with overheads,
    there are no idle times within a busy interval. *)
Section ScheduledInBusyPrefix.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Consider any arrival sequence with consistent non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider a schedule, ... *)
  Variable sched : schedule (overheads.processor_state Job).

  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context {RM : JobReady Job (overheads.processor_state Job)}.
  Hypothesis H_job_ready : work_bearing_readiness RM arr_seq sched.

  (** ... and assume that the schedule is valid and work-conserving. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Consider an arbitrary job [j] with positive cost. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variables t1 t2 : instant.
  Hypothesis H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** Then, we prove that, for every time instant within the busy
      interval prefix, some job is scheduled. *)
  Lemma job_scheduled_in_busy_interval_prefix :
    forall t,
      t1 <= t < t2 ->
      exists jo,
        scheduled_at sched jo t.
  Proof.
    move=> t NEQ.
    have [NON|[jo SOM]] := scheduled_job_dec sched t.
    { exfalso; apply: instant_t_is_not_idle => //.
      apply/eqP; apply filter_in_pred0 => s IN; apply/negP => SCHED.
      apply scheduled_at_iff_scheduled_job in SCHED.
      by rewrite NON in SCHED.
    }
    { by apply scheduled_at_iff_scheduled_job in SOM; exists jo. }
  Qed.

End ScheduledInBusyPrefix.
