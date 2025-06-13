Require Export prosa.analysis.definitions.busy_interval.classical.
Require Export prosa.analysis.facts.busy_interval.hep_at_pt.

(** In this section, we collect some basic facts about arrival times
    in busy windows. These are primarily useful for proof
    automation. *)
Section BasicFacts.

  (** Consider any kind of jobs... *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.
  (** ... and a [JLFP] policy defined on these jobs. *)
  Context `{JLFP_policy Job}.

  (** Consider any processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any schedule and arrival sequence. *)
  Variable sched : schedule PState.
  Variable arr_seq : arrival_sequence Job.

  (** We note the trivial fact that, by definition, a job arrives after the
      beginning of its busy-interval prefix ... *)
  Fact busy_interval_prefix_job_arrival :
    forall j t t',
      busy_interval_prefix arr_seq sched j t t' ->
      t <= job_arrival j.
  Proof. by move=> ? ? ? [_ [_ [_ /andP [GEQ _]]]]. Qed.

  (** ... and hence also after the beginning of its busy interval. *)
  Fact busy_interval_job_arrival :
    forall j t t',
      busy_interval arr_seq sched j t t' ->
      t <= job_arrival j.
  Proof.
    move=> ? ? ? [PREFIX _].
    by eauto using busy_interval_prefix_job_arrival.
  Qed.

End BasicFacts.

(** We add the above facts into the "Hint Database" basic_rt_facts, so Coq will
    be able to apply them automatically where needed. *)
Global Hint Resolve
  busy_interval_prefix_job_arrival
  busy_interval_job_arrival
  : basic_rt_facts.

(** In the following section, we prove additional, more involved
    properties about arrival times within busy intervals. *)
Section Facts.

  (** Consider any kind of jobs... *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.

  (** ... and a reflexive [JLFP] policy defined on these jobs. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_JLFP_reflexive : reflexive_job_priorities JLFP.

  (** Consider any processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence with consistent non-duplicate arrivals *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an arbitrary job [j] with positive cost. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** The start of a busy interval prefix [t1] must coincide with the
      arrival of some job [j_a] that has a priority higher than or
      equal to [j]. *)
  Lemma busy_prefix_starts_when_hep_job_arrives :
    forall (t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      exists j_a, arrives_at arr_seq j_a t1 /\ hep_job j_a j.
  Proof.
    move=> t1 t2 BUSY.
    have NEQ: t1 <= t1 < t2 by move: (BUSY) => [LT _]; lia.
    edestruct pending_hp_job_exists as [jh [ARR [PEND HEP]]]; (try exact BUSY) => //.
    exists jh; split; last by done.
    apply job_in_arrivals_at => //; apply/eqP.
    rewrite eqn_leq; apply/andP; split.
    { by move: PEND => /andP [A _]; rewrite /has_arrived in A; apply A. }
    { move_neq_up EA.
      move: (BUSY) => [_ [QT _]]; move: (QT _ ARR HEP EA) => COMPL.
      by rewrite /pending COMPL andbF in PEND.
    }
  Qed.

End Facts.
