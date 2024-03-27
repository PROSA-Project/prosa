Require Export prosa.analysis.definitions.busy_interval.classical.

(** In this module we collect some basic facts about arrival times in busy
    windows. These are primarily useful for proof automation. *)

Section Facts.

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

End Facts.

(** We add the above facts into the "Hint Database" basic_rt_facts, so Coq will
    be able to apply them automatically where needed. *)
Global Hint Resolve
  busy_interval_prefix_job_arrival
  busy_interval_job_arrival
  : basic_rt_facts.
