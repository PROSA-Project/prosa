Require Export prosa.analysis.definitions.busy_interval.
Require Export prosa.analysis.definitions.carry_in.

(** In this module we collect some basic facts about quiet times. *)

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

  (** We prove that 0 is always a quiet time. *)
  Lemma zero_is_quiet_time (j : Job) :
    quiet_time arr_seq sched j 0.
  Proof. by move=> jhp ARR HP; rewrite /arrived_before ltn0. Qed.

  (** The fact that there is no carry-in at time instant [t] trivially
      implies that [t] is a quiet time. *)
  Lemma no_carry_in_implies_quiet_time :
    forall j t,
      no_carry_in arr_seq sched t ->
      quiet_time arr_seq sched j t.
  Proof. by move=> j t + j_hp ARR HP BEF; apply. Qed.

  (** For convenience in proofs, we restate that by definition there are no
      quiet times in a busy-interval prefix... *)
  Fact busy_interval_prefix_no_quiet_time :
    forall j t1 t2,
      busy_interval_prefix arr_seq sched j t1 t2 ->
      (forall t, t1 < t < t2 -> ~ quiet_time arr_seq sched j t).
  Proof. by move=> j t1 t2 [_ [_ [NQT _]]]. Qed.

  (** ... and hence also not in a busy interval. *)
  Fact busy_interval_no_quiet_time :
    forall j t1 t2,
      busy_interval arr_seq sched j t1 t2 ->
      (forall t, t1 < t < t2 -> ~ quiet_time arr_seq sched j t).
  Proof. by move=> j t1 t2 [BIP _]; exact: busy_interval_prefix_no_quiet_time. Qed.

End Facts.
