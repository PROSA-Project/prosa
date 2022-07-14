Require Export prosa.analysis.definitions.busy_interval.
  
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
  Lemma zero_is_quiet_time (j : Job) : quiet_time arr_seq sched j 0.
  Proof.
    by intros jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0.
  Qed.

End Facts.
