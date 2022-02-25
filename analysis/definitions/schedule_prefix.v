Require Export prosa.behavior.ready.
Require Export prosa.util.nat.

(** We define the notion of prefix-equivalence of schedules. *)

Section PrefixDefinition.

  (** For any type of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor model, ... *)
  Context {PState: ProcessorState Job}.

  (** ... two schedules share an identical prefix if they are pointwise
          identical (at least) up to a fixed horizon. *)
  Definition identical_prefix (sched sched' : schedule PState) (horizon : instant) :=
    forall t,
      t < horizon ->
      sched t = sched' t.

  (** In other words, two schedules with a shared prefix are completely
      interchangeable w.r.t. whether a job is scheduled (in the prefix). *)
  Fact identical_prefix_scheduled_at:
    forall sched sched' h,
      identical_prefix sched sched' h ->
      forall j t,
        t < h ->
        scheduled_at sched j t = scheduled_at sched' j t.
  Proof.
    move=> sched sched' h IDENT j t LT_h.
    now rewrite /scheduled_at (IDENT t LT_h).
  Qed.

  (** Trivially, any prefix of an identical prefix is also an identical
      prefix. *)
  Fact identical_prefix_inclusion:
    forall sched sched' h,
      identical_prefix sched sched' h ->
      forall h',
        h' <= h ->
        identical_prefix sched sched' h'.
  Proof.
    move=> sched sched' h IDENT h' INCL t LT_h'.
    apply IDENT.
    now apply (leq_trans LT_h').
  Qed.

End PrefixDefinition.
