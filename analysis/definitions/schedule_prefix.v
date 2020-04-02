Require Export prosa.behavior.ready.

(** We define the notion of prefix-equivalence of schedules. *)

Section PrefixDefinition.

  (** For any type of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor model, ... *)
  Context {PState: Type} `{ProcessorState Job PState}.

  (** ... two schedules share an identical prefix if they are pointwise
          identical (at least) up to a fixed horizon. *)
  Definition identical_prefix (sched sched' : schedule PState) (horizon : instant) :=
    forall t,
      t < horizon ->
      sched t = sched' t.

End PrefixDefinition.
