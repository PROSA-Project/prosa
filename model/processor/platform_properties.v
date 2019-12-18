Require Export prosa.behavior.all.

(** To reason about classes of schedule types / processor models, we define the
    following properties that group processor models into classes of similar
    models. *)
Section ProcessorModels.
  (** Consider any job type and any processor state.

      Note: we make the processor state an explicit variable (rather than
      implicit context) because it is the primary subject of the following
      definitions. *)
  Context {Job : JobType}.
  Variable PState : Type.
  Context `{ProcessorState Job PState}.

  (** We say that a processor model provides unit service if no job ever
      receives more than one unit of service at any time. *)
  Definition unit_service_proc_model :=
    forall (j : Job) (s : PState), service_in j s <= 1.

  (** We say that a processor model offers ideal progress if a scheduled job
      always receives non-zero service. *)
  Definition ideal_progress_proc_model :=
    forall j s, scheduled_in j s -> service_in j s > 0.

  (** In a uniprocessor model, the scheduled job is always unique. *)
  Definition uniprocessor_model :=
    forall j1 j2 s t,
      scheduled_at s j1 t ->
      scheduled_at s j2 t ->
      j1 = j2.

End ProcessorModels.
