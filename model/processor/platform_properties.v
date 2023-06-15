Require Export prosa.behavior.all.
Require Export prosa.model.processor.supply.

(** To reason about classes of schedule types / processor models, we define the
    following properties that group processor models into classes of similar
    models. *)
Section ProcessorModels.
  (** Consider any job type and any processor state.

      Note: we make the processor state an explicit variable (rather than
      implicit context) because it is the primary subject of the following
      definitions. *)
  Context {Job : JobType}.
  Variable PState : ProcessorState Job.

  (** We say that a processor model provides unit service if no job ever
      receives more than one unit of service at any time. *)
  Definition unit_service_proc_model :=
    forall (j : Job) (s : PState), service_in j s <= 1.

  (** We say that a processor model offers ideal progress if a scheduled job
      always receives non-zero service. *)
  Definition ideal_progress_proc_model :=
    forall (j : Job) (s : PState),
      scheduled_in j s -> service_in j s > 0.

  (** In a uniprocessor model, the scheduled job is always unique. *)
  Definition uniprocessor_model :=
    forall (j1 j2 : Job) (s : schedule PState) (t : instant),
      scheduled_at s j1 t ->
      scheduled_at s j2 t ->
      j1 = j2.

  (** We say that a processor model is a unit-supply model if no state
      ever produces more than one unit of supply at any time. *)
  Definition unit_supply_proc_model :=
    forall (s : PState), supply_in s <= 1.

  (** Note that [unit_supply_proc_model] implies
      [unit_service_proc_model] because of the requirement
      [service_on_le_supply_on]. But not vice versa --- a unit-service
      processor model is not necessarily a unit-supply processor
      model. *)
  Remark unit_supply_is_unit_service :
    unit_supply_proc_model ->
    unit_service_proc_model.
  Proof.
    move=> USUP j s; move: (USUP s).
    apply leq_trans, leq_sum => r _.
    by apply service_on_le_supply_on.
  Qed.

  (** We say that a processor model is a fully consuming processor
      model if a job scheduled at time [t] receives the entire supply
      produced at that time as service. *)
  Definition fully_consuming_proc_model :=
    forall (j : Job) (s : schedule PState) (t : instant),
      scheduled_at s j t -> service_at s j t = supply_at s t.

End ProcessorModels.
