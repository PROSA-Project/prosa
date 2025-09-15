From HB Require Import structures.
Require Export prosa.behavior.all.

(** In the following, we define a processor state model for an ideal-uniprocessor
    system with jobs possibly exhibiting exceedance. *)
Section State.

  (** For a give type of jobs ...*)
  Context `{Job : JobType}.

  (** ... the exceedance processor state is defined as follows.
      Here, the [NominalExecution] processor state refers to the state of the
      processor when it is executing some job [j]. [ExceedanceExecution] also
      refers to the state of the processor when a job is executing in addition
      to its nominal execution time. Finally, [Idle] refers to the state of the
      processor when no job is executing. *)
  Inductive exceedance_processor_state :=
  | NominalExecution (j : Job)
  | ExceedanceExecution (j : Job)
  | Idle.

  (** To efficiently use the processor state in our mechanization, we need to
      define an [eqType] for the processor state. First, we define an inequality
      on the processor state as follows. *)
  Definition exceedance_processor_state_eqdef (p1 p2 : exceedance_processor_state) : bool :=
    match p1, p2 with
    | NominalExecution j1, NominalExecution j2 => j1 == j2
    | ExceedanceExecution j1, ExceedanceExecution j2 => j1 == j2
    | Idle, Idle => true
    | _, _ => false
    end.

  (** Next, we prove that the defined notion of equality is in fact an equality. *)
  Lemma eqn_exceedance_processor_state : Equality.axiom exceedance_processor_state_eqdef.
  Proof.
    unfold Equality.axiom.
    move => s1 s2.
    destruct (exceedance_processor_state_eqdef s1 s2) eqn: EQ.
    - apply ReflectT.
      by destruct s1; destruct s2 => //=;  move : EQ => /eqP -> .
    - apply /ReflectF => EQ1.
      move : EQ => /negP. apply.
      by destruct s1; destruct s2 => //=; inversion EQ1; subst.
  Qed.

  (** Finally, we register the processor state as an [eqType]. *)
  HB.instance Definition _ := hasDecEq.Build exceedance_processor_state eqn_exceedance_processor_state.

  (** Next, we need to define the notions of service and supply for the
      processor state under consideration. *)
  Section ExceedanceService.

    (** Consider any job [j]. *)
    Variable j : Job.

    (** [j] is considered to be "scheduled" if the processor state is either
        [NominalExecution j] or [ExceedanceExecution j] *)
    Definition exceedance_scheduled_on (proc_state : exceedance_processor_state) (_ : unit)
      : bool :=
      match proc_state with
      | NominalExecution j'
      | ExceedanceExecution j' => j' == j
      | _ => false
      end.

    (** Next, we need to define in which states the processor is offering supply.
        This is required to specify in which states a processor can offer
        productive work to a job. Note that when analysing a schedule of the
        [exceedance_processor_state], we want to model all instances of
        [ExceedanceExecution] as blackouts w.r.t. to nominal service and, therefore, the supply in this
        processor state is defined to be [0]. *)
    Definition exceedance_supply_on (proc_state :  exceedance_processor_state)
      (_ : unit) : work :=
      match proc_state with
      | NominalExecution _ => 1
      | ExceedanceExecution _ => 0
      | Idle => 1
      end.

    (** Finally we need to define in which states a job actually receives
        nominal service. In our case, a job [j] receives nominal service only when the system
        is in the [NominalExecution j] state. *)
    Definition exceedance_service_on (proc_state : exceedance_processor_state) (_ : unit) : work :=
      match proc_state with
      | NominalExecution j' => j' == j
      | ExceedanceExecution _ => 0
      | Idle => 0
      end.

  End ExceedanceService.

    (** Finally we can declare our processor state as an instance of the
        [ProcessorState] typeclass. *)
  Global Program Instance exceedance_proc_state : ProcessorState Job :=
    {|
      State := exceedance_processor_state;
      scheduled_on := exceedance_scheduled_on;
      supply_on := exceedance_supply_on;
      service_on := exceedance_service_on
    |}.
  Next Obligation.
    by move => j [] // s [] /=; case: eqP; lia.
  Qed.
  Next Obligation.
    by move => j [] // s [] /=; case: eqP; lia.
  Qed.

End State.

Global Arguments exceedance_proc_state : clear implicits.
