Require Import prosa.model.processor.ideal_uni_exceed.
Require Export prosa.model.processor.platform_properties.

(** In the following section, we prove some general properties about the
    ideal uniprocessor with exceedance processor state. *)
Section ExceedanceProcStateProperties.

  (** In this section, we consider any type of jobs. *)
  Context `{Job : JobType}.

  (** First we prove that the processor state provides unit supply. *)
  Lemma eps_is_unit_supply : unit_supply_proc_model (exceedance_proc_state Job).
  Proof.
    rewrite /unit_supply_proc_model.
    move => s.
    destruct s => //=.
    all : by rewrite /supply_in //=;rewrite sum_unit1.
  Qed.

  (** The usually opaque predicates are made transparent for this section
      to enable us to prove some processor properties. *)
  Local Transparent scheduled_in scheduled_on service_on.

  (** A job [j] is said to be [scheduled_at] some time [t] if and only if the
      processor state at that time is [NominalExecution j] or
      [ExceedanceExecution j]. *)
   Lemma scheduled_at_procstate (sched : schedule (exceedance_proc_state Job)) j t:
    scheduled_at sched j t <->
      sched t = NominalExecution j \/ sched t = ExceedanceExecution j.
  Proof.
    split.
    - move => /existsP [c SCHEDON].
      destruct (sched t); try done.
      + by left; move : SCHEDON => /eqP <-.
      + by right; move : SCHEDON => /eqP <-.
    - rewrite /scheduled_at.
      by move => [-> | -> ]; rewrite /scheduled_in /scheduled_on //=; apply /existsP.
  Qed.


  (** Next we prove that the processor model under consideration is a uniprocessor
      model i.e., only one job can be scheduled at any time instant. *)
  Lemma eps_is_uniproc : uniprocessor_model (exceedance_proc_state Job).
  Proof.
    move => j1 j2 sched t /existsP [? SCHED1] /existsP [? SCHED2].
    destruct (sched t) eqn: EQ; try done.
    - by move : SCHED1 => /eqP <-; move : SCHED2 => /eqP <-.
    - by move : SCHED1 => /eqP <-; move : SCHED2 => /eqP <-.
  Qed.

  (** Next, we prove that the processor model under consideration is fully
      consuming i.e., all the supply offered is consumed by the scheduled job. *)
  Lemma eps_is_fully_consuming :
    fully_consuming_proc_model (exceedance_proc_state Job).
  Proof.
    rewrite /fully_consuming_proc_model.
    move => j sched t SCHED1.
    rewrite /scheduled_at /scheduled_in in SCHED1.
    apply scheduled_at_procstate in SCHED1.
    move : SCHED1 => [SCHED1 | SCHED1].
    - by rewrite /service_at /service_in /exceedance_service_on /supply_at /supply_in
      !/exceedance_service_on //= SCHED1 sum_unit1 // sum_unit1 //
      /exceedance_service_on /exceedance_supply_on eq_refl.
    - by rewrite /service_at /service_in /exceedance_service_on /supply_at /supply_in
        !/exceedance_service_on //= SCHED1 sum_unit1 // sum_unit1 //
        /exceedance_service_on /exceedance_supply_on eq_refl.
  Qed.

  (** Finally we prove that the processor model under consideration is unit
      service i.e., it provides at most one unit of service at any time instant. *)
  Lemma eps_is_unit_service : unit_service_proc_model (exceedance_proc_state Job).
  Proof.
    move => j pstate.
    rewrite /service_in /service_on //= sum_unit1 /exceedance_service_on.
    destruct pstate =>//=.
    by apply leq_b1.
  Qed.

End ExceedanceProcStateProperties.

(** Next, we prove some general properties specific to the
    ideal uniprocessor with exceedance processor state. *)
Section ExceedanceProcStateProperties1.

  (** In this section we consider any type of jobs. *)
  Context `{Job : JobType}.

  (** First let us define the notion of exceedance execution. A processor state
      is said to be an exceedance execution state if is equal to
      [ExceedanceExecution j] for some [j]. *)
  Definition is_exceedance_exec (pstate : (exceedance_proc_state Job)) :=
    match pstate with
    | ExceedanceExecution _ => true
    | _ => false
    end.

  (** Next, let us consider any schedule of the [exceedance_proc_state]. *)
  Variable sched : schedule (exceedance_proc_state Job).

  (** We prove that the schedule being in blackout at any time [t] is equivalent
      to the processor state at [t] being an exceedance execution state. *)
  Lemma blackout_implies_exceedance_execution t :
    is_blackout sched t = is_exceedance_exec (sched t).
  Proof.
    rewrite /is_blackout /has_supply /supply_at /supply_in
    /is_exceedance_exec //= sum_unit1 /exceedance_supply_on.
    destruct (sched t) eqn : PSTATE; try done.
  Qed.

End ExceedanceProcStateProperties1.

Global Hint Resolve
  eps_is_uniproc
  eps_is_unit_supply
  eps_is_fully_consuming
  : basic_rt_facts.
