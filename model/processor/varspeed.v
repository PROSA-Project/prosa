Require Export prosa.behavior.all.

(** In the following, we define a model of processors with variable execution
    speeds.

    NB: For now, the definition serves only to document how this can be done;
        it is not actually used anywhere in the library.  *)

Section State.

  (** Consider any type of jobs. *)
  Variable Job : JobType.

  (** We define the state of a variable-speed processor at a given
      time to be one of two possible cases: either a specific job is
      scheduled and progresses with a specific speed, or the processor
      is idle.  Here, [Idle k] denotes a scenario where the processor
      could have generated [k] units of service, but there is no job
      being scheduled at that time instant. *)
  Inductive processor_state :=
  | Idle (speed : nat)
  | Progress (j : Job) (speed : nat).

  (** Next, we define the semantics of the variable-speed processor state. *)
  Section Service.

    (** Consider any job [j]. *)
    Variable j : Job.

    (** The job scheduled in a given state [s] is the job recorded as
        progressing in [s]. *)
    Definition varspeed_job_on (s : processor_state) (_ : unit) : option Job :=
      match s with
      | Idle _ => None
      | Progress j' _ => Some j'
      end.

    (** The processor state [Idle k] indicates that the processor is
        ready to produce [k] units of supply; however, no job is
        scheduled. If the processor is in state [Progress j k], it
        produces [k] units of work at a given time instant. *)
    Definition varspeed_supply_on (s : processor_state) (_ : unit) : work :=
      match s with
      | Idle k => k
      | Progress j' k => k
      end.

    (** If it is scheduled in state [s], job [j] receives service
        proportional to the speed recorded in the state. *)
    Definition varspeed_service_on (s : processor_state) (_ : unit) : work :=
      match s with
      | Idle _ => 0
      | Progress j' speed => if j' == j then speed else 0
      end.

  End Service.

  (** Finally, we connect the above definitions to the generic Prosa
      interface for processor states. *)
  Program Definition pstate_instance : ProcessorState Job :=
    {|
      State        := processor_state;
      job_on       := varspeed_job_on;
      supply_on    := varspeed_supply_on;
      service_on   := varspeed_service_on
    |}.
  Next Obligation.
    by move=> j [] //= s; case: eqP.
  Qed.
  Next Obligation.
    by move=> j [] //= j' v _; rewrite (inj_eq Some_inj); case: ifP.
  Qed.

End State.
