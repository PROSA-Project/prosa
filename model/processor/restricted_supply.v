Require Export prosa.behavior.all.

(** * The Restricted Supply Model *)

(** In the following, we define a processor state that includes the
    possibility of the processor becoming unavailable, where the jobs
    executing in the unavailable state do not progress (= don't get
    any service). We allow jobs to be scheduled in unavailable states
    in order to preserve work-conservation. *)
Section State.

  (** We define the state of a processor at a given time to be one of
      four possible cases: *)
  Inductive processor_state {Job : JobType} :=
  (** The processor is idle. We _could_ service a job, so we are
      wasting the capacity of the supply. *)
  | Idle
  (** A job is being executed. *)
  | Active (j : Job)
  (** A job is scheduled, but the processor is unavailable and yields
      no service. *)
  | Unavailable (j : Job)
  (** The processor is unavailable, and no job is being scheduled. *)
  | Inactive.

  (** Consider any type of jobs. *)
  Context (Job : JobType).

  (** Next, we define the semantics of the processor state with
      restricted supply. *)
  Section Service.

    (** Let [j] denote any job. *)
    Variable j : Job.

    (** It is scheduled in a given state [s] iff [j] is the job mentioned
        in the state. *)
    Definition rs_scheduled_on (s : processor_state) : bool :=
      match s with
      | Idle | Inactive => false
      | Active j' | Unavailable j' => j' == j
      end.

    (** Processor states [Idle] and [Active _] indicate that the
        processor is ready to produce [1] unit of supply. If the
        processor is in state [Unavailable _] or [Inactive], it
        produces [0] unit of work. *)
    Definition rs_supply_on (s : @processor_state Job) : work :=
      match s with
      | Idle | Active _ => 1
      | _ => 0
      end.

    (** Job [j] receives service only if the given state [s] is
        [Active j]. *)
    Definition rs_service_on (s : processor_state) : work :=
      if s is Active j'
      then if j' == j then 1 else 0
      else 0.

  End Service.

  (** Finally, we connect the above definitions with the generic Prosa
      interface for abstract processor states. *)
  Program Definition rs_processor_state : ProcessorState Job :=
    {|
      State                       := processor_state;
      scheduled_on j s (_ : unit) := rs_scheduled_on j s;
      supply_on s (_ : unit)      := rs_supply_on s;
      service_on j s (_ : unit)   := rs_service_on j s
    |}.
  Next Obligation. by move=> j s r; case s, r => //=; case: (_ == _). Qed.
  Next Obligation. by move=> j s r; case s, r => //=; case: (_ == _). Qed.

End State.
