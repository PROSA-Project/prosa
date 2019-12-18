From mathcomp Require Import all_ssreflect.
Require Export prosa.behavior.all.

(** In the following, we define a model of processors with variable execution
    speeds.

    NB: For now, the definition serves only to document how this can be done;
        it is not actually used anywhere in the library.  *)

Section State.

  (** Consider any type of jobs. *)
  Variable Job: JobType.

  (** We define the state of a variable-speed processor at a given time to be
      one of two possible cases: either a specific job is scheduled and
      progresses with a specific speed, or the processor is idle. *)
  Inductive processor_state :=
    Idle
  | Progress (j : Job) (speed : nat).

  (** Next, we define the semantics of the variable-speed processor state. *)
  Section Service.

    (** Consider any job [j]. *)
    Variable j : Job.

    (** Job [j] is scheduled in a given state [s] if [s] is not idle and [j]
        matches the job recorded in [s]. *)
    Definition varspeed_scheduled_on (s : processor_state) (_ : unit) : bool :=
      match s with
      | Idle => false
      | Progress j' _  => j' == j
      end.

    (** If it is scheduled in state [s], job [j] receives service proportional
        to the speed recorded in the state. *)
    Definition varspeed_service_in (s : processor_state) : nat :=
      match s with
      | Idle => 0
      | Progress j' speed  => if j' == j then speed else 0
      end.

  End Service.

  (** Finally, we connect the above definitions to the generic Prosa interface
      for processor states. *)
  Global Program Instance pstate_instance : ProcessorState Job processor_state :=
    {
      scheduled_on := varspeed_scheduled_on;
      service_in   := varspeed_service_in
    }.
  Next Obligation.
    move: H.
    case: s=>//= j' v /existsP.
    case: ifP=>//=_[].
    by exists.
  Defined.

End State.
