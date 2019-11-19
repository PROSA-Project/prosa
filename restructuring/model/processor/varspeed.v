From mathcomp Require Import all_ssreflect.
Require Export rt.restructuring.behavior.all.

(** Next, let us define a schedule with variable execution speed. *)
Section State.

  Variable Job: JobType.

  Inductive processor_state :=
    Idle
  | Progress (j : Job) (speed : nat).

  Section Service.

    Variable j : Job.

    Definition scheduled_on (s : processor_state) (_ : unit) : bool :=
      match s with
      | Idle => false
      | Progress j' _  => j' == j
      end.

    Definition service_in (s : processor_state) : nat :=
      match s with
      | Idle => 0
      | Progress j' speed  => if j' == j then speed else 0
      end.

  End Service.

  Global Program Instance pstate_instance : ProcessorState Job processor_state :=
    {
      scheduled_on := scheduled_on;
      service_in   := service_in
    }.
  Next Obligation.
    move: H.
    case: s=>//= j' v /existsP.
    case: ifP=>//=_[].
    by exists.
  Defined.

End State.
