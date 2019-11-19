From mathcomp Require Import all_ssreflect.
Require Export rt.restructuring.behavior.all.

(** Next we define a processor state that includes the possibility of spinning,
    where spinning jobs do not progress (= don't get service). *)
Section State.

  Variable Job: JobType.

  Inductive processor_state :=
    Idle
  | Spin (j : Job)
  | Progress (j : Job).

  Section Service.

    Variable j : Job.

    Definition scheduled_on (s : processor_state) (_ : unit) : bool :=
      match s with
      | Idle        => false
      | Spin j'     => j' == j
      | Progress j' => j' == j
      end.

    Definition service_in (s : processor_state) : nat :=
      match s with
      | Idle        => 0
      | Spin j'     => 0
      | Progress j' => j' == j
      end.

  End Service.

  Global Program Instance pstate_instance : ProcessorState Job (processor_state) :=
    {
      scheduled_on := scheduled_on;
      service_in   := service_in
    }.
  Next Obligation.
    move: H.
    case: s=>//= j' /existsP.
    rewrite /nat_of_bool.
    case: ifP=>//=_[].
    by exists.
  Defined.
End State.
