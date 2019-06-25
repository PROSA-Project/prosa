From rt.restructuring.behavior.schedule Require Export schedule.

(** Next, let us define a schedule with variable execution speed. *)
Section State.

  Variable Job: JobType.

  Inductive processor_state :=
    Idle
  | Progress (j : Job) (speed : nat).

  Section Service.

    Variable j : Job.

    Definition scheduled_in (s : processor_state) : bool :=
      match s with
      | Idle => false
      | Progress j' _  => j' == j
      end.

    Definition service_in (s : processor_state) : nat :=
      match s with
      | Idle => 0
      | Progress j' s  => if j' == j then s else 0
      end.

  End Service.

  Global Instance pstate_instance : ProcessorState Job processor_state :=
    {
      scheduled_in := scheduled_in;
      service_in   := service_in
    }.
  Proof.
      by move=> j []//= j' s->.
  Defined.
End State.
