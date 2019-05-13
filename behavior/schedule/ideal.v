From rt.behavior Require Export schedule.schedule.

(** First let us define the notion of an ideal schedule state,
 *  as done in Prosa so far: either a job is scheduled or the system is idle.
 *)

Section State.

  Variable Job: eqType.

  Definition processor_state := option Job.

  Global Instance pstate_instance : ProcessorState Job (option Job) :=
    {
      scheduled_in j s := s == Some j;
      service_in j s   := s == Some j
    }.
  Proof.
      by move=> j [j'->|].
  Qed.
End State.
