From rt.restructuring.behavior Require Export schedule.

(** First let us define the notion of an ideal schedule state, as done in Prosa
    so far: either a job is scheduled or the system is idle. *)

Section State.

  Variable Job: JobType.

  Definition processor_state := option Job.

  Global Program Instance pstate_instance : ProcessorState Job (option Job) :=
    {
      scheduled_in j s := s == Some j;
      service_in j s   := s == Some j;
    }.
  Next Obligation.
    by rewrite H.
  Defined.
End State.
