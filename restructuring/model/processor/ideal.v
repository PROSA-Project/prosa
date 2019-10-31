From mathcomp Require Import all_ssreflect.
From rt.restructuring.behavior Require Export all.


(** First let us define the notion of an ideal schedule state, as done in Prosa
    so far: either a job is scheduled or the system is idle. *)

Section State.

  Variable Job: JobType.

  Definition processor_state := option Job.

  Global Program Instance pstate_instance : ProcessorState Job (option Job) :=
    {
      (** As this is a uniprocessor model, cores are implicitly defined
          as the unit type containing a single element as a placeholder. *)
      scheduled_on j s (_ : unit) := s == Some j;
      service_in j s := s == Some j;
    }.
  Next Obligation.
    rewrite /nat_of_bool.
    case: ifP H=>//=_/existsP[].
    by exists tt.
  Defined.
End State.
