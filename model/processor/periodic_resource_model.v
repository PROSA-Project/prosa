Require Export prosa.model.processor.supply.

(** * Periodic Resource Model *)

(** In this section, we define the classical periodic resource model introduced
    in paper "Periodic Resource Model for Compositional Real-Time Guarantees" by
    Shin & Lee (RTSS 2003). *)
Section PeriodicResourceModel.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** The supply is distributed according to the periodic resource model with a
      resource period [Π] and a resource allocation time [Θ] if, for any
      interval <<[Π⋅k, Π⋅(k+1))>>, the processor provides at least [Θ] units of
      supply. *)
  Definition periodic_resource_model (Π Θ : duration) (sched : schedule PState) :=
    Π > 0
    /\ Π >= Θ
    /\ forall (k : nat),
         supply_during sched (Π * k) (Π * (k + 1)) >= Θ.

End PeriodicResourceModel.
