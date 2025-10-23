Require Export prosa.model.processor.supply.

(** * Periodic Resource Model *)

(** In this file, we define the classical periodic resource model and the
    corresponding SBF, as introduced by Shin & Lee in their paper "Periodic
    Resource Model for Compositional Real-Time Guarantees" (RTSS 2003). *)
Section PeriodicResourceModel.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** The supply is distributed according to the periodic resource model with a
      resource period [Π] and a resource allocation time [γ] if, for any
      interval <<[Π⋅k, Π⋅(k+1))>>, the processor provides at least [γ] units of
      supply. *)
  Definition periodic_resource_model (Π γ : duration) (sched : schedule PState) :=
    Π > 0
    /\ Π >= γ
    /\ forall (k : nat),
        supply_during sched (Π * k) (Π * (k + 1)) >= γ.

End PeriodicResourceModel.

(** * SBF for Periodic Resource Model *)

(** In this section, we define an SBF for the periodic resource model. *)
Section PeriodicResourceModelSBF.

  (** Given a periodic resource model with a resource period [Π] and resource
      allocation time [γ], ... *)
  Variable Π γ : duration.

  (** ... we define the corresponding SBF as introduced in "Periodic Resource
      Model for Compositional Real-Time Guarantees" by Shin & Lee (RTSS
      2003). *)
  Definition prm_sbf Δ :=
    let blackout := Π - γ in
    let n_full_periods := (Δ - blackout) %/ Π in
    let supply_in_full_periods := n_full_periods * γ in
    let duration_of_full_periods := n_full_periods * Π in
    supply_in_full_periods + (Δ - 2 * blackout - duration_of_full_periods).

End PeriodicResourceModelSBF.
