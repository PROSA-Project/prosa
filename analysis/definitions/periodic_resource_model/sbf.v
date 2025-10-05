Require Export prosa.behavior.all.

(** * SBF for Periodic Resource Model *)

(** In this section, we restate the SBF defined in paper "Periodic Resource
    Model for Compositional Real-Time Guarantees" by Shin & Lee (RTSS 2003). *)
Section PeriodicResourceModelSBF.

  (** Given a periodic resource model with a resource period [Π] and resource
      allocation time [Θ], ... *)
  Variable Π Θ : duration.

  (** ... we define the corresponding SBF as introduced in "Periodic Resource
      Model for Compositional Real-Time Guarantees" by Shin & Lee (RTSS
      2003). *)
  Definition prm_sbf Δ :=
    let blackout := Π - Θ in
    let n_full_periods := (Δ - blackout) %/ Π in
    let supply_in_full_periods := n_full_periods * Θ in
    let dulation_of_full_periods := n_full_periods * Π in
    supply_in_full_periods + (Δ - 2 * blackout - dulation_of_full_periods).

End PeriodicResourceModelSBF.
