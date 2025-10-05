Require Export prosa.behavior.all.

(** * SBF for Average Resource Model *)

(** In this section, we define an SBF for the average resource model. *)
Section AverageResourceModelSBF.

  (** Given, the average resource model with a resource period [Π], resource
      allocation time [Θ], and supply delay [ν],... *)
  Variable Π Θ ν : duration.

  (** ... we define SBF for the average resource model as [((Δ - ν) * Θ) / Π].

      Note that this SBF directly mirrors the bound given by the average
      resource model itself. This is due to the fact that the guaranteed supply
      depends only on the interval length [Δ], not on its alignment. Therefore,
      the same bound can be used as an SBF. *)
  Definition arm_sbf Δ := ((Δ - ν) * Θ) %/ Π.

End AverageResourceModelSBF.
