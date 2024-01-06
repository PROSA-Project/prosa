Require Export prosa.behavior.job.

(** * Supply Bound Functions (SBF) *)

(** In this module, we define the notion of Supply Bound Functions
    (SBF), which can be used to reason about the minimum amount of supply
    provided in a given time interval. *)
Class SupplyBoundFunction :=
  supply_bound_function : duration -> work.
