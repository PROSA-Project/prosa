Require Export prosa.model.processor.supply.

(** * Average Resource Model *)

(** In this file, we define the average resource model and the corresponding
    SBF, inspired by the periodic resource model introduced in the paper
    "Periodic Resource Model for Compositional Real-Time Guarantees" by Shin &
    Lee (RTSS 2003). *)

Section AverageResourceModel.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** The supply is distributed according to the average resource model with a
      resource period [Π], a resource allocation time [Θ], and supply delay [ν]
      if, for any interval <<[t1, t2)>>, the processor provides at least
      [ (t2 - t1 - ν) * Θ / Π ] units of supply.

      This model can be thought of as follows. On average, the processor
      produces [Θ] units of output per [Π] units of time. However, the
      distribution of supply is not ideal and is subject to fluctuations defined
      by [ν].

      Furthermore, we require [Π >= Θ] to focus on unit-supply processors. *)
  Definition average_resource_model (Π Θ ν : duration) (sched : schedule PState) :=
    Π >= Θ
    /\ forall (t1 t2 : duration),
         let Δ := t2 - t1 in
         supply_during sched t1 t2 >= ((Δ - ν) * Θ) %/ Π.

End AverageResourceModel.


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
