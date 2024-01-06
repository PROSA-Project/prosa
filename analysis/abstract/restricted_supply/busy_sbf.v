Require Export prosa.util.all.
Require Export prosa.analysis.definitions.sbf.pred.
Require Export prosa.analysis.abstract.definitions.

(** * SBF within Abstract Busy Interval *)

(** In the following, we define a weak notion of a supply bound
    function, which is a valid SBF only within an abstract busy
    interval of a job. *)
Section BusySupplyBoundFunctions.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any kind of processor state model, ... *)
  Context `{PState : ProcessorState Job}.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume we are provided with abstract functions for Interference
      and Interfering Workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** We say that the SBF is respected in an (abstract) busy interval
      if, for any busy interval <<[t1, t2)>> and a subinterval <<[t1,
      t) ⊆ [t1, t2)>>, at least [SBF (t - t1)] cumulative supply is
      provided. *)
  Definition sbf_respected_in_busy_interval (SBF : duration -> work) :=
    pred_sbf_respected sched (busy_interval_prefix sched) SBF.

  (** Next, we define an SBF that is valid within an (abstract) busy interval. *)
  Definition valid_busy_sbf (SBF : duration -> work) :=
    valid_pred_sbf sched (busy_interval_prefix sched) SBF.

End BusySupplyBoundFunctions.
