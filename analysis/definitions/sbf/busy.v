Require Export prosa.util.all.
Require Export prosa.analysis.definitions.sbf.pred.
Require Export prosa.analysis.definitions.busy_interval.classical.

(** * SBF within Busy Interval *)

(** In the following, we define a weak notion of a supply bound
    function, which is a valid SBF only within a busy interval of a
    job. *)
Section BusySupplyBoundFunctions.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any kind of processor state model, ... *)
  Context `{PState : ProcessorState Job}.

  (** ... any valid arrival sequence, and ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** We say that the SBF is respected in a busy interval if, for any
      busy interval <<[t1, t2)>> and a subinterval <<[t1, t) ⊆ [t1,
      t2)>>, at least [SBF (t - t1)] cumulative supply is provided. *)
  Definition sbf_respected_in_busy_interval (SBF : duration -> work) :=
    pred_sbf_respected arr_seq sched (busy_interval_prefix arr_seq sched) SBF.

  (** Next, we define an SBF that is valid within a busy interval. *)
  Definition valid_busy_sbf (SBF : duration -> work) :=
    valid_pred_sbf arr_seq sched (busy_interval_prefix arr_seq sched) SBF.

End BusySupplyBoundFunctions.
