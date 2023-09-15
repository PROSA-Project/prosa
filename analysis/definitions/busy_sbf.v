Require Export prosa.util.all.
Require Export prosa.model.processor.sbf.
Require Export prosa.analysis.abstract.definitions.

(** * SBF within Busy Interval *)

(** In the following, we define a weaker notion of a supply bound
    function, which is a valid SBF only within a busy interval of a
    job. *)
Section BusySupplyBoundFunctions.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any kind of processor state model, and ... *)
  Context `{PState : ProcessorState Job}.

  (** ... any schedule. *)
  Variable sched : schedule PState.

  (** Assume we are provided with abstract functions for Interference
      and Interfering Workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Suppose we are given an SBF characterizing the schedule. *)
  Context {SBF : SupplyBoundFunction}.

  (** We say that the SBF is respected in a busy interval if, for any
      busy interval <<[t1, t2)>> and a subinterval <<[t1, t) ⊆ [t1,
      t2)>>, at least [SBF (t - t1)] cumulative supply is provided. *)
  Definition sbf_respected_in_busy_interval :=
    forall (j : Job) (t1 t2 : instant),
      busy_interval_prefix sched j t1 t2 ->
      forall (t : instant),
        t1 <= t <= t2 ->
        SBF (t - t1) <= supply_during sched t1 t.

  (** Next, we define an SBF that is valid within a busy interval. *)
  Definition valid_busy_sbf :=
    SBF 0 = 0
    /\ sbf_respected_in_busy_interval.

  (** The assumption [unit_supply_bound_function] together with the
      introduced validity assumption implies that [SBF δ <= δ] for any [δ]. *)
  Remark sbf_bounded_by_duration :
    valid_busy_sbf ->
    unit_supply_bound_function ->
    forall δ, SBF δ <= δ.
  Proof.
    move => [ZERO _] UNIT; elim.
    - by rewrite leqn0; apply/eqP.
    - by move => n; rewrite (leqRW (UNIT _)) ltnS.
  Qed.

  (** Also, note that [supply_bound_function_respected] implies
      [sbf_respected_in_busy_interval]. *)
  Remark sbf_respected_implies_sbf_busy_respected :
    supply_bound_function_respected sched ->
    sbf_respected_in_busy_interval.
  Proof.
    by move => sbf j t1 t2 BUSY t LE; apply: sbf => //; lia.
  Qed.

End BusySupplyBoundFunctions.
