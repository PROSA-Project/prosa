Require Export prosa.util.all.
Require Export prosa.model.processor.supply.

(** * Supply Bound Functions (SBF) *)

(** In the following, we define the notion of Supply Bound Functions
    (SBF), which can be used to reason about the minimum amount of supply
    provided in a given time interval. *)

(** We let [supply_bound_function Δ] denote a lower bound on the
    supply provided in an interval of length [Δ]. *)
Class SupplyBoundFunction :=
  supply_bound_function : duration -> work.

(** ** Parameter Semantics *)

(** In the following, we precisely define the semantics of the supply
    bound functions and introduce one useful special case. *)
Section SupplyBoundFunctions.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any kind of processor state model, and ... *)
  Context `{PState : ProcessorState Job}.

  (** ... any schedule. *)
  Variable sched : schedule PState.

  (** Suppose we are given an SBF characterizing the schedule. *)
  Context {SBF : SupplyBoundFunction}.

  (** We say that the SBF is respected if, for any time interval <<[t1, t2)>>,
      at least [SBF (t2 - t1)] cumulative supply is provided within the given
      interval. In other words, the SBF lower-bounds the provided supply. *)
  Definition supply_bound_function_respected :=
    forall (t1 t2 : instant),
      t1 <= t2 ->
      SBF (t2 - t1) <= supply_during sched t1 t2.

  (** We say that the SBF is valid if two conditions are satisfied:
      (1) [SBF 0 = 0] and (2) the SBF is respected. *)
  Definition valid_supply_bound_function :=
    SBF 0 = 0
    /\ supply_bound_function_respected.

  (** In the context of unit-supply processor models, it is known that
      the amount of supply provided by the processor is bounded by [1]
      at any time instant. Hence, we can consider a restricted notion
      of SBF, where the bound can only increase by at most [1] at each
      time instant. *)
  Definition unit_supply_bound_function :=
    forall δ, SBF δ.+1 <= (SBF δ).+1.

  (** Together with the validity assumption, the unit SBF assumption
      implies that [SBF δ <= δ] for any [δ]. *)
  Remark sbf_bounded_by_duration :
    valid_supply_bound_function ->
    unit_supply_bound_function ->
    forall δ, SBF δ <= δ.
  Proof.
    move => [ZERO _] UNIT; elim.
    - by rewrite leqn0; apply/eqP.
    - by move => n; rewrite (leqRW (UNIT _)) ltnS.
  Qed.

End SupplyBoundFunctions.
