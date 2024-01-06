Require Export util.all.
Require Export behavior.schedule.
Require Export model.processor.supply.
Require Export analysis.definitions.sbf.sbf.

(** ** SBF Parameter Semantics *)

(** In the following, we define the semantics of the supply bound
    functions (SBF) parametrized by a predicate.

    In our development, we use several different types of SBF (such as
    the classical SBF, SBF within a busy interval, and SBF within an
    abstract busy interval). The parametrization of the definition
    with a predicate serves to avoid superfluous duplication.  *)
Section PredSupplyBoundFunctions.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any kind of processor state model, and ... *)
  Context `{PState : ProcessorState Job}.

  (** ... any schedule. *)
  Variable sched : schedule PState.

  (** Consider an arbitrary predicate on jobs and time intervals. *)
  Variable P : Job -> instant -> instant -> Prop.

  (** We say that the SBF is respected w.r.t. predicate [P] if, for
      any job [j], an interval <<[t1, t2)>> satisfying [P j], and a
      subinterval <<[t1, t) ⊆ [t1, t2)>>, at least [SBF (t - t1)]
      cumulative supply is provided. *)
  Definition pred_sbf_respected (SBF : duration -> work) :=
    forall (j : Job) (t1 t2 : instant),
      P j t1 t2 ->
      forall (t : instant),
        t1 <= t <= t2 ->
        SBF (t - t1) <= supply_during sched t1 t.

  (** We say that the SBF is valid w.r.t. predicate [P] if two
      conditions are satisfied: (1) [SBF 0 = 0] and (2) the SBF is
      respected w.r.t. predicate [P]. *)
  Definition valid_pred_sbf (SBF : duration -> work) :=
    SBF 0 = 0
    /\ pred_sbf_respected SBF.

  (** In the context of unit-supply processor models, it is known that
      the amount of supply provided by the processor is bounded by [1]
      at any time instant. Hence, we can consider a restricted notion
      of SBF, where the bound can only increase by at most [1] at each
      time instant. *)
  Definition unit_supply_bound_function (SBF : duration -> work) :=
    forall δ, SBF δ.+1 <= (SBF δ).+1.

  (** Next, suppose we are given an SBF characterizing the schedule. *)
  Context {SBF : SupplyBoundFunction}.

  (** The assumption [unit_supply_bound_function] together with the
      introduced validity assumption implies that [SBF δ <= δ] for any [δ]. *)
  Remark sbf_bounded_by_duration :
    valid_pred_sbf SBF ->
    unit_supply_bound_function SBF ->
    forall δ, SBF δ <= δ.
  Proof.
    move => [ZERO _] UNIT; elim.
    - by rewrite leqn0; apply/eqP.
    - by move => n; rewrite (leqRW (UNIT _)) ltnS.
  Qed.

End PredSupplyBoundFunctions.
