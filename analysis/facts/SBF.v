Require Export prosa.model.processor.sbf.
Require Export prosa.analysis.facts.behavior.supply.
Require Export prosa.model.task.concept.

(** In this section, we prove some useful facts about SBF. *)
Section SupplyBoundFunctionLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs. *)
  Context {Job : JobType}.

  (** Consider any kind of unit-supply processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Consider a valid, supply-bound function [SBF]. That is, (1) [SBF
      0 = 0] and (2) for any duration [Δ], the supply produced during
      a time interval of length [Δ] is at least [SBF Δ]. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_valid_SBF : valid_supply_bound_function sched.

  (** We show that the total blackout time during an interval of
      length [Δ] is bounded by [Δ - SBF Δ]. *)
  Lemma blackout_during_bound :
    forall t Δ,
      blackout_during sched t (t + Δ) <= Δ - SBF Δ.
  Proof.
    move=> t Δ; rewrite blackout_during_complement // leq_sub => //.
    rewrite -(leqRW (snd (H_valid_SBF) _ _ _)); last by rewrite leq_addr.
    by have -> : (t + Δ) - t = Δ by lia.
  Qed.

  (** In the following section, we prove a few facts about _unit_ SBF. *)
  Section UnitSupplyBoundFunctionLemmas.

    (** In addition, let us assume that [SBF] is a unit-supply SBF.
        That is, [SBF] makes steps of at most one. *)
    Hypothesis H_unit_SBF : unit_supply_bound_function.

    (** We prove that the complement of such an SBF (i.e., [fun Δ => Δ -
        SBF Δ]) is monotone. *)
    Lemma complement_SBF_monotone :
      forall Δ1 Δ2,
        Δ1 <= Δ2 ->
        Δ1 - SBF Δ1 <= Δ2 - SBF Δ2.
    Proof.
      move => Δ1 Δ2 LE; interval_to_duration Δ1 Δ2 k.
      elim: k => [|δ IHδ]; first by rewrite addn0.
      by rewrite (leqRW IHδ) addnS (leqRW (H_unit_SBF _)); lia.
    Qed.

  End UnitSupplyBoundFunctionLemmas.

End SupplyBoundFunctionLemmas.
