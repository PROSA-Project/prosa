Require Export prosa.analysis.definitions.sbf.pred.
Require Export prosa.analysis.facts.behavior.supply.
Require Export prosa.model.task.concept.

(** In this section, we prove some useful facts about SBF. *)
Section SupplyBoundFunctionLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of unit-supply processor state model, ... *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.

  (** ... any valid arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** In the following section, we prove a lemma about switching a
      predicate inside of [valid_pred_sbf]. *)
  Section SBFChangePred.

    (** Consider an SBF ... *)
    Context {SBF : SupplyBoundFunction}.

    (** ... and two predicates [P1] and [P2] such that, for any job [j]
        and a time interval <<[t1, t2)>>, [P2 j t1 t2] implies [P1 j t1 t2]. *)
    Variables P1 P2 : Job -> instant -> instant -> Prop.
    Hypothesis H_p2_implies_p1 :
      forall j t1 t2,
        arrives_in arr_seq j ->
        P2 j t1 t2 -> P1 j t1 t2.

    (** Then if [SBF] is a valid SBF w.r.t. predicate [P1], then [SBF]
        is a valid SBF w.r.t. predicate [P2]. *)
    Lemma valid_pred_sbf_switch_predicate :
      valid_pred_sbf arr_seq sched P1 SBF ->
      valid_pred_sbf arr_seq sched P2 SBF.
    Proof.
      move=> VAL; split; first by apply VAL.
      move=> j t1 t2 ARR P2j t NEQ.
      by eapply VAL => //.
    Qed.

  End SBFChangePred.

  (** Consider an arbitrary predicate on jobs and time intervals. *)
  Variable P : Job -> instant -> instant -> Prop.

  (** Consider a supply-bound function [SBF] that is valid w.r.t. the
      predicate [P]. That is, (1) [SBF 0 = 0] and (2) for any job [j],
      an interval <<[t1, t2)>> satisfying [P j], and a subinterval
      <<[t1, t) ⊆ [t1, t2)>>, the supply produced during the time
      interval <<[t1, t)>> is at least [SBF (t - t1)]. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_valid_SBF : valid_pred_sbf arr_seq sched P SBF.

  (** In this section, we show a simple upper bound on the blackout
      during an interval of length [Δ]. *)
  Section BlackoutBound.

    (** Consider any job [j]. *)
    Variable j : Job.
    Hypothesis H_arrives_in : arrives_in arr_seq j.

    (** Consider an interval <<[t1, t2)>> satisfying [P j]. *)
    Variables t1 t2 : instant.
    Hypothesis H_P_interval : P j t1 t2.

    (** Consider an arbitrary duration [Δ] such that [t1 + Δ <= t2]. *)
    Variable Δ : duration.
    Hypothesis H_subinterval : t1 + Δ <= t2.

    (** We show that the total blackout time during an interval of
        length [Δ] is bounded by [Δ - SBF Δ]. *)
    Lemma blackout_during_bound :
      blackout_during sched t1 (t1 + Δ) <= Δ - SBF Δ.
    Proof.
      rewrite blackout_during_complement // leq_sub => //.
      rewrite -(leqRW (snd H_valid_SBF _ _ _ _ _ _ _)).
      { by have -> : (t1 + Δ) - t1 = Δ by lia. }
      { by apply H_arrives_in. }
      { by eapply H_P_interval. }
      { lia. }
     Qed.

  End BlackoutBound.

  (** In the following section, we prove a few facts about _unit_ SBF. *)
  Section UnitSupplyBoundFunctionLemmas.

    (** In addition, let us assume that [SBF] is a unit-supply SBF.
        That is, [SBF] makes steps of at most one. *)
    Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

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
