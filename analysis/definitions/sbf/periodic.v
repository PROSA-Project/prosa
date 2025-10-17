Require Export prosa.model.priority.classes.
Require Export prosa.model.processor.supply.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.analysis.definitions.sbf.plain.
Require Export prosa.model.processor.periodic_resource_model.

(** * SBF for Periodic Resource Model *)

(** In this section, we restate the SBF defined in the paper "Periodic Resource
    Model for Compositional Real-Time Guarantees" by Shin & Lee (RTSS 2003). *)
Section PeriodicResourceModelSBF.

  (** Given a periodic resource model with a resource period [Π] and resource
      allocation time [γ], ... *)
  Variable Π γ : duration.

  (** ... we define the corresponding SBF as introduced in "Periodic Resource
      Model for Compositional Real-Time Guarantees" by Shin & Lee (RTSS
      2003). *)
  Definition prm_sbf Δ :=
    let blackout := Π - γ in
    let n_full_periods := (Δ - blackout) %/ Π in
    let supply_in_full_periods := n_full_periods * γ in
    let duration_of_full_periods := n_full_periods * Π in
    supply_in_full_periods + (Δ - 2 * blackout - duration_of_full_periods).

End PeriodicResourceModelSBF.

(** In this section, we prove that [prm_sbf] is a valid SBF for the periodic
    resource model. *)
Section PeriodicResourceModelValidSBF.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of unit-supply processor state model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.

  (** Consider a JLFP policy, ... *)
  Context `{JLFP_policy Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a periodic resource model with a resource period [Π] and resource
      allocation time [γ]. *)
  Variable Π γ : duration.
  Hypothesis H_periodic_resource_model : periodic_resource_model Π γ sched.

  (** Next, we prove a few properties required by aRSA-based analyses, in
      particular that the SBF is valid. *)

  (** We show that [sbf] is monotone. *)
  Lemma prm_sbf_monotone : sbf_is_monotone (prm_sbf Π γ).
  Proof.
    move => δ1 δ2 LE; rewrite /prm_sbf.
    interval_to_duration δ1 δ2 Δ.
    have [Z|POS] := posnP Π; first by subst; rewrite divn0 !mul0n !add0n !subn0 leq_addr.
    set (A := Π - γ); have ->: 2 * A = A + A by lia.
    rewrite !subnDAC.
    have [LEA|LEA] := leqP δ1 A.
    { move: LEA; rewrite -subn_eq0 => /eqP EQ.
      by rewrite EQ div0n !mul0n add0n. }
    have ->: δ1 + Δ - A = δ1 - A + Δ by lia.
    set (δ2 := δ1 - A).
    have [k [q [EQ LT1]]] : exists k q, Δ = k * Π + q /\ q < Π.
    { by eexists; eexists; split; [ apply divn_eq | rewrite ltn_mod ]. }
    subst Δ; have ->: δ2 + (k * Π + q) =k * Π + (δ2 + q) by lia.
    have [h [j [EQ LT2]]] : exists k q, δ2 = k * Π + q /\ q < Π.
    { by eexists; eexists; split; [ apply divn_eq | rewrite ltn_mod ]. }
    subst δ2; rewrite !EQ; clear EQ.
    rewrite divnDl; last by rewrite dvdn_mull // dvdnn.
    rewrite !mulnDl mulnK // subnDA.
    rewrite -![_ + j + q]addnA.
    rewrite divnDl; last by rewrite dvdn_mull // dvdnn.
    rewrite !mulnDl mulnK // subnDA.
    replace (j %/ Π) with 0; last by symmetry; apply divn_small.
    replace (q %/ Π) with 0; last by symmetry; apply divn_small.
    rewrite mul0n addn0 divnDl; last by rewrite dvdn_mull // dvdnn.
    rewrite !mulnDl mulnK // subnDA mul0n subn0.
    set (s := (j + q) %/ Π).
    have F: s <= 1.
    { rewrite /s; apply leq_trans with ((Π + q) %/ Π).
      { by apply leq_div2r; lia. }
      { by rewrite divnDl; [rewrite divnn POS divn_small | apply dvdnn]. }
    }
    rewrite [k*γ + _]addnC -!addnA leq_add2l.
    have ->: forall a b c, a + b - c - a = b - c by lia.
    rewrite !addnA -!mulnDl -!subnDA  -!mulnDl !addnA.
    have -> : (k + h) * Π + j + q - (A + (k + h + s) * Π)
             = j + q - (A + s * Π) by lia.
    destruct s as [ | [ | ]] => //; clear F.
    { by rewrite add0n mul0n addn0; lia. }
    rewrite /A; lia.
  Qed.

  (** The introduced SBF is also a unit-supply SBF. *)
  Lemma prm_sbf_unit : unit_supply_bound_function (prm_sbf Π γ).
  Proof.
    move: H_periodic_resource_model => [_ [LEΠ _]].
    move => δ; rewrite /prm_sbf !subnDAC.
    have [Z|POS] := posnP Π; first by subst; lia.
    have [h [j [EQ LT2]]] : exists k q, δ = k * Π + q /\ q < Π.
    { by eexists; eexists; split; [ apply divn_eq | rewrite ltn_mod ]. }
    subst δ; rewrite -addn1 -[leqRHS]addn1 !subnBA // !subn0.
    have ALT : j + 1 + γ < Π \/ j + 1 + γ = Π \/ Π < j + 1 + γ < 2 * Π \/ j + 1 + γ = 2 * Π by lia.
    have [Z|POSh] := posnP h.
    { subst; rewrite mul0n add0n; move: ALT => [NEQ|[NEQ|[NEQ|NEQ]]].
      - by rewrite !divn_small //; lia.
      - by rewrite !NEQ subnn div0n mul0n divn_small; lia.
      - have ->: (j + γ - Π) %/ Π = 0 by rewrite divn_small; lia.
        have ->: (j + 1 + γ - Π) %/ Π = 0 by rewrite divn_small; lia.
        by lia.
      - have ->: (j + γ - Π) %/ Π = 0 by rewrite divn_small; lia.
        rewrite NEQ; have ->: 2 * Π - Π = Π by lia.
        by rewrite divnK ?dvdnn // divnn POS; lia. }
    { have -> : h * Π + j + 1 + γ - Π = (h - 1) * Π + j + 1 + γ.
      { by rewrite mulnBl -!addnA addBnAC; [ lia | apply leq_mul ]. }
      have -> : h * Π + j + γ - Π = (h - 1) * Π + j + γ.
      { by rewrite mulnBl -!addnA addBnAC; [ lia | apply leq_mul ]. }
      rewrite -!addnA divnDl; last by rewrite dvdn_mull //.
      rewrite mulnK // !mulnDl [in leqRHS]divnDl; last by rewrite dvdn_mull //.
      rewrite !mulnDl mulnK // -!addnA leq_add2l !addnA.
      move: ALT => [NEQ|[NEQ|[NEQ|NEQ]]].
      - by rewrite !divn_small //; lia.
      - by rewrite !NEQ divnn POS mul1n divn_small; lia.
      - have ->: (j + γ) %/ Π = 1 by apply divn_leq; lia.
        have ->: (j + 1 + γ) %/ Π = 1 by apply divn_leq; lia.
        by rewrite mul1n; lia.
      - have ->: (j + γ) %/ Π = 1 by apply divn_leq; lia.
        rewrite NEQ divnK; last by apply dvdn_mull, dvdnn.
        by rewrite mulnK //; lia.
    }
  Qed.

  (** In the following, we prove that the introduced SBF is valid. *)

  (** We prove the validity claim via a case analysis on the interval for
      which the SBF is computed. First, we consider an interval that falls
      completely within a period <<[kΠ, (k + 1)Π)>> for some [k]. *)
  Section Case1.

    (** Consider a constant [k] and two durations [q1, q2 < Π]. *)
    Variable (k : nat) (q1 q2 : duration).
    Hypothesis H_q1_small : q1 < Π.
    Hypothesis H_q2_small : q2 < Π.

    (** We show that, in this case, supply during the interval is
        lower-bounded by [(q2 - q1) - (Π - Θ)].*)
    Local Lemma prm_sbf_valid_aux_11 :
      (q2 - q1) - (Π - γ) <= supply_during sched (k * Π + q1) (k * Π + q2).
    Proof.
      have [Z|LT] := leqP q2 q1; first by lia.
      set (P2 t := (k * Π + q1) <= t < (k * Π + q2)).
      have LEQ: \sum_(k * Π <= t < (k + 1) * Π) (has_supply sched t && P2 t) <= supply_during sched (k * Π + q1) (k * Π + q2).
      { erewrite big_cat_nat with (n := k * Π + q1); [rewrite //= | lia | lia].
        erewrite big_cat_nat with (m := k * Π + q1) (n := k * Π + q2); [rewrite //= | lia | lia].
        have -> : \sum_(k * Π <= i < k * Π + q1) has_supply sched i && P2 i  = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        have -> : \sum_(k * Π + q2 <= i < (k + 1) * Π) has_supply sched i && P2 i = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        rewrite add0n addn0; apply leq_sum_seq => //= => t; rewrite mem_index_iota => /andP [LEQ1 LEQ2] _.
        by rewrite /P2 LEQ1 LEQ2 !andbT /has_supply; case : (supply_at _ _ ).
      }
      rewrite -(leqRW LEQ); clear LEQ.
      have A : q2 - q1 <= \sum_(k * Π <= t < (k + 1) * Π) P2 t.
      { erewrite big_cat_nat with (n := k * Π + q1); [rewrite //= | lia | lia].
        have -> : \sum_(k * Π <= i < k * Π + q1) P2 i = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        erewrite big_cat_nat with (n := k * Π + q2); [rewrite //= | lia | lia].
        have -> : \sum_(k * Π + q2 <= i < (k + 1) * Π) P2 i = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        rewrite -[q2 - q1](sum_of_ones (k * Π + q1)) add0n addn0.
        have -> : k * Π + q1 + (q2 - q1) = k * Π + q2 by lia.
        rewrite big_seq_cond [leqRHS]big_seq_cond.
        by apply leq_sum => t; rewrite /P2 mem_index_iota => /andP [NEQ _]; lia.
      }
      have B : γ <= \sum_(k * Π <= t < (k + 1) * Π) has_supply sched t.
      { move: (H_periodic_resource_model) => [_ [_ LE]]; rewrite (leqRW (LE k)).
        rewrite mulnC [_ * ( _ + _ ) ]mulnC; apply leq_sum => t _.
        by move: (H_unit_supply_proc_model (sched t)); rewrite /has_supply /supply_at; case:(supply_in _); lia.
      }
      by rewrite -(leqRW (pigeonhole_on_interval _ _ _ _ _ _ _ _)); [ | apply B |apply A]; lia.
    Qed.

    (** Let <<[t1, t2)>> := <<[kΠ + q1, kΠ + q2)>> be the interval under analysis. *)
    Let t1 := k * Π + q1.
    Let t2 := k * Π + q2.

    (** By unfolding the expression for [sbf] and using the above
        inequalities, we show that the supply during <<[t1, t2)>> is
        indeed lower-bounded by [sbf (t2-t1)].  *)
    Lemma prm_sbf_valid_aux_1 :
      prm_sbf Π γ (t2 - t1) <= supply_during sched t1 t2.
    Proof.
      move: (H_periodic_resource_model) => [POS [LE VAL]].
      rewrite -(leqRW prm_sbf_valid_aux_11) // /prm_sbf.
      have ->: forall a b, a - 2 * b = a - b - b by lia.
      have ->: k * Π + q2 - (k * Π + q1) = q2 - q1 by lia.
      rewrite subnBA //.
      set (q3 := q2 - q1); set (q4 := q3 + γ); set (q5 := q4 - Π).
      rewrite {2}(divn_eq q5 Π).
      have -> : q5 %/ Π * Π + q5 %% Π - (Π - γ) - q5 %/ Π * Π = q5 %% Π - (Π - γ).
      { have -> : forall a b c d, a + b - c - d = a + b - d - c by lia.
        by set (q6 := q5 %/ Π * Π); lia. }
      apply leq_trans with (q5 %/ Π * γ + (q5 %% Π)); first by lia.
      apply leq_trans with (q5 %/ Π * Π + (q5 %% Π)).
      { by rewrite leq_add2r leq_mul2l; apply/orP; right. }
      by rewrite -divn_eq.
    Qed.

  End Case1.

  (** For the second case, consider an interval that touches at least two
      periods. That is, consider an interval <<[k1 Π + q1, k2 Π + q2)>> for
      some [k1 < k2]. *)
  Section Case2.

    (** Consider two constants [k1, k2] such that [k1 < k2] and two durations [q1, q2 < Π]. *)
    Variables (k1 k2 : nat) (q1 q2 : duration).
    Hypothesis H_q1_small : q1 < Π.
    Hypothesis H_q2_small : q2 < Π.
    Hypothesis H_k1_lt_k2 : k1 < k2.

    (** First, we show that the interval can be split into three
        sub-intervals: <<[k1 Π + q1, (k1 + 1) Π + q1)>>,
        <<[(k1 + 1) Π + q1, k2 Π)>>, and <<[k2 Π, k2 Π + q2)>>. *)
    Lemma prm_sbf_valid_aux_21 :
      supply_during sched (k1 * Π + q1) (k2 * Π + q2)
      = supply_during sched (k1 * Π + q1) ((k1 + 1) * Π)
        + supply_during sched ((k1 + 1) * Π) (k2 * Π)
        + supply_during sched (k2 * Π) (k2 * Π + q2).
    Proof.
      apply/eqP. rewrite /supply_during.
      erewrite big_cat_nat with (n := (k1 + 1) * Π); [rewrite //= | lia | ]; first last.
      { have [Δ [EQ LT]] : exists Δ, k2 = k1 + Δ /\ Δ > 0 by (exists (k2 - k1); lia).
        by subst k2; rewrite !mulnDl -addnA leq_add2l mul1n -[leqRHS](leqRW (leq_addr _ _ )) leq_pmull. }
      rewrite -!addnA eqn_add2l.
      erewrite big_cat_nat with (n := k2 * Π); [rewrite //= |  | lia ].
      { have [Δ [EQ LT]] : exists Δ, k2 = k1 + Δ /\ Δ > 0 by (exists (k2 - k1); lia).
        by subst k2; rewrite leq_mul2r; apply/orP; right; lia. }
    Qed.

    (** In the following, we simply lower-bound the supply in each
        of the three sub-intervals. *)

    (** Supply in the interval <<[k1 Π + q1, (k1 + 1) Π + q1)>> is
        lower-bounded by [(Π - q1) - (Π - Θ)]. *)
    Lemma prm_sbf_valid_aux_22 :
      (Π - q1) - (Π - γ) <= supply_during sched (k1 * Π + q1) ((k1 + 1) * Π).
    Proof.
      set (P2 t := (k1 * Π + q1) <= t < ((k1 + 1) * Π)).
      have LEQ: \sum_(k1 * Π <= t < (k1 + 1) * Π) (has_supply sched t && P2 t) <= supply_during sched (k1 * Π + q1) ((k1 + 1) * Π).
      { erewrite big_cat_nat with (n := k1 * Π + q1); [rewrite //= | lia | lia].
        have -> : \sum_(k1 * Π <= i < k1 * Π + q1) has_supply sched i && P2 i  = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        rewrite add0n; apply leq_sum_seq => //= => t; rewrite mem_index_iota => /andP [LEQ1 LEQ2] _.
        by rewrite /P2 LEQ1 LEQ2 !andbT /has_supply; case : (supply_at _ _ ).
      }
      rewrite -(leqRW LEQ); clear LEQ.
      have A : Π - q1 <= \sum_(k1 * Π <= t < (k1 + 1) * Π) P2 t.
      { erewrite big_cat_nat with (n := k1 * Π + q1); [rewrite //= | lia | lia].
        have -> : \sum_(k1 * Π <= i < k1 * Π + q1) P2 i = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        rewrite -[Π - q1](sum_of_ones (k1 * Π + q1)) add0n.
        have -> : k1 * Π + q1 + (Π - q1) = (k1 + 1) * Π by lia.
        rewrite big_seq_cond [leqRHS]big_seq_cond.
        by apply leq_sum => t; rewrite /P2 mem_index_iota => /andP [NEQ _]; lia.
      }
      have B : γ <= \sum_(k1 * Π <= t < (k1 + 1) * Π) has_supply sched t.
      { move: (H_periodic_resource_model) => [_ [_ LE]]; rewrite (leqRW (LE k1)).
        rewrite mulnC [_ * ( _ + _ ) ]mulnC; apply leq_sum => t _.
        by move: (H_unit_supply_proc_model (sched t)); rewrite /has_supply /supply_at; case:(supply_in _); lia.
      }
      by rewrite -(leqRW (pigeonhole_on_interval _ _ _ _ _ _ _ _)); [ | apply B |apply A]; lia.
    Qed.

    (** Supply in the interval <<[(k1 + 1) Π + q1, k2 Π)>> is
        lower-bounded by [(k2 - (k1 + 1)) * Θ]. *)
    Lemma prm_sbf_valid_aux_23 :
      (k2 - (k1 + 1)) * γ <= supply_during sched ((k1 + 1) * Π) (k2 * Π).
    Proof.
      move: (H_periodic_resource_model) => [_ [_ LE]].
      move: (H_k1_lt_k2) => NEQ; rewrite -addn1 in NEQ.
      set (k3 := k1 + 1) in *.
      interval_to_duration k3 k2 δ.
      have ->: k3 + δ - k3 = δ by lia.
      clear H_k1_lt_k2; induction δ as [ | δ IHδ]; first by rewrite mul0n.
      unfold supply_during in *.
      erewrite big_cat_nat with (n := (k3 + δ) * Π); [rewrite //= | lia | lia].
      rewrite -(leqRW IHδ); clear IHδ.
      by rewrite addnS -[in leqRHS]addn1 [_ * Π]mulnC [(_ + _ ) * Π]mulnC -(leqRW (LE _)); lia.
    Qed.

    (** Supply in the interval <<[k2 Π, k2 Π + q2)>> is
        lower-bounded by [q2 - (Π - Θ)]. *)
    Lemma prm_sbf_valid_aux_24 :
      q2 - (Π - γ) <= supply_during sched (k2 * Π) (k2 * Π + q2).
    Proof.
      set (P2 t := (k2 * Π) <= t < (k2 * Π + q2)).
      have LEQ: \sum_(k2 * Π <= t < (k2 + 1) * Π) (has_supply sched t && P2 t) <= supply_during sched (k2 * Π) (k2 * Π + q2).
      { erewrite big_cat_nat with (n := k2 * Π + q2); [rewrite //= | lia | lia].
        have -> : \sum_(k2 * Π + q2 <= i < (k2 + 1) * Π) has_supply sched i && P2 i = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        rewrite addn0; apply leq_sum_seq => //= => t; rewrite mem_index_iota => /andP [LEQ1 LEQ2] _.
        by rewrite /P2 LEQ1 LEQ2 !andbT /has_supply; case : (supply_at _ _ ).
      }
      rewrite -(leqRW LEQ); clear LEQ.
      have A : q2 <= \sum_(k2 * Π <= t < (k2 + 1) * Π) P2 t.
      { erewrite big_cat_nat with (n := k2 * Π + q2); [rewrite //= | lia | lia].
        have -> : \sum_(k2 * Π + q2 <= i < (k2 + 1) * Π) P2 i = 0.
        { by apply big1_seq => t; rewrite /P2 mem_index_iota => /andP [_ FF]; lia. }
        rewrite -{1}[q2](sum_of_ones (k2 * Π)) addn0.
        rewrite big_seq_cond [leqRHS]big_seq_cond.
        by apply leq_sum => t; rewrite /P2 mem_index_iota => /andP [NEQ _]; lia.
      }
      have B : γ <= \sum_(k2 * Π <= t < (k2 + 1) * Π) has_supply sched t.
      { move: (H_periodic_resource_model) => [_ [_ LE]]; rewrite (leqRW (LE k2)).
        rewrite mulnC [_ * ( _ + _ ) ]mulnC; apply leq_sum => t _.
        by move: (H_unit_supply_proc_model (sched t)); rewrite /has_supply /supply_at; case:(supply_in _); lia.
      }
      by rewrite -(leqRW (pigeonhole_on_interval _ _ _ _ _ _ _ _)); [ | apply B |apply A]; lia.
    Qed.

    (** Let <<[t1, t2)>> := <<[k1 Π + q1, k2 Π + q2)>> be the interval under analysis. *)
    Let t1 := k1 * Π + q1.
    Let t2 := k2 * Π + q2.

    (** By unfolding the expression for [sbf] and using the above
        inequalities, we show that the supply during <<[t1, t2)>>
        is indeed lower-bounded by [sbf (t2-t1)].  *)
    Lemma prm_sbf_valid_aux_2 :
      prm_sbf Π γ (t2 - t1) <= supply_during sched t1 t2.
    Proof.
      rewrite /prm_sbf.
      move: (H_periodic_resource_model) => [POS [LE VAL]].
      rewrite prm_sbf_valid_aux_21 //
              -(leqRW prm_sbf_valid_aux_22) //
              -(leqRW prm_sbf_valid_aux_23) //
              -(leqRW prm_sbf_valid_aux_24) //.
      have ->: Π - q1 - (Π - γ) = γ - q1 by lia.
      have [NEQk1|NEQk2] : k1 + 1 = k2 \/ k1 + 1 < k2 by lia.
      { subst k2; rewrite subnn mul0n addn0; clear H_k1_lt_k2.
        have ->: forall a b, a - 2 * b = a - b - b by lia.
        have ->: (k1 + 1) * Π + q2 - (k1 * Π + q1) = Π + q2 - q1 by lia.
        have ->: (Π + q2 - q1) = (Π - q1 + q2) by lia.
        have ->: Π - q1 + q2 - (Π - γ) = q2 + γ - q1 by lia.
        have [NEQ | NEQ] : (q2 + γ - q1 < Π) \/ (Π <= q2 + γ - q1 < 2 * Π).
        { by enough (A : q2 + γ - q1 < 2 * Π); lia. }
        { by rewrite divn_small // !mul0n add0n subn0; lia. }
        { by have ->: (q2 + γ - q1) %/ Π = 1; [apply divn_leq | ]; lia. }
      }
      { have ->: forall a b, a - 2 * b = a - b - b by lia.
        have ->: k2 * Π + q2 - (k1 * Π + q1) = (k2 - k1) * Π + q2 - q1 by lia.
        have ->: (k2 - k1) * Π + q2 - q1 - (Π - γ) = (k2 - (k1 + 1)) * Π + q2 - q1 + γ.
        { rewrite subnBA // -addnBAC; first lia.
          apply leq_trans with (2 * Π + q2 - q1); first lia.
          by rewrite leq_sub2r // leq_add2r leq_mul //; lia.
        }
        have [k3 ->] : exists k3, (k2 - (k1 + 1)) = k3 + 1 by (exists (k2 - (k1 + 1) - 1); lia).
        rewrite !mulnDl mul1n.
        have -> : k3 * Π + Π + q2 - q1 + γ = k3 * Π + (Π + q2 - q1 + γ) by lia.
        rewrite divnDl ?mulnK // ?mulnDl.
        have [NEQ | [NEQ | NEQ]] :
          (Π + q2 - q1 + γ < Π) \/ (Π <= Π + q2 - q1 + γ < 2 * Π) \/ (2 * Π <= Π + q2 - q1 + γ < 3 * Π).
        { by enough (F : 0 <= Π + q2 - q1 + γ < 3 * Π); lia. }
        { by rewrite divn_small //; lia. }
        { by have ->: (Π + q2 - q1 + γ) %/ Π = 1; [apply divn_leq | ]; lia. }
        { by have ->: (Π + q2 - q1 + γ) %/ Π = 2; [apply divn_leq | ]; lia. }
      }
    Qed.

  End Case2.

  (** By using the two auxiliary lemmas above, we prove that [sbf]
      is a valid SBF. *)
  Lemma prm_sbf_valid :
    valid_supply_bound_function arr_seq sched (prm_sbf Π γ).
  Proof.
    have FS: forall a, 0 - a = 0 by lia.
    split; first by rewrite /prm_sbf !FS addn0 div0n mul0n.
    move => j t1 t2 ARR _ t /andP [LE1 LE2].
    move: H_periodic_resource_model => [POSΠ [LE SUP]].
    have [k1 [q1 [EQ1 LT1]]] : exists k1 q1, t1 = k1 * Π + q1 /\ q1 < Π.
    { by eexists; eexists; split; [apply divn_eq | apply ltn_pmod]. }
    have [k2 [q2 [EQ2 LT2]]] : exists k2 q2, t = k2 * Π + q2 /\ q2 < Π.
    { by eexists; eexists; split; [apply divn_eq | apply ltn_pmod]. }
    subst.
    have [EQk|NEQk] : k1 = k2 \/ k1 < k2.
    { enough (LEQ : k1 <= k2); first by lia.
      move_neq_up LT; move_neq_down LE1.
      apply leq_trans with (k2 * Π + Π); first by lia.
      apply leq_trans with (k1 * Π); last by lia.
      by rewrite -{2}[Π]mul1n -mulnDl leq_mul2r; apply/orP; right; lia.
    }
    { by subst; apply prm_sbf_valid_aux_1. }
    { by apply prm_sbf_valid_aux_2. }
  Qed.

End PeriodicResourceModelValidSBF.
