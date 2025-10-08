Require Export prosa.model.priority.classes.
Require Export prosa.model.processor.supply.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.analysis.definitions.sbf.plain.
Require Export prosa.model.processor.average_resource_model.


(** In this section, we define a valid SBF for the average resource model. *)
Section AverageResourceModelValidSBF.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Consider a JLFP policy, ... *)
  Context `{JLFP_policy Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume the average resource model with a resource period [Π],
      resource allocation time [Θ], and supply delay [ν]. *)
  Variable Π Θ ν : duration.
  Hypothesis H_average_resource_model : average_resource_model Π Θ ν sched.

  (** We define SBF for the average resource model as
      [((Δ - ν) - (Π - Θ)) * Θ / Π]. *)
  #[local] Instance sbf : SupplyBoundFunction :=
    fun Δ =>
      ((Δ - ν) - (Π - Θ)) * Θ %/ Π.

  (** We show that [sbf] is monotone. *)
  Lemma arm_sbf_monotone : sbf_is_monotone sbf.
  Proof.
    move => δ1 δ2 LE; rewrite /sbf.
    interval_to_duration δ1 δ2 Δ.
    set (A := Π - Θ).
    have [LEA|LEA] := leqP (δ1 - ν) A.
    { by move: LEA; rewrite -subn_eq0 => /eqP EQ; rewrite EQ div0n. }
    { have ->: δ1 + Δ - ν - A = δ1 - ν - A + Δ by lia.
      by rewrite mulnDl; apply leq_div2r; lia. }
  Qed.

  (** The introduced SBF is also a unit-supply SBF. *)
  Lemma arm_sbf_unit : unit_supply_bound_function sbf.
  Proof.
    move: H_average_resource_model => [LEΠ _].
    move => δ; rewrite /sbf.
    have [Z|POS] := posnP Π; first by subst; lia.
    set (A := Π - Θ).
    have [LEν|LEν] := leqP δ ν.
    { move: (LEν); rewrite -subn_eq0 => /eqP ->.
      have [EQ|EQ]: (δ.+1 - ν = 0) \/ (δ.+1 - ν = 1) by lia.
      { by rewrite EQ. }
      { rewrite EQ //=; clear EQ.
        have [EQ|EQ]: 1 - A = 0 \/ 1 - A = 1 by lia.
        { by rewrite EQ. }
        { rewrite EQ mul1n sub0n mul0n -addn1 div0n add0n.
          move: LEΠ; rewrite leq_eqVlt => /orP [/eqP T| LT]; subst.
          { by rewrite divnn POS. }
          { by rewrite divn_small. }
        }
      }
    }
    { rewrite -addn1 -addnBAC ?addn1; last by lia.
      have [LEA|LEA] := leqP (δ - ν).+1 A.
      { by move: LEA; rewrite -subn_eq0 => /eqP EQ; rewrite EQ div0n. }
      by rewrite -addn1 -addnBAC // mulnDl mul1n -addn1 -divnDMl //; apply leq_div2r; lia.
    }
  Qed.

  (** Finally, we show that the defined [sbf] is a valid SBF. *)
  Lemma arm_sbf_valid :
    valid_supply_bound_function arr_seq sched sbf.
  Proof.
    have FS: forall a, 0 - a = 0 by lia.
    split; first by rewrite /sbf !FS mul0n div0n.
    move => j t1 t2 ARR _ t /andP [LE1 LE2].
    move: H_average_resource_model => [LE SUP].
    interval_to_duration t1 t Δ.
    rewrite -(leqRW (SUP _ _)) /sbf.
    have ->: t1 + Δ - t1 = Δ by lia.
    by rewrite subnBA //; apply leq_div2r, leq_mul => //; lia.
  Qed.

End AverageResourceModelValidSBF.
