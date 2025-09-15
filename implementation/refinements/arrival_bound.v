Require Export prosa.implementation.refinements.refinements.
Require Export prosa.implementation.definitions.arrival_bound.

(** In this section, we define a generic version of arrival bound and
    prove that it is isomorphic to the standard, natural-number-based
    definition. *)
Section Definitions.

  (** Consider a generic type [T], for which all the basic arithmetical
      operations, ordering, and equality are defined. *)
  Context {T : Type}.
  Context `{!zero_of T, !one_of T, !sub_of T, !add_of T, !mul_of T,
            !div_of T, !mod_of T, !eq_of T, !leq_of T, !lt_of T}.
  Context `{!eq_of (seq T)}.
  Context `{!eq_of (T * seq (T * T))}.

  (** As in the natural-numbers-based definition, an arrival curve prefix
      is composed of an horizon and a list of steps. *)
  Let ArrivalCurvePrefix : Type := T * seq (T * T).

  (** A task's arrival bound is an inductive type comprised of three types of
      arrival patterns: (a) periodic, characterized by a period between consequent
      activation of a task, (b) sporadic, characterized by a minimum inter-arrival
      time, or (c) arrival-curve prefix, characterized by a finite prefix of an
      arrival curve. *)
  Inductive task_arrivals_bound_T :=
  | Periodic_T : T -> task_arrivals_bound_T
  | Sporadic_T : T -> task_arrivals_bound_T
  | ArrivalPrefix_T : T * seq (T * T) -> task_arrivals_bound_T.

  (** Further, we define the equality for two generic tasks as the equality
        of each attribute. *)
  Definition taskab_eqdef_T (tb1 tb2 : task_arrivals_bound_T) : bool :=
    match tb1, tb2 with
    | Periodic_T p1, Periodic_T p2 => (p1 == p2)%C
    | Sporadic_T s1, Sporadic_T s2 => (s1 == s2)%C
    | ArrivalPrefix_T s1, ArrivalPrefix_T s2 => (s1 == s2)%C
    | _, _ => false
    end.

  (** The first component of arrival-curve prefix [ac_prefix] is called horizon. *)
  Definition horizon_of_T (ac_prefix_vec : T * seq (T * T)) := fst ac_prefix_vec.

  (** The second component of [ac_prefix] is called steps. *)
  Definition steps_of_T (ac_prefix_vec : T * seq (T * T)) := snd ac_prefix_vec.

  (** The time steps of [ac_prefix] are the first components of the
      steps. That is, these are time instances before the horizon
      where the corresponding arrival curve makes a step. *)
  Definition time_steps_of_T (ac_prefix_vec : T * seq (T * T)) := map fst (steps_of_T ac_prefix_vec).

  (** The function [step_at] returns the last step ([duration ×
      value]) such that [duration ≤ t]. *)
  Definition step_at_T (ac_prefix_vec : T * seq (T * T)) (t : T) :=
    (last (0, 0) [ seq step <- steps_of_T ac_prefix_vec | fst step <= t ])%C.

  (** The function [value_at] returns the _value_ of the last step
      ([duration × value]) such that [duration ≤ t] *)
  Definition value_at_T (ac_prefix_vec : T * seq (T * T)) (t : T) := snd (step_at_T ac_prefix_vec t).

  (** Finally, we define a generic version of the function [extrapolated_arrival_curve]
      that performs the periodic extension of the arrival-curve prefix (and
      hence, defines an arrival curve). *)
  Definition extrapolated_arrival_curve_T (ac_prefix_vec : T * seq (T * T)) (t : T) :=
    let h := horizon_of_T ac_prefix_vec in
    (t %/ h * value_at_T ac_prefix_vec h + value_at_T ac_prefix_vec (t %% h))%C.

  (** Steps should be strictly increasing both in time steps and values. *)
  Definition ltn_steps_T (a b : T * T) := (fst a < fst b)%C && (snd a < snd b)%C.
  Definition sorted_ltn_steps_T (ac_prefix : ArrivalCurvePrefix) :=
    sorted ltn_steps_T (steps_of_T ac_prefix).

  (** We also define a predicate for non-decreasing order that is
      more convenient for proving some of the claims. *)
  Definition leq_steps_T (a b : T * T) := (fst a <= fst b)%C && (snd a <= snd b)%C.

  (** Horizon should be positive. *)
  Definition positive_horizon_T (ac_prefix : ArrivalCurvePrefix) := (0 < horizon_of_T ac_prefix)%C.

  (** Horizon should bound time steps. *)
  Definition large_horizon_T (ac_prefix : ArrivalCurvePrefix) : bool :=
    all (fun s => s <= horizon_of_T ac_prefix)%C (time_steps_of_T ac_prefix).

  (** There should be no infinite arrivals; that is, [value_at 0 = 0]. *)
  Definition no_inf_arrivals_T (ac_prefix : ArrivalCurvePrefix) :=
    (value_at_T ac_prefix 0 == 0)%C.

  (** Bursts must be specified; that is, [steps_of] should contain a
      pair [(ε, b)]. *)
  Definition specified_bursts_T (ac_prefix : ArrivalCurvePrefix) :=
    has (fun step => step == 1)%C (time_steps_of_T ac_prefix).

  (** The conjunction of the 5 afore-defined properties defines a
      valid arrival-curve prefix. *)
  Definition valid_extrapolated_arrival_curve_T (ac_prefix : ArrivalCurvePrefix) : bool :=
    positive_horizon_T ac_prefix
    && large_horizon_T ac_prefix
    && no_inf_arrivals_T ac_prefix
    && specified_bursts_T ac_prefix
    && sorted_ltn_steps_T ac_prefix.

End Definitions.

Section Translation.

  (** First, we define the function that maps a generic arrival-curve prefix to a natural-number
      one... *)
  Definition ACPrefixT_to_ACPrefix (ac_prefix_vec_T : N * seq (N * N)) : ArrivalCurvePrefix :=
    (nat_of_bin (horizon_of_T ac_prefix_vec_T), m_tb2tn (steps_of_T ac_prefix_vec_T)).

  (** ... and its function relationship. *)
  Definition RArrivalCurvePrefix := fun_hrel ACPrefixT_to_ACPrefix.

  (** Next, we define the converse function, mapping a natural-number arrival-curve prefix
      task to a generic one. *)
  Definition ACPrefix_to_ACPrefixT (ac_prefix_vec : ArrivalCurvePrefix) : (N * seq (N * N)) :=
    (bin_of_nat (horizon_of ac_prefix_vec), m_tn2tb (steps_of ac_prefix_vec)).

  (** Further, we define the function that maps a generic task arrival-bound to a natural-number
      one... *)
  Definition task_abT_to_task_ab (ab : @task_arrivals_bound_T N) : task_arrivals_bound :=
    match ab with
    | Periodic_T p => Periodic p
    | Sporadic_T m => Sporadic m
    | ArrivalPrefix_T ac_prefix_vec => ArrivalPrefix (ACPrefixT_to_ACPrefix ac_prefix_vec)
    end.

  (** ... and its function relationship. *)
  Definition Rtask_ab := fun_hrel task_abT_to_task_ab.

  (** Finally, we define the converse function, mapping a natural-number task arrival-bound
      task to a generic one. *)
  Definition task_ab_to_task_abT (ab : task_arrivals_bound) : @task_arrivals_bound_T N :=
    match ab with
    | Periodic p => Periodic_T (bin_of_nat p)
    | Sporadic m => Sporadic_T (bin_of_nat m)
    | ArrivalPrefix ac_prefix_vec => ArrivalPrefix_T (ACPrefix_to_ACPrefixT ac_prefix_vec)
    end.

End Translation.

Section Lemmas.

  (** We prove that [leq_steps_T] is transitive... *)
  Lemma leq_stepsT_is_transitive :
    transitive (@leq_steps_T N leq_N).
  Proof.
    move=> a b c /andP [FSTab SNDab] /andP [FSTbc SNDbc].
    rewrite /leq_steps_T.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; simpl in *.
    apply/andP; split.
    - by apply /N.leb_spec0; eapply N.le_trans;
      [apply /N.leb_spec0; apply FSTab
      | apply /N.leb_spec0; apply FSTbc].
    - by apply /N.leb_spec0; eapply N.le_trans;
      [apply /N.leb_spec0; apply SNDab
      | apply /N.leb_spec0; apply SNDbc].
  Qed.

  (** ... and so is [ltn_steps_T]. *)
  Lemma ltn_stepsT_is_transitive :
    transitive (@ltn_steps_T N lt_N).
  Proof.
    move=> a b c /andP [FSTab SNDab] /andP [FSTbc SNDbc].
    rewrite /ltn_steps_T.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; simpl in *.
    apply/andP; split.
    - by apply /N.ltb_spec0; eapply N.lt_trans;
      [apply /N.ltb_spec0; apply FSTab
      | apply /N.ltb_spec0; apply FSTbc].
    - by apply /N.ltb_spec0; eapply N.lt_trans;
      [apply /N.ltb_spec0; apply SNDab
      | apply /N.ltb_spec0; apply SNDbc].
  Qed.

End Lemmas.

(** In this fairly technical section, we prove a series of refinements
    aimed to be able to convert between a standard natural-number task
    and a generic task. *)
Section Refinements.

  (** We prove the refinement for the [leq_steps] function. *)
  Global Instance refine_leq_steps :
    refines (prod_R Rnat Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel leq_steps leq_steps_T.
  Proof.
    rewrite /leq_steps /leq_steps_T refinesE => a a' Ra b b' Rb.
    by apply refinesP; refines_apply.
  Qed.

  (** Next, we prove the refinement for the [ltn_steps] function. *)
  Global Instance refine_ltn_steps :
    refines (prod_R Rnat Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel ltn_steps ltn_steps_T.
  Proof.
    rewrite /ltn_steps /ltn_steps_T refinesE => a a' Ra b b' Rb.
    destruct a as [a1 a2], a' as [a1' a2'], b as [b1 b2], b' as [b1' b2']; simpl in *.
    inversion Ra; subst.
    inversion Rb; subst.
    by apply andb_R; apply refine_ltn.
  Qed.

  (** Next, we prove the refinement for the [ACPrefixT_to_ACPrefix] function. *)
  Local Instance refine_ACPrefixT_to_ACPrefix :
    refines (unify (A:=N * seq (N * N)) ==> prod_R Rnat (list_R (prod_R Rnat Rnat)))%rel ACPrefixT_to_ACPrefix id.
  Proof.
    rewrite refinesE => evec evec' Revec.
    unfold unify  in *; subst evec'.
    destruct evec as [h st].
    apply pair_R.
    - by compute.
    - simpl; clear h; elim: st => [|a st IHst].
      + apply nil_R.
      + simpl; apply cons_R; last by done.
        destruct a; unfold tb2tn, tmap; simpl.
        by apply refinesP; refines_apply.
  Qed.

  (** Next, we prove the refinement for the [ltn_steps_sorted] function. *)
  Global Instance refine_ltn_steps_sorted :
    forall xs xs',
      refines ( list_R (prod_R Rnat Rnat) )%rel xs xs' ->
      refines ( bool_R )%rel (sorted ltn_steps xs) (sorted ltn_steps_T xs').
  Proof.
    elim=> [|x xs IHxs] xs' Rxs.
    { destruct xs' as [ | x' xs']; first by tc.
      by rewrite refinesE in Rxs; inversion Rxs. }
    { destruct xs' as [ | x' xs']; first by rewrite refinesE in Rxs; inversion Rxs.
      rewrite //= !path_sortedE; first last.
      { by apply ltn_steps_is_transitive. }
      { by apply ltn_stepsT_is_transitive. }
      { rewrite refinesE in Rxs; inversion Rxs; subst.
        rewrite refinesE; apply andb_R.
        - apply refinesP; refines_apply.
        - by apply refinesP; apply IHxs; rewrite refinesE. } }
  Qed.

  (** Next, we prove the refinement for the [leq_steps_sorted] function. *)
  Global Instance refine_leq_steps_sorted :
    forall xs xs',
      refines ( list_R (prod_R Rnat Rnat) )%rel xs xs' ->
      refines ( bool_R )%rel (sorted leq_steps xs) (sorted leq_steps_T xs').
  Proof.
    elim=> [|x xs IHxs] xs' Rxs.
    { destruct xs' as [ | x' xs']; first by tc.
      by rewrite refinesE in Rxs; inversion Rxs. }
    { destruct xs' as [ | x' xs']; first by rewrite refinesE in Rxs; inversion Rxs.
      rewrite //= !path_sortedE; first last.
      { by apply leq_steps_is_transitive. }
      { by apply leq_stepsT_is_transitive. }
      { rewrite refinesE in Rxs; inversion Rxs; subst.
        rewrite refinesE; apply andb_R.
        - by apply refinesP; refines_apply.
        - by apply refinesP; apply IHxs; rewrite refinesE. } }
  Qed.

  (** Next, we prove the refinement for the [value_at] function. *)
  Global Instance refine_value_at :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> Rnat ==> Rnat)%rel value_at value_at_T.
  Proof.
    rewrite refinesE => evec evec' Revec δ δ' Rδ.
    unfold value_at, value_at_T, step_at, step_at_T.
    have RP := refines_snd_R Rnat Rnat.
    rewrite refinesE in RP.
    eapply RP; clear RP.
    have RL := @refine_last _ _ (prod_R Rnat Rnat).
    rewrite refinesE in RL.
    apply RL; clear RL.
    - by apply refinesP; refines_apply.
    - apply filter_R.
      + move=> _ _ [n1 n1' Rn1 _ _ _] /=.
        by apply: refinesP; apply: refines_apply.
      + unfold steps_of, steps_of_T.
        by apply refinesP; refines_apply.
  Qed.

  (** Next, we prove the refinement for the [time_steps_of] function. *)
  Global Instance refine_get_time_steps :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> list_R Rnat)%rel time_steps_of time_steps_of_T.
  Proof.
    rewrite refinesE => evec evec' Revec.
    destruct evec as [h st], evec' as [h' st'].
    case: Revec => n1 n1' Rn1 n2 n2' Rn2.
    by apply: refinesP; apply: refines_apply.
  Qed.

  (** Next, we prove the refinement for the [extrapolated_arrival_curve] function. *)
  Global Instance refine_arrival_curve_prefix :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> Rnat ==> Rnat)%rel extrapolated_arrival_curve extrapolated_arrival_curve_T.
  Proof.
    rewrite refinesE => evec evec' Revec δ δ' Rδ.
    unfold extrapolated_arrival_curve, extrapolated_arrival_curve_T.
    by apply refinesP; refines_apply.
  Qed.

  (** Next, we prove the refinement for the [ArrivalCurvePrefix] function. *)
  Global Instance refine_ArrivalPrefix :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> Rtask_ab)%rel ArrivalPrefix ArrivalPrefix_T.
  Proof.
    rewrite refinesE => arrival_curve_prefix arrival_curve_prefix' Rarrival_curve_prefix.
    destruct arrival_curve_prefix as [h steps], arrival_curve_prefix' as [h' steps'].
    case: Rarrival_curve_prefix => {}h {}h' Rh {}steps {}steps' Rsteps.
    rewrite /Rtask_ab /fun_hrel /task_abT_to_task_ab /ACPrefixT_to_ACPrefix /=.
    have ->: nat_of_bin h' = h by rewrite -Rh.
    have ->: m_tb2tn steps' = steps; last by done.
    clear h h' Rh; elim: steps steps' Rsteps => [|a steps IHsteps] steps' Rsteps.
    - by destruct steps'; [done | inversion Rsteps].
    - destruct steps' as [|p steps']; first by inversion Rsteps.
      inversion_clear Rsteps as [|? ? Rap ? ? Rstep].
      rewrite /m_tb2tn/= /tb2tn/tmap/=.
      congr cons; first by case: Rap => _ {}a <- _ b <-.
      exact: IHsteps.
  Qed.

  (** Next, we define some useful equality functions to guide the typeclass engine. *)
  Global Instance eq_listN : eq_of (seq N) := fun x y => x == y.
  Global Instance eq_NlistNN : eq_of (prod N (seq (prod N N))) := fun x y => x == y.
  Global Instance eq_taskab : eq_of (@task_arrivals_bound_T N) := taskab_eqdef_T.

  (** Finally, we prove the refinement for the [ArrivalCurvePrefix] function. *)
  Global Instance refine_task_ab_eq :
    refines (Rtask_ab ==> Rtask_ab ==> bool_R)%rel eqtype.eq_op eq_taskab.
  Proof.
    rewrite refinesE => tb1 tb1' Rtb1 tb2 tb2' Rtb2.
    destruct tb1 as [per1 | spor1 | evec1], tb1' as [per1' | spor1' | evec1'];
      destruct tb2 as [per2 | spor2 | evec2], tb2' as [per2' | spor2' | evec2'].
    all: try (inversion Rtb1; fail); try (inversion Rtb2; fail); try (compute; constructor).
    { replace (Periodic per1 == Periodic per2) with (per1 == per2) by constructor.
      replace (eq_taskab(Periodic_T per1')(Periodic_T per2'))%C with (per1' == per2') by constructor.
      inversion Rtb1; inversion Rtb2; subst; clear.
      by apply refinesP; refines_apply. }
    { replace (Sporadic spor1 == Sporadic spor2) with (spor1 == spor2) by constructor.
      have ->: (eq_taskab (Sporadic_T spor1') (Sporadic_T spor2'))%C = (spor1' == spor2') by constructor.
      inversion Rtb1; inversion Rtb2; subst; clear.
      by apply refinesP; refines_apply. }
    { replace (ArrivalPrefix evec1 == ArrivalPrefix evec2) with (evec1 == evec2) by constructor.
      replace (eq_taskab (ArrivalPrefix_T evec1') (ArrivalPrefix_T evec2'))%C with (evec1' == evec2')%C by constructor.
      inversion Rtb1; inversion Rtb2; subst; clear.
      rename evec1' into evec1, evec2' into evec2.
      destruct evec1 as [h1 evec1], evec2 as [h2 evec2].
      rewrite /ACPrefixT_to_ACPrefix //= !xpair_eqE.
      have -> : ((h1, evec1) == (h2, evec2))%C = ((h1 == h2) && (evec1 == evec2))%C by constructor.
      apply andb_R; first by apply refinesP; refines_apply.
      clear h1 h2; move: evec2; elim: evec1 => [[] //|h1 evec1 IHevec1].
      case=> [//|h2 evec2].
      rewrite //= !eqseq_cons.
      apply andb_R; last by apply IHevec1.
      move: h1 h2 => [n n0] [n1 n2].
      rewrite /tb2tn /tmap /=.
      replace ((n, n0) == (n1, n2)) with ((n == n1) && (n0 == n2)) by constructor.
      replace ((nat_of_bin n, nat_of_bin n0) == (nat_of_bin n1, nat_of_bin n2)) with
          ((nat_of_bin n == nat_of_bin n1) && (nat_of_bin n0 == nat_of_bin n2)) by constructor.
      apply refinesP; refines_apply. }
  Qed.

End Refinements.
