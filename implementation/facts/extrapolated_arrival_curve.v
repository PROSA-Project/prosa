Require Export prosa.behavior.time.
Require Export prosa.util.all.
Require Export prosa.implementation.definitions.extrapolated_arrival_curve.

(** In this file, we prove basic properties of the arrival-curve
    prefix and the [extrapolated_arrival_curve] function. *)

(** We start with basic facts about the relations [ltn_steps] and [leq_steps]. *)
Section BasicFacts.

  (** We show that the relation [ltn_steps] is transitive. *)
  Lemma ltn_steps_is_transitive :
    transitive ltn_steps.
  Proof.
    move=> a b c /andP [FSTab SNDab] /andP [FSTbc SNDbc].
    by apply /andP; split; lia.
  Qed.

  (** Next, we show that the relation [leq_steps] is reflexive... *)
  Lemma leq_steps_is_reflexive :
    reflexive leq_steps.
  Proof.
    move=> [l r].
    rewrite /leq_steps.
    by apply /andP; split.
  Qed.

  (** ... and transitive. *)
  Lemma leq_steps_is_transitive :
    transitive leq_steps.
  Proof.
    move=> a b c /andP [FSTab SNDab] /andP [FSTbc SNDbc].
    by apply /andP; split; lia.
  Qed.

End BasicFacts.

(** In the following section, we prove a few properties of
    arrival-curve prefixes assuming that there are no infinite
    arrivals and that the list of steps is sorted according to the
    [leq_steps] relation. *)
Section ArrivalCurvePrefixSortedLeq.

  (** Consider an arbitrary [leq]-sorted arrival-curve prefix without
      infinite arrivals. *)
  Variable ac_prefix : ArrivalCurvePrefix.
  Hypothesis H_sorted_leq : sorted_leq_steps ac_prefix.
  Hypothesis H_no_inf_arrivals : no_inf_arrivals ac_prefix.

  (** We prove that [value_at] is monotone with respect to the relation [<=]. *)
  Lemma value_at_monotone :
    monotone leq (value_at ac_prefix).
  Proof.
    intros t1 t2 LE; clear H_no_inf_arrivals.
    unfold sorted_leq_steps, value_at, step_at, steps_of in *.
    destruct ac_prefix as [h steps]; simpl.
    have GenLem:
      forall t__d1 v__d1 t__d2 v__d2,
        v__d1 <= v__d2 ->
        all (leq_steps (t__d1, v__d1)) steps ->
        all (leq_steps (t__d2, v__d2)) steps ->
        snd (last (t__d1, v__d1) [seq step <- steps | fst step <= t1]) <= snd (last (t__d2, v__d2) [seq step <- steps | fst step <= t2]).
    { have steps_sorted := H_sorted_leq; clear H_sorted_leq.
      elim: steps steps_sorted => [//|[t__c v__c] steps IHsteps] steps_sorted.
      simpl; intros *; move => LEv /andP [LTN1 /allP ALL1] /andP [LTN2 /allP ALL2].
      move: (steps_sorted); rewrite //= (@path_sorted_inE _ predT leq_steps); first last.
      { by apply/allP. }
      { by intros ? ? ? _ _ _; apply leq_steps_is_transitive. }
      move => /andP [ALL SORT].
      destruct (leqP (fst (t__c, v__c)) t1) as [R1 | R1], (leqP (fst (t__c, v__c)) t2) as [R2 | R2]; simpl in *.
      { by rewrite R1 R2 //=; apply: IHsteps. }
      { lia. }
      { rewrite ltnNge -eqbF_neg in R1; move: R1 => /eqP ->; rewrite R2 //=; apply IHsteps => //.
        - by move: LTN1; rewrite /leq_steps => /andP //= [_ LEc].
        - by apply/allP.
      }
      { rewrite ltnNge -eqbF_neg in R1; move: R1 => /eqP ->.
        rewrite ltnNge -eqbF_neg in R2; move: R2 => /eqP ->.
        by apply IHsteps => //; apply/allP.
      }
    }
    by apply: GenLem => [//||];  apply/allP; intros x _; rewrite /leq_steps //=.
  Qed.

  (** Next, we prove a correctness claim stating that if [value_at]
      makes a step at time instant [t + ε] (that is, [value_at t <
      value_at (t + ε)]), then [steps_of ac_prefix] contains a step
      [(t + ε, v)] for some [v]. *)
  Lemma value_at_change_is_in_steps_of :
    forall t,
      value_at ac_prefix t < value_at ac_prefix (t + ε) ->
      exists v, (t + ε, v) \in steps_of ac_prefix.
  Proof.
    move=> t LT /=.
    unfold value_at, step_at in LT.
    destruct ac_prefix as [h2 steps]; simpl in LT.
    rewrite [in X in _ < X](sorted_split _ _ fst t) /= in LT.
    { rewrite [in X in _ ++ X](eq_filter (a2 := fun x => fst x == t + ε)) in LT; last first.
      { by move=> [a b] /=; lia. }
      { destruct ([seq x <- steps | fst x == t + ε]) as [|p l] eqn:LST => //=.
        { rewrite [in X in X ++ _](eq_filter (a2 := fun x => fst x <= t)) in LT; last first.
          { clear; intros [a b]; simpl.
            destruct (leqP a t).
            - by rewrite Bool.andb_true_r; apply/eqP; lia.
            - by rewrite Bool.andb_false_r.
          }
          { by rewrite cats0 ltnn in LT. }
        }
        { have: p \in [seq x <- steps | x.1 == t + 1]
            by rewrite LST; apply: mem_head.
          move=> {LT} {LST}; move: p => //= [t_c v_c].
          by rewrite mem_filter => //= /andP [/eqP ->].
        }
      }
    }
    { move: (H_sorted_leq); clear H_sorted_leq; rewrite /sorted_leq_steps //= => SORT; clear H_no_inf_arrivals.
      elim: steps SORT => [//|a steps IHsteps] /= SORT.
      move: SORT; rewrite path_sortedE; auto using leq_steps_is_transitive; move => /andP [LE SORT].
      apply IHsteps in SORT.
      rewrite path_sortedE; last by intros ? ? ? LE1 LE2; lia.
      apply/andP; split=> [|//].
      apply/allP; intros [x y] IN.
      by move: LE => /allP LE; specialize (LE _ IN); move: LE => /andP [LT _].
    }
  Qed.

End ArrivalCurvePrefixSortedLeq.

(* In the next section, we make the stronger assumption that
   arrival-curve prefixes are sorted according to the [ltn_steps]
   relation. *)
Section ArrivalCurvePrefixSortedLtn.

  (** Consider an arbitrary [ltn]-sorted arrival-curve prefix without
      infinite arrivals. *)
  Variable ac_prefix : ArrivalCurvePrefix.
  Hypothesis H_sorted_ltn : sorted_ltn_steps ac_prefix. (* Stronger assumption. *)
  Hypothesis H_no_inf_arrivals : no_inf_arrivals ac_prefix.

  (** First, we show that an [ltn]-sorted arrival-curve prefix is an
      [leq]-sorted arrival-curve prefix. *)
  Lemma sorted_ltn_steps_imply_sorted_leq_steps_steps :
    sorted_leq_steps ac_prefix.
  Proof.
    destruct ac_prefix as [d l]; unfold sorted_leq_steps, sorted_ltn_steps in *; simpl in *.
    clear H_no_inf_arrivals d.
    destruct l => [//|]; simpl in *.
    eapply sub_path; last by apply H_sorted_ltn.
    intros [a1 b1] [a2 b2] LT.
    by unfold ltn_steps, leq_steps in *; simpl in *; lia.
  Qed.

  (** Next, we show that [step_at 0] is equal to [(0, 0)]. *)
  Lemma step_at_0_is_00 :
    step_at ac_prefix 0 = (0, 0).
  Proof.
    unfold step_at; destruct ac_prefix as [h [ | [t v] steps]] => [//|].
    have TR := ltn_steps_is_transitive.
    move: (H_sorted_ltn); clear H_sorted_ltn; rewrite /sorted_ltn_steps //= path_sortedE // => /andP [ALL LT].
    have EM : [seq step <- steps | fst step <= 0] = [::].
    { apply filter_in_pred0; intros [t' v'] IN.
      move: ALL => /allP ALL; specialize (ALL _ IN); simpl in ALL.
      by rewrite -ltnNge //=; move: ALL; rewrite /ltn_steps //= => /andP [T _ ]; lia. }
    rewrite EM; destruct (posnP t) as [Z | POS].
    { subst t; simpl.
      move: H_no_inf_arrivals; rewrite /no_inf_arrivals /value_at /step_at //= EM //=.
      by move => /eqP EQ; subst v. }
    { by rewrite leqNgt POS //=. }
  Qed.

  (** We show that functions [steps_of] and [step_at] are consistent.
      That is, if a pair [(t, v)] is in steps of [ac_prefix], then
      [step_at t] is equal to [(t, v)]. *)
  Lemma step_at_agrees_with_steps_of :
    forall t v, (t, v) \in steps_of ac_prefix -> step_at ac_prefix t = (t, v).
  Proof.
    case: ac_prefix H_sorted_ltn => [h steps] + //= ? ? IN.
    move: IN => /in_cat //= [steps__l [steps__r ->]] /sorted_cat //=; case => //= [|_ +]; first by apply ltn_steps_is_transitive.
    rewrite /step_at filter_cat last_cat (nonnil_last _ _ (0,0)); last by rewrite //= leqnn.
    rewrite //= path_sortedE; auto using ltn_steps_is_transitive; rewrite //= leqnn => /andP [ALL SORT].
    replace (filter _ _ ) with (@nil (nat * nat)) => [//|].
    rewrite filter_in_pred0 // => x IN; rewrite -ltnNge.
    by move: ALL => /allP ALL; move: (ALL _ IN); rewrite /ltn_steps //= => /andP [LT _ ].
  Qed.

End ArrivalCurvePrefixSortedLtn.

(** In this section, we prove a few basic properties of
    [extrapolated_arrival_curve] function, such as (1) monotonicity of
    [extrapolated_arrival_curve] or (2) implications of the fact that
    [extrapolated_arrival_curve] makes a step at time [t + ε]. *)
Section ExtrapolatedArrivalCurve.

  (** Consider an arbitrary [leq]-sorted arrival-curve prefix without infinite arrivals. *)
  Variable ac_prefix : ArrivalCurvePrefix.
  Hypothesis H_positive : positive_horizon ac_prefix.
  Hypothesis H_sorted_leq : sorted_leq_steps ac_prefix.

  (** Let [h] denote the horizon of [ac_prefix] ... *)
  Let h := horizon_of ac_prefix.

  (** ... and [prefix] be shorthand for [value_at ac_prefix]. *)
  Let prefix := value_at ac_prefix.

  (** We show that [extrapolated_arrival_curve] is monotone. *)
  Lemma extrapolated_arrival_curve_is_monotone :
    monotone leq (extrapolated_arrival_curve ac_prefix).
  Proof.
    intros t1 t2 LE; unfold extrapolated_arrival_curve.
    replace (horizon_of _) with h => [|//].
    move: LE; rewrite leq_eqVlt => /orP [/eqP EQ | LTs].
    { by subst t2. }
    { have ALT : (t1 %/ h == t2 %/ h) \/ (t1 %/ h < t2 %/ h).
      { by apply/orP; rewrite -leq_eqVlt; apply leq_div2r, ltnW. }
      move: ALT => [/eqP EQ | LT].
      { rewrite EQ leq_add2l; apply value_at_monotone => //.
        by apply eqdivn_leqmodn; lia.
      }
      { have EQ: exists k, t1 + k = t2 /\ k > 0.
        { exists (t2 - t1); split; lia. }
        destruct EQ as [k [EQ POS]]; subst t2; clear LTs.
        rewrite divnD//.
        rewrite !mulnDl -!addnA leq_add2l.
        destruct (leqP h k) as [LEk|LTk].
        { eapply leq_trans; last by apply leq_addr.
          move: LEk; rewrite leq_eqVlt => /orP [/eqP EQk | LTk].
          { by subst; rewrite divnn POS mul1n; apply value_at_monotone, ltnW, ltn_pmod. }
          { rewrite -[value_at _ (t1 %% h)]mul1n; apply leq_mul.
            - by rewrite divn_gt0; [apply: ltnW|].
            - by apply value_at_monotone, ltnW, ltn_pmod.
          }
        }
        { rewrite divn_small // mul0n add0n.
          rewrite divnD // in LT; move: LT; rewrite -addnA -addn1 leq_add2l divn_small // add0n.
          rewrite lt0b => F; rewrite F; clear F.
          rewrite mul1n; eapply leq_trans; last by apply leq_addr.
          by apply value_at_monotone, ltnW, ltn_pmod.
        }
      }
    }
  Qed.

  (** Finally, we show that if
      [extrapolated_arrival_curve t <> extrapolated_arrival_curve (t + ε)],
      then either (1) [t + ε] divides [h] or (2) [prefix (t mod h) < prefix ((t + ε) mod h)]. *)
  Lemma extrapolated_arrival_curve_change :
    forall t,
      extrapolated_arrival_curve ac_prefix t != extrapolated_arrival_curve ac_prefix (t + ε) ->
      (* 1 *) t %/ h < (t + ε) %/ h
      \/ (* 2 *) t %/ h = (t + ε) %/ h /\ prefix (t %% h) < prefix ((t + ε) %% h).
  Proof.
    intros t NEQ.
    have LT := ltn_neqAle (extrapolated_arrival_curve ac_prefix t) (extrapolated_arrival_curve ac_prefix (t + ε)).
    rewrite NEQ in LT; rewrite extrapolated_arrival_curve_is_monotone in LT; last by apply leq_addr.
    clear NEQ; simpl in LT.
    unfold extrapolated_arrival_curve in LT.
    replace (horizon_of _) with h in LT => [|//].
    have AF :
      forall s1 s2 m x y,
        s1 <= s2 ->
        m * s1 + x < m * s2 + y ->
        s1 < s2 \/ s1 = s2 /\ x < y.
    {  clear; intros s1 s2 m x y LEs LT.
       move: LEs; rewrite leq_eqVlt => /orP [/eqP EQ | LTs].
       { by subst s2; rename s1 into s; right; split; [|lia]. }
       { by left. }
    }
    apply AF with (m := prefix h).
    { by apply leq_div2r, leq_addr. }
    { by rewrite ![prefix _ * _]mulnC; apply LT. }
  Qed.

End ExtrapolatedArrivalCurve.
