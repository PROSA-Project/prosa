Require Export prosa.implementation.refinements.arrival_curve.

(** In this section, we prove some properties that every valid
    arrival curve prefix entails. *)
Section ValidArrivalCurvePrefixFacts.

  (** Consider a task set with valid arrivals [ts], ... *)
  Variable ts : seq Task.
  Hypothesis H_valid_task_set : task_set_with_valid_arrivals ts.

  (** ... and a task [tsk] belonging to [ts] with positive cost and
      non-zero arrival bound. *)
  Variable tsk : Task.
  Hypothesis H_positive_cost : 0 < task_cost tsk.
  Hypothesis H_tsk_in_ts : tsk \in ts.
  Hypothesis H_positive_step : fst (head (0,0) (steps_of (get_arrival_curve_prefix tsk))) > 0.

  (** First, we show that the arrival curve prefix of [tsk] is valid. *)
  Lemma has_valid_arrival_curve_prefix_tsk :
    has_valid_arrival_curve_prefix tsk.
  Proof.
    move: (H_valid_task_set tsk H_tsk_in_ts); rewrite /valid_arrivals => VALID.
    destruct (arrival_cases tsk) as [[p EQ] | [[m EQ] | [evec EQ]]].
    all: rewrite /has_valid_arrival_curve_prefix /max_arrivals /MaxArrivals /ConcreteMaxArrivals /get_arrival_curve_prefix EQ //=.
    all: rewrite EQ in VALID.
    { exists (inter_arrival_to_prefix p).
      split;[|split;[|split;[|split;[|split]]]] => //=.
      move=> s.
      by rewrite /large_horizon in_cons => /orP [|] /eqP. }
    { exists (inter_arrival_to_prefix m).
      split;[|split;[|split;[|split;[|split]]]] => //=.
      move=> s.
      by rewrite /large_horizon in_cons => /orP [|] /eqP. }
    { by exists evec; split => //; apply /valid_arrival_curve_prefix_P. }
  Qed.

  (** Next, we show that each time step of the arrival curve prefix must be
      positive. *)
  Lemma steps_are_positive_if_first_step_is_positive :
    forall st,
      st \in get_time_steps_of_task tsk -> st > 0.
  Proof.
    intros st IN; unfold get_time_steps_of_task in *.
    move: (H_valid_task_set) => VAL; specialize (VAL _ H_tsk_in_ts).
    unfold valid_arrivals in VAL; unfold get_arrival_curve_prefix in *.
    destruct (task_arrival tsk) as [a|a|a].
    { by unfold inter_arrival_to_prefix, time_steps_of in *; simpl in IN;
        move: IN; rewrite mem_seq1 => /eqP EQ; subst. }
    { by unfold inter_arrival_to_prefix, time_steps_of in *; simpl in IN;
        move: IN; rewrite mem_seq1 => /eqP EQ; subst. }
    { destruct a as [h [ | st0 sts]]; first by done.
      move: IN => /mapP [[t v] IN EQ]; simpl in *; subst st.
      move: IN; rewrite in_cons => /orP [/eqP EQ | IN]; first by subst.
      move: VAL => /valid_arrival_curve_prefix_P VAL.
      destruct VAL as [_ [_ [_ [_ SORT]]]].
      unfold sorted_ltn_steps in *; simpl in *.
      rewrite (@path_sorted_inE _ predT) in SORT; last apply all_predT.
      + move: SORT => /andP [/allP ALL _].
        specialize (ALL (t,v) IN); move: ALL.
        destruct st0; simpl in *.
        by move => /andP //= => [[LT1 LT2]]; lia.
      + by intros ? ? ? _ _ _; apply ltn_steps_is_transitive. }
  Qed.

  (** Next, we show that even shifting the time steps by a positive
      offset, they remain positive. *)
  Lemma nonshifted_offsets_are_positive :
    forall A offs,
      A \in repeat_steps_with_offset tsk offs -> A > 0.
  Proof.
    intros A offs IN.
    move: IN  => /flatten_mapP [o INo IN].
    move: IN => /mapP [st IN EQ]; subst A.
    rewrite addn_gt0; apply/orP; left.
    by apply steps_are_positive_if_first_step_is_positive.
  Qed.

  (** Finally, we show that the time steps are strictly increasing. *)
  Lemma time_steps_sorted :
    sorted ltn (get_time_steps_of_task tsk).
  Proof.
    move: (H_valid_task_set) => VALID; rewrite /get_time_steps_of_task.
    move: (has_valid_arrival_curve_prefix_tsk) => [arrival_curve_prefix [EQ [POSh [LARGEh [NOINF [BUR SORT]]]]]].
    rewrite EQ.
    eapply (homo_sorted _ _ SORT).
    Unshelve.
    by move => x y; rewrite /ltn_steps => /andP[LT _].
  Qed.

End ValidArrivalCurvePrefixFacts.
