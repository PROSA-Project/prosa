Require Export prosa.implementation.refinements.arrival_curve_prefix.

(** In this section, we provide definitions and lemmas to show
    Abstract RTA' s search space can be rewritten in an equivalent,
    computation-oriented way. *)
Section FastSearchSpaceComputation.

  (** Let L be a constant which bounds any busy interval of task [tsk]. *)
  Variable L : duration.

  (** Consider a task set [ts] with valid arrivals... *)
  Variable ts : seq Task.
  Hypothesis H_valid_task_set : task_set_with_valid_arrivals ts.

  (** ... and a task [tsk] of [ts] with positive cost. *)
  Variable tsk : Task.
  Hypothesis H_positive_cost : 0 < task_cost tsk.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  Section Definitions.

    (** We generically define the search space for fixed-priority tasks in
      the interval <<[l,r)>> by repeating the time steps of the task
      in the interval <<[l*h,r*h)>>. *)
    Definition search_space_arrival_curve_prefix_FP_h (tsk : Task) l r :=
      let h := get_horizon_of_task tsk in
      let offsets := map (muln h) (iota l r) in
      let arrival_curve_prefix_offsets := repeat_steps_with_offset tsk offsets in
      map predn arrival_curve_prefix_offsets.

    (** By using the above definition, we give a concrete definition of
      the search space for fixed-priority tasks. *)
    Definition search_space_arrival_curve_prefix_FP (tsk : Task) L :=
      let h := get_horizon_of_task tsk in
      search_space_arrival_curve_prefix_FP_h (tsk : Task) 0 (L %/h).+1.

  End Definitions.

  Section Facts.

    (** We begin by showing that either each time step of an arrival curve prefix
        is either strictly less than the horizon, or it is the horizon. *)
    Lemma steps_lt_horizon_last_eq_horizon :
      (forall s, s \in get_time_steps_of_task tsk -> s < get_horizon_of_task tsk) \/
      (last0 (get_time_steps_of_task tsk) = get_horizon_of_task tsk).
    Proof.
      move: (has_valid_arrival_curve_prefix_tsk _ H_valid_task_set _ H_tsk_in_ts).
      move => [arrival_curve_prefix [EQ [POSh [LARGEh [NOINF [BUR SORT]]]]]].
      destruct (ltngtP (last0 (get_time_steps_of_task tsk)) (get_horizon_of_task tsk))
        as [GT1 | LT1 | EQ1]; last by right.
      { left.
        move => step IN.
        apply leq_ltn_trans with (n:=last0 (get_time_steps_of_task tsk)) => //.
        move: (time_steps_sorted ts H_valid_task_set tsk H_tsk_in_ts).
        rewrite ltn_sorted_uniq_leq => /andP [TS_UNIQ TS_SORT].
        apply (sorted_leq_index leq_trans leqnn TS_SORT step _ IN) => //=.
        - by destruct get_time_steps_of_task; last by rewrite /last0 //=; apply mem_last.
        - destruct get_time_steps_of_task; rewrite //= -index_mem in IN.
          by rewrite /last0; simpl (last 0 _); rewrite index_last. }
      { exfalso. (* h is at least the last step *)
        destruct get_time_steps_of_task as [|d l] eqn:TS => //.
        have IN: last0 (d::l) \in d::l by rewrite /last0 //=; apply mem_last.
        unfold large_horizon, get_time_steps_of_task in *.
        rewrite EQ in TS; rewrite TS in LARGEh.
        apply LARGEh in IN.
        by rewrite /get_horizon_of_task EQ in LT1; lia. }
    Qed.

    (** Next, we show that for each offset [A] in the search space for fixed-priority
        tasks, either (1) [A+ε] is zero or a multiple of the horizon, offset by
        one of the time steps of the arrival curve prefix, or (2) [A+ε] is
        exactly a multiple of the horizon. *)
    Lemma structure_of_correct_search_space :
      forall A,
        A < L ->
        task_rbf tsk A != task_rbf tsk (A + ε) ->
        (exists i t,
            i < (L %/ get_horizon_of_task tsk).+1
            /\ (t \in get_time_steps_of_task tsk)
            /\ A + ε = i * get_horizon_of_task tsk + t )
        \/ (exists i,
              i < (L %/ get_horizon_of_task tsk).+1
              /\ A + ε = i * get_horizon_of_task tsk).
    Proof.
      move: (has_valid_arrival_curve_prefix_tsk ts H_valid_task_set tsk H_tsk_in_ts).
      move=> [evec [EQ [POSh [LARGEh [NOINF [BUR SORT]]]]]] A LT_L NEQ.
      rewrite eqn_pmul2l // /max_arrivals /MaxArrivals /ConcreteMaxArrivals
              /concrete_max_arrivals EQ in NEQ.
      rewrite /get_horizon_of_task EQ.
      move: (sorted_ltn_steps_imply_sorted_leq_steps_steps _ SORT NOINF) => SORT_LEQ.
      unfold positive_horizon in *; set (h := horizon_of evec) in *.
      move: (extrapolated_arrival_curve_change evec POSh SORT_LEQ A NEQ) => [LT|[EQdiv LTe]].
      { right.
        exists ((A+ε) %/ h); split; first by rewrite ltnS leq_div2r // ; lia.
        by symmetry; apply /eqP; rewrite -dvdn_eq; by apply ltdivn_dvdn. }
      { left.
        exists ((A + ε) %/ h), (step_at evec ((A + ε) %% h)).1; split; last split.
        { by rewrite addn1 ltnS; apply leq_div2r. }
        { rewrite /get_time_steps_of_task EQ.
          have-> := @map_f _ _ fst (steps_of _) (last (0, 0) [seq s <- _ | s.1 <= (A+ε)%%h])=> //.
          have EQeps: (A + ε) %% h = A %% h + ε by apply addn1_modn_commute.
          rewrite EQeps in LTe.
          move: (value_at_change_is_in_steps_of _ SORT_LEQ NOINF _ LTe) => [v IN].
          rewrite -EQeps in IN; apply filter_last_mem; apply /hasP.
          by exists ((A+ε) %% h, v). }
        { case (extrapolated_arrival_curve_change _ POSh SORT_LEQ _ NEQ) as [EQs|[EQs LT]].
          { apply ltdivn_dvdn in EQs; move: EQs => /dvdnP [k EQs]; rewrite EQs.
            by rewrite modnMl step_at_0_is_00; [rewrite addn0 mulnK | apply SORT |]. }
          { subst h; set (h := horizon_of evec) in *.
            rewrite {1}[_ + _](divn_eq _ h).
            apply/eqP; rewrite eqn_add2l; apply/eqP.
            rewrite modnD //= [h <= _]leqNgt addmod_le_mod //= subn0 in LT.
            have EQ1: 1%%h= 1 by apply modn_small; case h as [|[|h]]; rewrite //= in EQs; lia.
            rewrite EQ1 in LT; apply value_at_change_is_in_steps_of in LT => //.
            case LT as [v IN].
            rewrite modnD //= [h <= _]leqNgt addmod_le_mod //=.
            apply step_at_agrees_with_steps_of in IN => //.
            by rewrite subn0 !EQ1 IN. } } }
    Qed.

    (** Conversely, every multiple of the horizon that is strictly less than [L] is contained
        in the search space for fixed-priority tasks... *)
    Lemma multiple_of_horizon_in_approx_ss :
      forall A,
        A < L ->
        get_horizon_of_task tsk %| A ->
        A \in search_space_arrival_curve_prefix_FP tsk L.
    Proof.
      move: (has_valid_arrival_curve_prefix_tsk ts H_valid_task_set tsk H_tsk_in_ts) => [evec [EMAX VALID]].
      intros A LT DIV; rewrite /search_space_arrival_curve_prefix_FP.
      destruct VALID as [POSh [LARGEh [NOINF [BUR SORT]]]].
      replace A with (A + ε - ε); last by lia.
      rewrite subn1; apply map_f.
      set (h := get_horizon_of_task tsk) in *.
      rewrite /repeat_steps_with_offset; apply/flatten_mapP.
      move: DIV => /dvdnP [k DIV]; subst A.
      exists (k * h).
      { rewrite mulnC; apply map_f.
        rewrite mem_iota; apply/andP; split; first by apply leq0n.
        rewrite add0n ltnS leq_divRL //.
        rewrite /specified_bursts in BUR.
        by rewrite /h /get_horizon_of_task EMAX. }
      { rewrite /time_steps_with_offset addnC.
        have MFF := map_f  (fun t0 => t0 + k * h); apply: MFF.
        by rewrite /get_time_steps_of_task EMAX; apply BUR. }
    Qed.

    (** ... and every [A] for which [A+ε] is a multiple of the horizon offset by a
        time step of the arrival curve prefix is also in the search space for
        fixed-priority tasks. *)
    Lemma steps_in_approx_ss :
      forall i t A,
        i < (L %/ get_horizon_of_task tsk).+1 ->
        (t \in get_time_steps_of_task tsk) ->
        A + ε = i * get_horizon_of_task tsk + t ->
        A \in search_space_arrival_curve_prefix_FP tsk L.
    Proof.
      move: (H_valid_task_set) => VALID; intros i t A LT IN EQ; rewrite /search_space_arrival_curve_prefix_FP.
      replace A with (A + ε - ε); last by lia.
      rewrite subn1; apply map_f.
      set (h := get_horizon_of_task tsk) in *.
      rewrite /repeat_steps_with_offset; apply/flatten_mapP.
      exists (i * h); first by rewrite mulnC; apply map_f; rewrite mem_iota; lia.
      unfold time_steps_with_offset.
      rewrite EQ addnC.
      by apply (map_f (fun t0 => t0 + i * h) IN).
    Qed.

    (** Next, we show that if the horizon of the arrival curve prefix divides [A+ε],
     then [A] is not contained in the search space for fixed-priority tasks.  *)
    Lemma constant_max_arrivals :
      forall A,
        (forall s, s \in get_time_steps_of_task tsk -> s < get_horizon_of_task tsk) ->
        get_horizon_of_task tsk %| (A + ε) ->
        max_arrivals tsk A = max_arrivals tsk (A + ε).
    Proof.
      move: (has_valid_arrival_curve_prefix_tsk ts H_valid_task_set tsk H_tsk_in_ts).
      move=> [evec [EMAX [POSh [LARGEh [NOINF [BUR SORT]]]]]] A LTH DIV.
      rewrite /max_arrivals /ConcreteMaxArrivals /concrete_max_arrivals EMAX.
      rewrite /get_horizon_of_task EMAX in DIV; move: (DIV) => /eqP MOD0.
      rewrite /extrapolated_arrival_curve.
      set (h := horizon_of evec) in *; set (vec := value_at evec) in *.
      destruct (ltngtP 1 h) as [GT1|LT1|EQ1].
      { move: NOINF => /eqP NOINF.
        rewrite MOD0 {4}/vec NOINF addn0.
        have -> : vec (A %% h) = vec h.
        { rewrite /vec /value_at.
          have -> : ((step_at evec (A %% h)) = (step_at evec h)) => //.
          rewrite (pred_Sn A) -addn1 modn_pred; [|repeat destruct h as [|h]=> //|lia].
          rewrite /step_at DIV.
          have -> : [seq step <- steps_of evec | step.1 <= h] = steps_of evec.
          { apply /all_filterP /allP => [step IN]; apply ltnW; subst h.
            move: LTH; rewrite /get_horizon_of_task EMAX => -> //.
            rewrite /get_time_steps_of_task EMAX.
            by apply (map_f fst). }
          have -> : [seq step <- steps_of evec | step.1 <= h.-1] = steps_of evec => //.
          apply /all_filterP /allP => [step IN]; subst h.
          move: LTH; rewrite /get_horizon_of_task EMAX => VALID.
          specialize (VALID step.1).
          feed VALID; first by rewrite /get_time_steps_of_task EMAX; apply (map_f fst).
          by destruct (horizon_of evec).
        }
        rewrite -mulSnr {1}(pred_Sn A) divn_pred -(addn1 A) DIV subn1 prednK //=.
        move: DIV => /dvdnP [k EQk]; rewrite EQk.
        by destruct k;[lia | rewrite mulnK]. }
      { replace h with 0; rewrite /positive_horizon in POSh; lia. }
      { exfalso.
        rewrite /get_time_steps_of_task EMAX in LTH.
        specialize (LTH _ BUR).
        move: LTH; rewrite ltnNge => /negP CONTR; apply: CONTR.
        by unfold h in *; rewrite /get_horizon_of_task EMAX -EQ1. }
    Qed.

    (** Finally, we show that steps in the request-bound function correspond to
        points in the search space for fixed-priority tasks. *)
    Lemma task_search_space_subset :
      forall A,
        A < L ->
        task_rbf tsk A != task_rbf tsk (A + ε) ->
        A \in search_space_arrival_curve_prefix_FP tsk L.
    Proof.
      intros A LT_L IN.
      destruct (get_horizon_of_task tsk %|A) eqn:DIV;
        first by apply multiple_of_horizon_in_approx_ss.
      move: (structure_of_correct_search_space _ LT_L IN).
      move=> [[i [t [LT [INt EQ]]]] | [i [LT EQ]]]; first by eapply steps_in_approx_ss; eauto.
      destruct (steps_lt_horizon_last_eq_horizon) as [LTh | EQh].
      { exfalso. (* Can't be in search space if h > last step *)
        move: (H_valid_task_set) => VALID; specialize (VALID _ H_tsk_in_ts).
        move: (has_valid_arrival_curve_prefix_tsk ts H_valid_task_set tsk H_tsk_in_ts).
        move => [evec [EMAXeq [POSh [LARGEh [NOINF [BUR SORT]]]]]].
        rewrite /task_rbf /task_request_bound_function /max_arrivals
                /MaxArrivals /ConcreteMaxArrivals /concrete_max_arrivals
                EMAXeq eqn_mul2l negb_or in IN.
        move: IN => /andP [_ NEQ].
        move: (sorted_ltn_steps_imply_sorted_leq_steps_steps _ SORT NOINF) => SORT_LEQ.
        move: (constant_max_arrivals A LTh) => EQmax.
        feed EQmax; first by rewrite EQ; apply dvdn_mull, dvdnn.
        rewrite /max_arrivals /MaxArrivals /ConcreteMaxArrivals
                /concrete_max_arrivals EMAXeq in EQmax.
        by rewrite EQmax in NEQ; move: NEQ => /eqP. }
      { replace A with (A + ε - ε); last by lia.
        rewrite subn1; apply map_f; rewrite EQ.
        set (h := get_horizon_of_task tsk) in *.
        apply /flatten_mapP; exists ((i-1)*h); first by rewrite mulnC map_f // mem_iota; lia.
        replace (i * h) with (h + (i - 1) * h); last first.
        { destruct (posnP i) as [Z|POS]; first by subst i; lia.
          by rewrite mulnBl mul1n; apply subnKC, leq_pmull. }
        have MFF := map_f (fun t0 => t0 + (i - 1) * h); apply: MFF.
        rewrite -EQh.
        move: (has_valid_arrival_curve_prefix_tsk ts H_valid_task_set tsk H_tsk_in_ts).
        move => [evec [EMAXeq [POSh [LARGEh [NOINF [BUR SORT]]]]]].
        rewrite /get_time_steps_of_task EMAXeq; unfold specified_bursts in *.
        destruct (time_steps_of evec) => //=.
        by rewrite /last0 //=; apply mem_last. }
    Qed.

  End Facts.

End FastSearchSpaceComputation.
