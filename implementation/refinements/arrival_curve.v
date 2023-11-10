Require Export prosa.analysis.definitions.request_bound_function.
Require Export prosa.implementation.refinements.task.

(** ** Arrival Curve Refinements. *)

(** In this module, we provide a series of definitions related to arrival curves
    when working with generic tasks. *)

(** First, we define a helper function that yields the horizon of the arrival
      curve prefix of a task ... *)
Definition get_horizon_of_task (tsk : Task) : duration :=
  horizon_of (get_arrival_curve_prefix tsk).

(** ... another one that yields the time steps of the arrival curve, ... *)
Definition get_time_steps_of_task (tsk : Task) : seq duration :=
  time_steps_of (get_arrival_curve_prefix tsk).

(** ... a function that yields the same time steps, offset by δ, ...**)
Definition time_steps_with_offset tsk δ := [seq t + δ | t <- get_time_steps_of_task tsk].

(** ... and a generalization of the previous function that repeats the time
      steps for each given offset. *)
Definition repeat_steps_with_offset (tsk : Task) (offsets : seq nat): seq nat :=
  flatten (map (time_steps_with_offset tsk) offsets).

(** For convenience, we provide a short form to indicate the request-bound
      function of a task. *)
Definition task_rbf (tsk : Task) (Δ : duration) :=
  task_request_bound_function tsk Δ.

(** Further, we define a valid arrival bound as (1) a positive
      minimum inter-arrival time/period, or (2) a valid arrival curve prefix. *)
Definition valid_arrivals (tsk : Task) : bool :=
  match task_arrival tsk with
  | Periodic p => p >= 1
  | Sporadic m => m >= 1
  | ArrivalPrefix emax_vec => valid_arrival_curve_prefix_dec emax_vec
  end.

(** Next, we define some helper functions, that indicate whether
      the given task is periodic, ... *)
Definition is_periodic_arrivals (tsk : Task) : Prop :=
  exists p, task_arrival tsk = Periodic p.

(** ... sporadic, ... *)
Definition is_sporadic_arrivals (tsk : Task) : Prop :=
  exists m, task_arrival tsk = Sporadic m.

(** ... or bounded by an arrival curve. *)
Definition is_etamax_arrivals (tsk : Task) : Prop :=
  exists ac_prefix_vec, task_arrival tsk = ArrivalPrefix ac_prefix_vec.

(** Further, for convenience, we define the notion of task
      having a valid arrival curve. *)
Definition has_valid_arrival_curve_prefix (tsk: Task) :=
  exists ac_prefix_vec,  get_arrival_curve_prefix tsk = ac_prefix_vec /\
                    valid_arrival_curve_prefix ac_prefix_vec.

(** Finally, we define define the notion of task set with
      valid arrivals. *)
Definition task_set_with_valid_arrivals (ts : seq Task) :=
  forall tsk,
    tsk \in ts -> valid_arrivals tsk.

(** In this section, we prove some facts regarding the above definitions. *)
Section Facts.

  (** Consider a task [tsk]. *)
  Variable tsk : Task.

  (** We show that a task is either periodic, sporadic, or bounded by
      an arrival-curve prefix. *)
  Lemma arrival_cases :
    is_periodic_arrivals tsk
    \/ is_sporadic_arrivals tsk
    \/ is_etamax_arrivals tsk.
  Proof.
    rewrite /is_periodic_arrivals /is_sporadic_arrivals /is_etamax_arrivals.
    destruct (task_arrival tsk).
    - by left; eexists; reflexivity.
    - by right; left; eexists; reflexivity.
    - by right; right; eexists; reflexivity.
  Qed.

End Facts.


(** In this fairly technical section, we prove a series of refinements
    aimed to be able to convert between a standard natural-number task
    arrival bound and an arrival bound that uses, instead of numbers,
    a generic type [T]. *)
Section Theory.

  (** First, we prove a refinement for [positive_horizon]. *)
  Local Instance refine_positive_horizon :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> bool_R)%rel
            positive_horizon positive_horizon_T.
  Proof.
    unfold positive_horizon, positive_horizon_T.
    apply: refines_abstr => a b X.
    unfold horizon_of, horizon_of_T.
    destruct a as [h s], b as [h' s']; simpl.
    rewrite refinesE; rewrite refinesE in X; inversion_clear X.
    by apply refine_ltn; auto using Rnat_0.
  Qed.

  (** Next, we prove a refinement for [large_horizon]. *)
  Local Instance refine_large_horizon :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> bool_R)%rel
            large_horizon_dec large_horizon_T.
  Proof.
    unfold large_horizon_dec, large_horizon_T.
    apply refines_abstr; intros ac ac' Rac.
    refines_apply.
    apply refines_abstr; intros a a' Ra.
    by refines_apply.
  Qed.

  (** Next, we prove a refinement for [no_inf_arrivals]. *)
  Local Instance refine_no_inf_arrivals :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> bool_R)%rel
            no_inf_arrivals no_inf_arrivals_T.
  Proof.
    unfold no_inf_arrivals, no_inf_arrivals_T.
    apply refines_abstr; intros ac ac' Rac.
    refines_apply.
  Qed.

  (** Next, we prove a refinement for [specified_bursts]. *)
  Local Instance refine_specified_bursts :
    refines (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> bool_R)%rel
            specified_bursts specified_bursts_T.
  Proof.
    unfold specified_bursts, specified_bursts_T.
    apply refines_abstr; intros ac ac' Rac.
    rewrite -has_pred1.
    refines_apply; last first.
    - by refines_abstr; rewrite pred1E eq_sym ; refines_apply.
    - refines_abstr.
      rewrite refinesE; eapply has_R; last by apply refinesP; eassumption.
      by intros; apply refinesP; refines_apply.
  Qed.

  (** Next, we prove a refinement for the arrival curve prefix validity. *)
  Local Instance refine_valid_arrival_curve_prefix :
    refines
      (prod_R Rnat (list_R (prod_R Rnat Rnat)) ==> bool_R)%rel
      valid_arrival_curve_prefix_dec
      valid_extrapolated_arrival_curve_T.
  Proof.
    apply refines_abstr.
    unfold valid_arrival_curve_prefix_dec, valid_extrapolated_arrival_curve_T.
    by intros; refines_apply.
  Qed.

  (** Next, we prove a refinement for the arrival curve validity. *)
  Global Instance refine_valid_arrivals :
    forall tsk,
      refines (bool_R)%rel
              (valid_arrivals (taskT_to_task tsk))
              (valid_arrivals_T tsk) | 0.
  Proof.
    move=> tsk.
    have Rtsk := refine_task'.
    rewrite refinesE in Rtsk.
    specialize (Rtsk tsk tsk (unifyxx _)); simpl in Rtsk.
    have Rab := refine_task_arrival.
    rewrite refinesE in Rab.
    specialize (Rab _ _ Rtsk).
    all: unfold valid_arrivals, valid_arrivals_T.
    destruct (task_arrival (_ _)) as [?|?|arrival_curve_prefix], (task_arrival_T _) as [?|?|arrival_curve_prefixT].
    all: try (inversion Rab; fail).
    all: try (refines_apply; rewrite refinesE; inversion Rab; subst; by done).
    { unfold ArrivalCurvePrefix in *.
      refines_apply.
      destruct arrival_curve_prefix as [h st], arrival_curve_prefixT as [h' st'].
      inversion Rab as [(H0, H1)]; refines_apply.
      rewrite refinesE.
      move: H1; clear; elim: st st' => [|s st IHst] [|s' st'] //.
      - by move=> _; apply: list_R_nil_R.
      - move=> H1; inversion H1 as [(H0, H2)].
        apply: list_R_cons_R; last by apply IHst.
        destruct s', s; unfold tb2tn, tmap; simpl.
        by apply refinesP; refines_apply. }
  Qed.

  (** Next, we prove a refinement for [repeat_steps_with_offset]. *)
  Global Instance refine_repeat_steps_with_offset :
    refines (Rtask ==> list_R Rnat ==> list_R Rnat)%rel
            repeat_steps_with_offset repeat_steps_with_offset_T.
  Proof.
    rewrite refinesE => tsk tsk' Rtsk os os' Ros.
    apply flatten_R; eapply map_R; last by apply Ros.
    intros o o' Ro.
    eapply map_R.
    { by intros a a' Ra; apply refinesP; refines_apply. }
    { unfold get_time_steps_of_task, get_time_steps_of_task_T.
      have Rab := refine_task_arrival.
      rewrite refinesE in Rab; specialize (Rab _ _ Rtsk).
      rewrite /get_arrival_curve_prefix /get_extrapolated_arrival_curve_T.
      destruct (task_arrival tsk) as [?|?|arrival_curve_prefix], (task_arrival_T tsk') as [?|?|arrival_curve_prefixT].
      all: try (inversion Rab; fail).
      all: unfold inter_arrival_to_prefix, inter_arrival_to_extrapolated_arrival_curve_T.
      { apply refinesP; refines_apply.
        by rewrite refinesE; inversion Rab; subst. }
      { apply refinesP; refines_apply.
        by rewrite refinesE; inversion Rab; subst. }
      { apply refinesP; refines_apply.
        destruct arrival_curve_prefix as [h st], arrival_curve_prefixT as [h' st'].
        inversion Rab as [(H0, H1)]; refines_apply.
        move: H1; clear; move: st'.
        rewrite refinesE; elim: st => [|a st IHst] [ |s st'] //.
        - by intros _; rewrite //=; apply list_R_nil_R.
        - intros H1; inversion H1; rewrite //=.
          apply list_R_cons_R; last by apply IHst.
          destruct s, a; unfold tb2tn, tmap; simpl.
          by apply refinesP; refines_apply. } }
  Qed.


  (** Next, we prove a refinement for [get_horizon_of_task]. *)
  Global Instance refine_get_horizon_of_task :
    refines (Rtask ==> Rnat)%rel get_horizon_of_task get_horizon_of_task_T.
  Proof.
    rewrite refinesE => tsk tsk' Rtsk.
    rewrite /get_horizon_of_task /get_horizon_of_task_T.
    have Rab := refine_task_arrival.
    rewrite refinesE in Rab; specialize (Rab _ _ Rtsk).
    rewrite /get_arrival_curve_prefix /get_extrapolated_arrival_curve_T.
    destruct (task_arrival _) as [?|?|arrival_curve_prefix], (task_arrival_T _) as [?|?|arrival_curve_prefixT].
    all: try (inversion Rab; fail).
    all: unfold inter_arrival_to_prefix, inter_arrival_to_extrapolated_arrival_curve_T.
    { apply refinesP; refines_apply.
      by rewrite refinesE; inversion Rab; subst. }
    { apply refinesP; refines_apply.
      by rewrite refinesE; inversion Rab; subst. }
    { destruct arrival_curve_prefix as [h st], arrival_curve_prefixT as [h' st'].
      rewrite /horizon_of /horizon_of_T //=.
      by inversion Rab; apply refinesP; tc. }
  Qed.

  (** Next, we prove a refinement for the extrapolated arrival curve. *)
  Local Instance refine_extrapolated_arrival_curve :
    forall arrival_curve_prefix arrival_curve_prefixT δ δ',
      refines Rnat δ δ' ->
      Rtask_ab (ArrivalPrefix arrival_curve_prefix) (ArrivalPrefix_T arrival_curve_prefixT) ->
      refines Rnat (extrapolated_arrival_curve arrival_curve_prefix δ) (extrapolated_arrival_curve_T arrival_curve_prefixT δ').
  Proof.
    move=> arrival_curve_prefix arrival_curve_prefixT  δ δ' Rδ Rab.
    refines_apply.
    destruct arrival_curve_prefix as [h st], arrival_curve_prefixT as [h' st'].
    inversion Rab as [(H0, H1)]; refines_apply.
    move: H1; clear; move: st'.
    rewrite refinesE; elim: st => [|a st IHst] [ |s st'] //.
    - by intros _; rewrite //=; apply list_R_nil_R.
    - intros H1; inversion H1; rewrite //=.
      apply list_R_cons_R; last by apply IHst.
      destruct s, a; unfold tb2tn, tmap; simpl.
      by apply refinesP; refines_apply.
  Qed.

  (** Next, we prove a refinement for the arrival bound definition. *)
  Local Instance refine_ConcreteMaxArrivals :
    refines ( Rtask ==> Rnat ==> Rnat )%rel ConcreteMaxArrivals ConcreteMaxArrivals_T.
  Proof.
    apply refines_abstr2.
    rewrite /ConcreteMaxArrivals /concrete_max_arrivals /ConcreteMaxArrivals_T.
    move => tsk tsk' Rtsk δ δ' Rδ.
    have Rab := refine_task_arrival.
    rewrite refinesE in Rab; rewrite refinesE in Rtsk.
    specialize (Rab _ _ Rtsk).
    rewrite /get_arrival_curve_prefix /get_extrapolated_arrival_curve_T.
    destruct (task_arrival tsk) as [?|?|arrival_curve_prefix], (task_arrival_T tsk') as [?|?|arrival_curve_prefixT].
    all: try (inversion Rab; fail).
    all: unfold inter_arrival_to_prefix, inter_arrival_to_extrapolated_arrival_curve_T.
    { by refines_apply; rewrite refinesE; inversion Rab; subst. }
    { by refines_apply; rewrite refinesE; inversion Rab; subst. }
    { by apply refine_extrapolated_arrival_curve. }
  Qed.

  (** Next, we prove a refinement for the arrival bound definition applied to the
      task conversion function. *)
  Global Instance refine_ConcreteMaxArrivals' :
    forall tsk,
      refines (Rnat ==> Rnat)%rel (ConcreteMaxArrivals (taskT_to_task tsk))
              (ConcreteMaxArrivals_T tsk) | 0.
  Proof.
    intros tsk; apply refines_abstr.
    rewrite /ConcreteMaxArrivals /concrete_max_arrivals
            /ConcreteMaxArrivals_T => δ δ' Rδ.
    have Rtsk := refine_task'.
    rewrite refinesE in Rtsk.
    specialize (Rtsk tsk tsk (unifyxx _)); simpl in Rtsk.
    have Rab := refine_task_arrival.
    rewrite refinesE in Rab.
    specialize (Rab _ _ Rtsk).
    rewrite /get_arrival_curve_prefix /get_extrapolated_arrival_curve_T.
    destruct (task_arrival (_ _)) as [?|?|arrival_curve_prefix], (task_arrival_T tsk) as [?|?|arrival_curve_prefixT].
    all: try (inversion Rab; fail).
    all: unfold inter_arrival_to_prefix, inter_arrival_to_extrapolated_arrival_curve_T.
    { by refines_apply; rewrite refinesE; inversion Rab; subst. }
    { by refines_apply; rewrite refinesE; inversion Rab; subst. }
    { by apply refine_extrapolated_arrival_curve. }
  Qed.

  (** Next, we prove a refinement for [get_arrival_curve_prefix]. *)
  Global Instance refine_get_arrival_curve_prefix :
    refines (Rtask ==> prod_R Rnat (list_R (prod_R Rnat Rnat)))%rel
            get_arrival_curve_prefix get_extrapolated_arrival_curve_T.
  Proof.
    rewrite refinesE => tsk tsk' Rtsk.
    have Rab := refine_task_arrival.
    rewrite refinesE in Rab; specialize (Rab _ _ Rtsk).
    rewrite /get_arrival_curve_prefix /get_extrapolated_arrival_curve_T.
    unfold inter_arrival_to_prefix, inter_arrival_to_extrapolated_arrival_curve_T.
    destruct (task_arrival _) as [?|?|e], (task_arrival_T _) as [?|?|eT].
    all: try (inversion Rab; fail).
    all: try (inversion Rab; subst; apply refinesP; refines_apply; fail).
    destruct e as [h?], eT as [? st];[apply refinesP; refines_apply; inversion Rab; tc].
    inversion Rab as [(H__, Hst)]; subst.
    elim: st Rab Hst => [|a st IHst] Rab H1; first by rewrite //= refinesE; apply list_R_nil_R.
    destruct a; rewrite refinesE.
    apply list_R_cons_R; first by apply refinesP; unfold tb2tn,tmap; refines_apply.
    by apply refinesP, IHst.
  Qed.

  (** Next, we prove a refinement for [get_arrival_curve_prefix] applied to lists. *)
  Global Instance refine_get_arrival_curve_prefix' :
    forall tsk,
      refines
        (prod_R Rnat (list_R (prod_R Rnat Rnat)))%rel
        (get_arrival_curve_prefix (taskT_to_task tsk))
        (get_extrapolated_arrival_curve_T tsk) | 0.
  Proof.
    intros tsk.
    have Rtsk := refine_task'.
    rewrite refinesE in Rtsk.
    specialize (Rtsk tsk tsk (unifyxx _)); simpl in Rtsk.
    move: (refine_task_arrival) => Rab.
    rewrite refinesE in Rab.
    specialize (Rab _ _ Rtsk).
    rewrite /get_arrival_curve_prefix /get_extrapolated_arrival_curve_T.
    unfold inter_arrival_to_prefix, inter_arrival_to_extrapolated_arrival_curve_T.
    destruct (task_arrival _) as [?|?|e], (task_arrival_T _) as [?|?|eT].
    all: try (inversion Rab; fail).
    all: try (inversion Rab; subst; refines_apply; fail).
    destruct e as [h?], eT as [? st]; refines_apply; first by inversion Rab; subst; tc.
    inversion Rab; subst.
    elim: st Rab => [|a st IHst] Rab; first by rewrite //= refinesE; apply list_R_nil_R.
    destruct a; rewrite //= refinesE.
    apply list_R_cons_R; first by apply refinesP; unfold tb2tn,tmap; refines_apply.
    by apply refinesP, IHst.
  Qed.

  (** Next, we prove a refinement for [sorted] when applied to [leq_steps]. *)
  Global Instance refine_sorted_leq_steps :
    forall tsk,
      refines (bool_R)%rel
              (sorted leq_steps (steps_of (get_arrival_curve_prefix (taskT_to_task tsk))))
              (sorted leq_steps_T (get_extrapolated_arrival_curve_T tsk).2) | 0.
  Proof.
    intros.
    by apply refine_leq_steps_sorted; refines_apply.
  Qed.

  (** Lastly, we prove a refinement for the task request-bound function. *)
  Global Instance refine_task_rbf :
    refines ( Rtask ==> Rnat ==> Rnat )%rel task_rbf task_rbf_T.
  Proof.
    apply refines_abstr2.
    rewrite /task_rbf /task_rbf_T /task_request_bound_function
            /concept.task_cost /TaskCost
            /max_arrivals /MaxArrivals => t t' Rt y y' Ry.
    by refines_apply.
  Qed.

End Theory.
