Require Export prosa.model.processor.platform_properties.
Require Export prosa.model.processor.restricted_supply.

(** In this section we establish the classes to which a
    restricted-supply schedule belongs. *)
Section ScheduleClass.

  Local Transparent scheduled_in scheduled_on service_on.

  (** We assume a restricted-supply uni-processor schedule. *)
  #[local] Existing Instance rs_processor_state.

  (** Consider any job type and the ideal processor model. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** We note that the restricted-supply processor model is indeed a
      uni-processor model. *)
  Lemma rs_proc_model_is_a_uniprocessor_model :
    uniprocessor_model (rs_processor_state Job).
  Proof.
    move=> j1 j2 sched t  /existsP[[]/eqP E1] /existsP[[]/eqP E2].
    by move: E1 E2; case (sched t) => //= => j /eqP /eqP -> /eqP /eqP ->.
  Qed.

  (** Restricted-supply processor model is unit-supply. *)
  Lemma rs_proc_is_unit_supply :
    unit_supply_proc_model (rs_processor_state Job).
  Proof.
    move=> sched.
    by rewrite /supply_in sum_unit1; case: sched.
  Qed.

  (** Restricted-supply processor model is a fully supply-consuming
      processor model. *)
  Lemma rs_proc_model_fully_consuming :
    fully_consuming_proc_model (rs_processor_state Job).
  Proof.
    move=> j S t.
    rewrite /scheduled_at /scheduled_in /service_at /supply_at /supply_in /service_in !sum_unit1.
    case (S t) => //=.
    - by move => /existsP [] => //.
    - by move => jo /existsP [_ /eqP ->]; rewrite eq_refl.
  Qed.

End ScheduleClass.

(** * Automation *)
(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve
       rs_proc_model_is_a_uniprocessor_model
       rs_proc_is_unit_supply
       rs_proc_model_fully_consuming : basic_rt_facts.
