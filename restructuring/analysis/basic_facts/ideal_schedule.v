From rt.restructuring.model.processor Require Import ideal platform_properties.
(** Note: we do not re-export the basic definitions to avoid littering the global
   namespace with type class instances. *)

(** In this section we estlish the classes to which an ideal schedule belongs. *)
Section ScheduleClass.
  (** Consider any job type and the ideal processor model. *)
  Context {Job: JobType}.

  (** We note that the ideal processor model is indeed a uniprocessor
     model. *)
  Lemma ideal_proc_model_is_a_uniprocessor_model:
    uniprocessor_model (processor_state Job).
  Proof.
    move=> j1 j2 sched t.
    by rewrite /scheduled_at=> /eqP-> /eqP[->].
  Qed.

  (** We observe that the ideal processor model falls into the category
     of ideal-progress models, i.e., a scheduled job always receives
     service. *)
  Lemma ideal_proc_model_ensures_ideal_progress:
    ideal_progress_proc_model (processor_state Job).
  Proof.
    move=> j s /eqP /eqP SOME.
    by rewrite /service_in /pstate_instance SOME.
  Qed.

  (** The ideal processor model is a unit-service model. *)
  Lemma ideal_proc_model_provides_unit_service:
    unit_service_proc_model (processor_state Job).
  Proof.
    move=> j s.
    rewrite /service_in /pstate_instance.
    by elim: (s == Some j).
  Qed.

End ScheduleClass.

