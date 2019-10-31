From mathcomp Require Import all_ssreflect.
From rt.restructuring.model.processor Require Import ideal platform_properties.
(** Note: we do not re-export the basic definitions to avoid littering the global
   namespace with type class instances. *)

(** In this section we estlish the classes to which an ideal schedule belongs. *)
Section ScheduleClass.

  Local Transparent service_in scheduled_in scheduled_on.
  (** Consider any job type and the ideal processor model. *)
  Context {Job: JobType}.

  (** We note that the ideal processor model is indeed a uniprocessor
     model. *)
  Lemma ideal_proc_model_is_a_uniprocessor_model:
    uniprocessor_model (processor_state Job).
  Proof.
    move=> j1 j2 sched t /existsP[[]/eqP E1] /existsP[[]/eqP E2].
    by move: E1 E2=>->[].
  Qed.

  (** We observe that the ideal processor model falls into the category
     of ideal-progress models, i.e., a scheduled job always receives
     service. *)
  Lemma ideal_proc_model_ensures_ideal_progress:
    ideal_progress_proc_model (processor_state Job).
  Proof.
    move=> j s /existsP[[]/eqP->]/=.
    by rewrite eqxx.
  Qed.

  (** The ideal processor model is a unit-service model. *)
  Lemma ideal_proc_model_provides_unit_service:
    unit_service_proc_model (processor_state Job).
  Proof.
    move=> j s.
    rewrite /service_in/=/nat_of_bool.
    by case:ifP.
  Qed.

  Lemma scheduled_in_def (j : Job) s :
    scheduled_in j s = (s == Some j).
  Proof.
    rewrite /scheduled_in/scheduled_on/=.
    case: existsP=>[[_->]//|].
    case: (s == Some j)=>//=[[]].
      by exists.
  Qed.

  Lemma scheduled_at_def sched (j : Job) t :
    scheduled_at sched j t = (sched t == Some j).
  Proof.
      by rewrite /scheduled_at scheduled_in_def.
  Qed.

  Lemma service_in_is_scheduled_in (j : Job) s :
    service_in j s = scheduled_in j s.
  Proof.
    by rewrite /service_in scheduled_in_def/=.
  Qed.

  Lemma service_at_is_scheduled_at sched (j : Job) t :
    service_at sched j t = scheduled_at sched j t.
  Proof.
      by rewrite /service_at service_in_is_scheduled_in.
  Qed.
End ScheduleClass.
