Require Export prosa.util.all.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.analysis.facts.behavior.service.
Require Export prosa.analysis.facts.model.scheduled.
Require Import prosa.model.processor.ideal.

(** Note: we do not re-export the basic definitions to avoid littering the global
   namespace with type class instances. *)

(** In this section we establish the classes to which an ideal schedule belongs. *)
Section ScheduleClass.

  (** We assume ideal uni-processor schedules. *)
  #[local] Existing Instance ideal.processor_state.

  Local Transparent scheduled_in scheduled_on.
  (** Consider any job type and the ideal processor model. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** We note that the ideal processor model is indeed a uni-processor
     model. *)
  Lemma ideal_proc_model_is_a_uniprocessor_model:
    uniprocessor_model (processor_state Job).
  Proof.
    move=> j1 j2 sched t /existsP[[]/eqP E1] /existsP[[]/eqP E2].
    by move: E1 E2 =>->[].
  Qed.

  (** By definition, [service_in] is the sum of the service received
      in total across all cores.  In the ideal uniprocessor model,
      however, there is only one "core," which is expressed by using
      [unit] as the type of cores. The type [unit] only has a single
      member [tt], which serves as a placeholder. Consequently, the
      definition of [service_in] simplifies to a single term of the
      sum, the service on the one core, which we note with the
      following lemma that relates [service_in] to [service_on]. *)
  Lemma service_in_service_on (j : Job) s :
    service_in j s = service_on j s tt.
  Proof.
    by rewrite /service_in sum_unit1.
  Qed.

  (** Furthermore, since the ideal uniprocessor state is represented
      by the [option Job] type, [service_in] further simplifies to a
      simple equality comparison, which we note next. *)
  Lemma service_in_def (j : Job) (s : processor_state Job) :
    service_in j s = (s == Some j).
  Proof.
    by rewrite service_in_service_on.
  Qed.

  (** We observe that the ideal processor model falls into the category
     of ideal-progress models, i.e., a scheduled job always receives
     service. *)
  Lemma ideal_proc_model_ensures_ideal_progress:
    ideal_progress_proc_model (processor_state Job).
  Proof.
    move=> j s /existsP[[]/eqP->] /=.
    by rewrite service_in_def /= eqxx /nat_of_bool.
  Qed.

  (** The ideal processor model is a unit-service model. *)
  Lemma ideal_proc_model_provides_unit_service:
    unit_service_proc_model (processor_state Job).
  Proof.
    move=> j s.
    rewrite service_in_def /= /nat_of_bool.
    by case:ifP.
  Qed.

  (** The ideal processor model is a unit-supply model. *)
  Lemma ideal_proc_model_provides_unit_supply :
    unit_supply_proc_model (processor_state Job).
  Proof.
    by move=> s; rewrite /supply_in /index_enum sum_unit1.
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

  (** The ideal processor model is a fully supply-consuming processor
      model. *)
  Lemma ideal_proc_model_fully_consuming :
    fully_consuming_proc_model (processor_state Job).
  Proof.
    move=> j S t SCHED.
    rewrite /service_at /supply_at /supply_in service_in_def.
    move: SCHED; rewrite scheduled_at_def => ->.
    by rewrite sum_unit1.
  Qed.

  Lemma service_in_is_scheduled_in (j : Job) s :
    service_in j s = scheduled_in j s.
  Proof.
    by rewrite service_in_def scheduled_in_def.
  Qed.

  Lemma service_at_is_scheduled_at sched (j : Job) t :
    service_at sched j t = scheduled_at sched j t.
  Proof.
      by rewrite /service_at service_in_is_scheduled_in.
  Qed.

  Lemma service_on_def (j : Job) (s : processor_state Job) c :
    service_on j s c = (s == Some j).
  Proof. by []. Qed.

  Lemma service_at_def sched (j : Job) t :
    service_at sched j t = (sched t == Some j).
  Proof.
    by rewrite /service_at service_in_def.
  Qed.

  (** The ideal uniprocessor always has supply. *)
  Lemma ideal_proc_has_supply :
    forall (sched : schedule (ideal.processor_state Job)) (t : instant),
      has_supply sched t.
  Proof.
    move=> sched t; rewrite /has_supply /supply_at /supply_in //=.
    by rewrite sum_unit1.
  Qed.

  (** Next we prove a lemma which helps us to do a case analysis on
      the state of an ideal schedule. *)
  Lemma ideal_proc_model_sched_case_analysis:
    forall (sched : schedule (ideal.processor_state Job)) (t : instant),
      ideal_is_idle sched t \/ exists j, scheduled_at sched j t.
  Proof.
    move=> sched t.
    unfold ideal_is_idle; simpl; destruct (sched t) as [s|] eqn:EQ.
    - by right; exists s; auto; rewrite scheduled_at_def EQ.
    - by left; auto.
  Qed.

  (** We prove that if a job [j] is scheduled at a time instant [t],
      then the scheduler is not idle at [t]. *) 
  Lemma ideal_sched_implies_not_idle sched (j : Job) t :
    scheduled_at sched j t ->
    ~ ideal_is_idle sched t.
  Proof.
    rewrite scheduled_at_def => /eqP SCHED /eqP IDLE.
    by rewrite IDLE in SCHED; inversion SCHED.
  Qed.
  
  (** On a similar note, if a scheduler is idle at a time instant [t],
      then no job can receive service at [t]. *)
  Lemma ideal_not_idle_implies_sched sched (j : Job) t :
    ideal_is_idle sched t ->
    service_at sched j t = 0.
  Proof. by rewrite service_at_is_scheduled_at scheduled_at_def => /eqP ->. Qed.

  (** In the following, we relate the ideal uniprocessor state to the generic
       definition [job_scheduled_at]. Specifically, the two notions are
       equivalent. To show this, require an arrival sequence in context. *)
  Section RelationToGenericScheduledJob.

    (** Consider any arrival sequence ... *)
    Variable arr_seq : arrival_sequence Job.
    Context `{JobArrival Job}.

    (** ... and any ideal uni-processor schedule of this arrival sequence. *)
    Variable sched : schedule (ideal.processor_state Job).

  (** Suppose all jobs come from the arrival sequence and do not execute before
      their arrival time (which must be consistent with the arrival
      sequence). *)
    Hypothesis H_jobs_come_from_arrival_sequence :
      jobs_come_from_arrival_sequence sched arr_seq.
    Hypothesis H_jobs_must_arrive_to_execute :
      jobs_must_arrive_to_execute sched.
    Hypothesis H_arrival_times_are_valid :
      valid_arrival_sequence arr_seq.

    (** The generic notion [scheduled_job_at] coincides with our notion of ideal
        processor state. This observation allows cutting out the generic notion
        in proofs specific to ideal uniprocessor schedules. *)
    Lemma scheduled_job_at_def :
      forall t,
        scheduled_job_at arr_seq sched t = sched t.
    Proof.
      move=> t.
      case: (scheduled_at_dec arr_seq _ sched _ _ t) => //[[j SCHED]|NS].
      { move: (SCHED); rewrite scheduled_at_def => /eqP ->.
        by apply/eqP; rewrite scheduled_job_at_scheduled_at
           ; auto using ideal_proc_model_is_a_uniprocessor_model. }
      { move: (NS); rewrite -scheduled_job_at_none; eauto => NONE.
        case SCHED: (sched t) => [j|]; last by rewrite NONE.
        exfalso.
        move: SCHED => /eqP; rewrite -scheduled_at_def.
        by move: (NS j) => /negP. }
    Qed.

    (** Similarly, the generic and specific notions of idle instants
        coincide, too. *)
    Lemma is_idle_def :
      forall t,
        is_idle arr_seq sched t = ideal_is_idle sched t.
    Proof.
      move=> t.
      rewrite /is_idle/ideal_is_idle -scheduled_job_at_def /scheduled_job_at.
      by case: (scheduled_jobs_at _ _ _).
    Qed.

  End RelationToGenericScheduledJob.

End ScheduleClass.

(** * Automation *)
(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve ideal_proc_model_is_a_uniprocessor_model
     ideal_proc_model_provides_unit_supply
     ideal_proc_model_ensures_ideal_progress
     ideal_proc_model_provides_unit_service
     ideal_proc_model_fully_consuming
     ideal_proc_has_supply : basic_rt_facts.

(** We also provide tactics for case analysis on ideal processor state. *)

(** The first tactic generates two sub-goals: one with idle processor and
    the other with processor executing a job named [JobName]. *)
Ltac ideal_proc_model_sched_case_analysis sched t JobName :=
  let Idle := fresh "Idle" in
  let Sched := fresh "Sched_" JobName in
  destruct (ideal_proc_model_sched_case_analysis sched t) as [Idle | [JobName Sched]].

(** The second tactic is similar to the first, but it additionally generates
    two equalities: [sched t = None] and [sched t = Some j]. *)
Ltac ideal_proc_model_sched_case_analysis_eq sched t JobName :=
  let Idle := fresh "Idle" in
  let IdleEq := fresh "Eq" Idle in
  let Sched := fresh "Sched_" JobName in
  let SchedEq := fresh "Eq" Sched in
  destruct (ideal_proc_model_sched_case_analysis sched t) as [Idle | [JobName Sched]];
  [move: (Idle) => /eqP IdleEq; rewrite ?IdleEq
  | move: (Sched); simpl; move => /eqP SchedEq; rewrite ?SchedEq].
