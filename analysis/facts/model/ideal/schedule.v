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
    by rewrite /service_in /index_enum Finite.EnumDef.enumDef /= big_seq1.
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
    by rewrite service_in_def scheduled_in_def.
  Qed.

  Lemma service_at_is_scheduled_at sched (j : Job) t :
    service_at sched j t = scheduled_at sched j t.
  Proof.
      by rewrite /service_at service_in_is_scheduled_in.
  Qed.

  Lemma service_on_def (j : Job) (s : processor_state Job) c :
    service_on j s c = (s == Some j).
  Proof.
    done.
  Qed.

  Lemma service_at_def sched (j : Job) t :
    service_at sched j t = (sched t == Some j).
  Proof.
    by rewrite /service_at service_in_def.
  Qed.

  (** Next we prove a lemma which helps us to do a case analysis on
      the state of an ideal schedule. *)
  Lemma ideal_proc_model_sched_case_analysis:
    forall (sched : schedule (ideal.processor_state Job)) (t : instant),
      is_idle sched t \/ exists j, scheduled_at sched j t.
  Proof.
    move=> sched t.
    unfold is_idle; simpl; destruct (sched t) as [s|] eqn:EQ.
    - by right; exists s; auto; rewrite scheduled_at_def EQ.
    - by left; auto.
  Qed.

  (** We prove that if a job [j] is scheduled at a time instant [t],
      then the scheduler is not idle at [t]. *) 
  Lemma ideal_sched_implies_not_idle sched (j : Job) t :
    scheduled_at sched j t ->
    ~ is_idle sched t.
  Proof.
    rewrite scheduled_at_def => /eqP SCHED /eqP IDLE.
    by rewrite IDLE in SCHED; inversion SCHED.
  Qed.
  
  (** On a similar note, if a scheduler is idle at a time instant [t],
      then no job can receive service at [t]. *)
  Lemma ideal_not_idle_implies_sched sched (j : Job) t :
    is_idle sched t ->
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
    Hypothesis H_arrival_times_are_consistent :
      consistent_arrival_times arr_seq.

    (** The generic notion [scheduled_job_at] coincides with our notion of ideal
        processor state. This observation allows cutting out the generic notion
        in proofs specific to ideal uniprocessor schedules. *)
    Lemma scheduled_job_at_def :
      forall t,
        scheduled_job_at arr_seq sched t = sched t.
    Proof.
      move=> t.
      case: (scheduled_at_dec arr_seq sched _ _ _ t) => //[[j SCHED]|NS].
      { move: (SCHED); rewrite scheduled_at_def => /eqP ->.
        by rewrite scheduled_job_at_iff
           ; auto using ideal_proc_model_is_a_uniprocessor_model. }
      { move: (NS); rewrite -scheduled_job_at_none; eauto => NONE.
        case SCHED: (sched t) => [j|]; last by rewrite NONE.
        exfalso.
        move: SCHED => /eqP; rewrite -scheduled_at_def.
        by move: (NS j) => /negP. }
    Qed.

  End RelationToGenericScheduledJob.

End ScheduleClass.

(** * Incremental Service in Ideal Schedule *)
(** In the following section we prove a few facts about service in ideal schedule. *)
(* Note that these lemmas can be generalized to an arbitrary scheduler. *)
Section IncrementalService.

  (** Consider any job type, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any ideal uni-processor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** As a base case, we prove that if a job [j] receives service in
      some time interval <<[t1,t2)>>, then there exists a time instant
      <<t ∈ [t1,t2)>> such that [j] is scheduled at time [t] and [t] is
      the first instant where [j] receives service. *)
  Lemma positive_service_during:
    forall j t1 t2,
      0 < service_during sched j t1 t2 ->
      exists t : nat, t1 <= t < t2 /\ scheduled_at sched j t /\ service_during sched j t1 t = 0.
  Proof.
    intros j t1 t2 SERV.
    have LE: t1 <= t2.
    { rewrite leqNgt; apply/negP; intros CONTR.
        by apply ltnW in CONTR;  move: SERV; rewrite /service_during big_geq.
    }
    destruct (scheduled_at sched j t1) eqn:SCHED.
    { exists t1; repeat split; try done.
      - apply/andP; split; first by done.
        rewrite ltnNge; apply/negP; intros CONTR.
          by move: SERV; rewrite/service_during big_geq.
      - by rewrite /service_during big_geq.
    }
    { apply negbT in SCHED.
      move: SERV.
      rewrite /service_during sum_nat_gt0 filter_predT => /hasP[t IN SCHEDt].
      rewrite service_at_def /= lt0b in SCHEDt.
      rewrite mem_iota subnKC in IN; last by done.
      move: IN => /andP [IN1 IN2].
      move: (exists_first_intermediate_point
               ((fun t => scheduled_at sched j t)) t1 t IN1 SCHED) => A.
      feed A; first by rewrite scheduled_at_def/=.
      move: A => [x [/andP [T1 T4] [T2 T3]]].
      exists x; repeat split; try done.
      - apply/andP; split; first by apply ltnW.
          by apply leq_ltn_trans with t.
      - apply/eqP; rewrite big_nat_cond big1 //.
        move => y /andP [T5 _].
        apply/eqP.
        rewrite service_at_def /= eqb0.
        by specialize (T2 y); rewrite scheduled_at_def/= in T2; apply T2.
    }
  Qed.

  (** Furthermore, we observe that, if a job receives some positive
      amount of service during an interval <<[t1, t2)>>, then the
      interval can't be empty and hence [t1 < t2]. *)
  Lemma service_during_ge :
    forall j t1 t2 k,
      service_during sched j t1 t2 > k ->
      t1 < t2.
  Proof.
    move=> j t1 t2 k SERV.
    rewrite leqNgt.
    apply/negP => CONTR.
    move: SERV.
    by rewrite /service_during big_geq.
  Qed.

  (** Next, we prove that if in some time interval <<[t1,t2)>> a job [j]
     receives [k] units of service, then there exists a time instant
     <<t ∈ [t1,t2)>> such that [j] is scheduled at time [t] and service
     of job [j] within interval <<[t1,t)>> is equal to [k]. *)
  Lemma incremental_service_during:
    forall j t1 t2 k,
      service_during sched j t1 t2 > k ->
      exists t, t1 <= t < t2 /\ scheduled_at sched j t /\ service_during sched j t1 t = k.
  Proof.
    move=> j t1 t2 k SERV.
    have LE: t1 < t2 by move: (service_during_ge _ _ _ _ SERV).
    elim: k SERV => [|k IHk] SERV; first by apply positive_service_during in SERV.
    feed IHk; first by apply ltn_trans with k.+1.
    move: IHk => [t [/andP [NEQ1 NEQ2] [SCHEDt SERVk]]].
    have SERVk1: service_during sched j t1 t.+1 = k.+1.
    { rewrite -(service_during_cat _ _ _ t); last by apply/andP; split.
      rewrite  SERVk -[X in _ = X]addn1; apply/eqP; rewrite eqn_add2l.
      rewrite /service_during big_nat1 service_at_def /=.
      by rewrite eqb1 -scheduled_at_def /=.
    }
    move: SERV; rewrite -(service_during_cat _ _ _ t.+1); last first.
    { by apply/andP; split; first apply leq_trans with t. }
    rewrite SERVk1 -addn1 leq_add2l; move => SERV.
    destruct (scheduled_at sched j t.+1) eqn:SCHED.
    - exists t.+1; repeat split; try done. apply/andP; split.
      + apply leq_trans with t; by done.
      + rewrite ltnNge; apply/negP; intros CONTR.
          by move: SERV; rewrite /service_during big_geq.
    -  apply negbT in SCHED.
       move: SERV; rewrite /service /service_during sum_nat_gt0 filter_predT; move => /hasP[x INx SCHEDx].
       rewrite service_at_def lt0b in SCHEDx.
       rewrite mem_iota subnKC in INx; last by done.
       move: INx => /andP [INx1 INx2].
       move: (exists_first_intermediate_point _ _ _ INx1 SCHED) => A.
       feed A; first by rewrite scheduled_at_def/=.
       move: A => [y [/andP [T1 T4] [T2 T3]]].
       exists y; repeat split => //.
       + apply/andP; split.
         apply leq_trans with t; first by done.
         apply ltnW, ltn_trans with t.+1; by done.
           by apply leq_ltn_trans with x.
       + rewrite (@big_cat_nat _ _ _ t.+1) //=; [ | by apply leq_trans with t | by apply ltn_trans with t.+1].
         unfold service_during in SERVk1; rewrite SERVk1; apply/eqP.
         rewrite -{2}[k.+1]addn0 eqn_add2l.
         rewrite big_nat_cond big1 //; move => z /andP [H5 _].
         apply/eqP.
         rewrite service_at_def eqb0.
         by specialize (T2 z); rewrite scheduled_at_def/= in T2; apply T2.
  Qed.

End IncrementalService.

(** * Automation *)
(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve ideal_proc_model_is_a_uniprocessor_model
     ideal_proc_model_ensures_ideal_progress
     ideal_proc_model_provides_unit_service : basic_rt_facts.

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
