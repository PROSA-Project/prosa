Require Export prosa.util.all.
Require Export prosa.behavior.all.
Require Export prosa.model.processor.platform_properties.

(** * Service *)

(** In this file, we establish basic facts about the service received by
    jobs. *)

(** To begin with, we provide some simple but handy rewriting rules for
      [service] and [service_during]. *)
Section Composition.
  
  (** Consider any job type and any processor state. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** For any given schedule... *)
  Variable sched: schedule PState.

  (** ...and any given job... *)
  Variable j: Job.

  (** ...we establish a number of useful rewriting rules that decompose
     the service received during an interval into smaller intervals. *)

  (** As a trivial base case, no job receives any service during an empty
     interval. *)
  Lemma service_during_geq:
    forall t1 t2,
      t1 >= t2 -> service_during sched j t1 t2 = 0.
  Proof.
    move=> t1 t2 t1t2.
    rewrite /service_during big_geq //.
  Qed.

  (** Equally trivially, no job has received service prior to time zero. *)
  Corollary service0:
    service sched j 0 = 0.
  Proof.
    rewrite /service service_during_geq //.
  Qed.

  (** Trivially, an interval consisting of one time unit is equivalent to
     [service_at].  *)
  Lemma service_during_instant:
    forall t,
      service_during sched j t t.+1 = service_at sched j t.
  Proof.
    move => t.
     by rewrite /service_during big_nat_recr ?big_geq //.
  Qed.

  (** Next, we observe that we can look at the service received during an
     interval <<[t1, t3)>> as the sum of the service during [t1, t2) and [t2, t3)
     for any t2 \in [t1, t3]. (The "_cat" suffix denotes the concatenation of
     the two intervals.) *)
  Lemma service_during_cat:
    forall t1 t2 t3,
      t1 <= t2 <= t3 ->
      (service_during sched j t1 t2) + (service_during sched j t2 t3)
      = service_during sched j t1 t3.
  Proof.
    move => t1 t2 t3 /andP [t1t2 t2t3].
      by rewrite /service_during -big_cat_nat /=.
  Qed.

  (** Since [service] is just a special case of [service_during], the same holds
     for [service]. *)
  Lemma service_cat:
    forall t1 t2,
      t1 <= t2 ->
      (service sched j t1) + (service_during sched j t1 t2)
      = service sched j t2.
  Proof.
    move=> t1 t2 t1t2.
    rewrite /service service_during_cat //.
  Qed.

  (** As a special case, we observe that the service during an interval can be
     decomposed into the first instant and the rest of the interval. *)
  Lemma service_during_first_plus_later:
    forall t1 t2,
      t1 < t2 ->
      (service_at sched j t1) + (service_during sched j t1.+1 t2)
      = service_during sched j t1 t2.
  Proof.
    move => t1 t2 t1t2.
    have TIMES: t1 <= t1.+1 <= t2 by rewrite /(_ && _) ifT //.
    have SPLIT := service_during_cat t1 t1.+1 t2 TIMES.
      by rewrite -service_during_instant //.
  Qed.

  (** Symmetrically, we have the same for the end of the interval. *)
  Lemma service_during_last_plus_before:
    forall t1 t2,
      t1 <= t2 ->
      (service_during sched j t1 t2) + (service_at sched j t2)
      = service_during sched j t1 t2.+1.
  Proof.
    move=> t1 t2 t1t2.
    rewrite -(service_during_cat t1 t2 t2.+1); last by rewrite /(_ && _) ifT //.
    rewrite service_during_instant //.
  Qed.

  (** And hence also for [service]. *)
  Corollary service_last_plus_before:
    forall t,
      (service sched j t) + (service_at sched j t)
      = service sched j t.+1.
  Proof.
    move=> t.
    rewrite /service. rewrite -service_during_last_plus_before //.
  Qed.

  (** Finally, we deconstruct the service received during an interval <<[t1, t3)>>
     into the service at a midpoint t2 and the service in the intervals before
     and after. *)
  Lemma service_split_at_point:
    forall t1 t2 t3,
      t1 <= t2 < t3 ->
      (service_during sched j t1 t2) + (service_at sched j t2) + (service_during sched j t2.+1 t3)
      = service_during sched j t1 t3.
  Proof.
    move => t1 t2 t3 /andP [t1t2 t2t3].
    rewrite -addnA service_during_first_plus_later// service_during_cat// /(_ && _) ifT//.
      by exact: ltnW.
  Qed.

End Composition.

(** As a common special case, we establish facts about schedules in which a
    job receives either 1 or 0 service units at all times. *)
Section UnitService.

  (** Consider any job type and any processor state. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Let's consider a unit-service model... *)
  Hypothesis H_unit_service: unit_service_proc_model PState.

  (** ...and a given schedule. *)
  Variable sched: schedule PState.

  (** Let [j] be any job that is to be scheduled. *)
  Variable j: Job.

  (** First, we prove that the instantaneous service cannot be greater than 1, ... *)
  Lemma service_at_most_one:
    forall t, service_at sched j t <= 1.
  Proof.
      by move=> t; rewrite /service_at.
  Qed.

  (** ...which implies that the cumulative service received by job [j] in any
     interval of length delta is at most delta. *)
  Lemma cumulative_service_le_delta:
    forall t delta,
      service_during sched j t (t + delta) <= delta.
  Proof.
    unfold service_during; intros t delta.
    apply leq_trans with (n := \sum_(t <= t0 < t + delta) 1);
      last by rewrite sum_of_ones.
    by apply: leq_sum => t' _; apply: service_at_most_one.
  Qed.

  Section ServiceIsAStepFunction.

    (** We show that the service received by any job [j] is a step function. *)
    Lemma service_is_a_step_function:
      is_step_function (service sched j).
    Proof.
      rewrite /is_step_function => t.
      rewrite addn1 -service_last_plus_before leq_add2l.
      apply service_at_most_one.
    Qed.

    (** Next, consider any time [t]... *)
    Variable t: instant.

    (** ...and let [s0] be any value less than the service received
       by job [j] by time [t]. *)
    Variable s0: duration.
    Hypothesis H_less_than_s: s0 < service sched j t.

    (** Then, we show that there exists an earlier time [t0] where job [j] had [s0]
       units of service. *)
    Corollary exists_intermediate_service:
      exists t0,
        t0 < t /\
        service sched j t0 = s0.
    Proof.
      feed (exists_intermediate_point (service sched j));
        [by apply service_is_a_step_function | intros EX].
      feed (EX 0 t); first by done.
      feed (EX s0);
        first by rewrite /service /service_during big_geq //.
        by move: EX => /= [x_mid EX]; exists x_mid.
    Qed.
  End ServiceIsAStepFunction.

End UnitService.

(** We establish a basic fact about the monotonicity of service. *)
Section Monotonicity.

  (** Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any given schedule... *)
  Variable sched: schedule PState.

  (** ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (** We observe that the amount of service received is monotonic by definition. *)
  Lemma service_monotonic:
    forall t1 t2,
      t1 <= t2 ->
      service sched j t1 <= service sched j t2.
  Proof.
    move=> t1 t2 let1t2.
      by rewrite -(service_cat sched j t1 t2 let1t2); apply: leq_addr.
  Qed.

End Monotonicity.

(** Consider any job type and any processor model. *)
Section RelationToScheduled.

  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any given schedule... *)
  Variable sched: schedule PState.

  (** ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (** We observe that a job that isn't scheduled cannot possibly receive service. *)
  Lemma not_scheduled_implies_no_service:
    forall t,
      ~~ scheduled_at sched j t -> service_at sched j t = 0.
  Proof.
    rewrite /service_at /scheduled_at.
    move=> t NOT_SCHED.
    rewrite service_implies_scheduled //.
  Qed.

  (** Conversely, if a job receives service, then it must be scheduled. *)
  Lemma service_at_implies_scheduled_at:
    forall t,
      service_at sched j t > 0 -> scheduled_at sched j t.
  Proof.
    move=> t.
    destruct (scheduled_at sched j t) eqn:SCHEDULED; first trivial.
    rewrite not_scheduled_implies_no_service // negbT //.
  Qed.

  (** Thus, if the cumulative amount of service changes, then it must be
     scheduled, too. *)
  Lemma service_delta_implies_scheduled:
    forall t,
      service sched j t < service sched j t.+1 -> scheduled_at sched j t.
  Proof.
    move => t.
    rewrite -service_last_plus_before -{1}(addn0 (service sched j t)) ltn_add2l.
    apply: service_at_implies_scheduled_at.
  Qed.

  (** We observe that a job receives cumulative service during some interval iff
     it receives services at some specific time in the interval. *)
  Lemma service_during_service_at:
    forall t1 t2,
      service_during sched j t1 t2 > 0
      <->
      exists t,
        t1 <= t < t2 /\
        service_at sched j t > 0.
  Proof.
    split.
    {
      move=> NONZERO.
      case (boolP([exists t: 'I_t2,
                      (t >= t1) && (service_at sched j t > 0)])) => [EX | ALL].
      - move: EX => /existsP [x /andP [GE SERV]].
        exists x; split => //.
        apply /andP; by split.
      - rewrite negb_exists in ALL; move: ALL => /forallP ALL.
        rewrite /service_during big_nat_cond in NONZERO.
        rewrite big1 ?ltn0 // in NONZERO => i.
        rewrite andbT; move => /andP [GT LT].
        specialize (ALL (Ordinal LT)); simpl in ALL.
        rewrite GT andTb -eqn0Ngt in ALL.
        apply /eqP => //.
    }
    {
      move=> [t [TT SERVICE]].
      case (boolP (0 < service_during sched j t1 t2)) => // NZ.
      exfalso.
      rewrite -eqn0Ngt in NZ. move/eqP: NZ.
      rewrite big_nat_eq0 => IS_ZERO.
      have NO_SERVICE := IS_ZERO t TT.
      apply lt0n_neq0 in SERVICE.
        by move/neqP in SERVICE; contradiction.
    }
  Qed.

  (** Thus, any job that receives some service during an interval must be
      scheduled at some point during the interval... *)
  Corollary cumulative_service_implies_scheduled:
    forall t1 t2,
      service_during sched j t1 t2 > 0 ->
      exists t,
        t1 <= t < t2 /\
        scheduled_at sched j t.
  Proof.
    move=> t1 t2.
    rewrite service_during_service_at.
    move=> [t' [TIMES SERVICED]].
    exists t'; split => //.
    by apply: service_at_implies_scheduled_at.
 Qed.

  (** ...which implies that any job with positive cumulative service must have
     been scheduled at some point. *)
  Corollary positive_service_implies_scheduled_before:
    forall t,
      service sched j t > 0 -> exists t', (t' < t /\ scheduled_at sched j t').
  Proof.
    move=> t2.
    rewrite /service => NONZERO.
    have EX_SCHED := cumulative_service_implies_scheduled 0 t2 NONZERO.
    by move: EX_SCHED => [t [TIMES SCHED_AT]]; exists t; split.
  Qed.
 
  (** If we can assume that a scheduled job always receives service,
      we can further prove the converse. *)
  Section GuaranteedService.

    (** Assume [j] always receives some positive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** In other words, not being scheduled is equivalent to receiving zero
       service. *)
    Lemma no_service_not_scheduled:
      forall t,
        ~~ scheduled_at sched j t <-> service_at sched j t = 0.
    Proof.
      move=> t. rewrite /scheduled_at /service_at.
      split => [NOT_SCHED | NO_SERVICE].
      - by rewrite service_implies_scheduled //.
      - apply (contra (H_scheduled_implies_serviced j (sched t))).
        by rewrite -eqn0Ngt; apply /eqP => //.
    Qed.

    (** Then, if a job does not receive any service during an interval, it
       is not scheduled. *)
    Lemma no_service_during_implies_not_scheduled:
      forall t1 t2,
        service_during sched j t1 t2 = 0 ->
        forall t,
          t1 <= t < t2 -> ~~ scheduled_at sched j t.
    Proof.
      move=> t1 t2 ZERO_SUM t /andP [GT_t1 LT_t2].
      rewrite no_service_not_scheduled.
      move: ZERO_SUM.
      rewrite /service_during big_nat_eq0 => IS_ZERO.
      by apply (IS_ZERO t); apply /andP; split => //.
    Qed.
    
    (** Conversely, if a job is not scheduled during an interval, then
        it does not receive any service in that interval *)
    Lemma not_scheduled_during_implies_zero_service:
      forall t1 t2,
        (forall t, t1 <= t < t2 -> ~~ scheduled_at sched j t) -> 
        service_during sched j t1 t2 = 0.
    Proof.
      intros t1 t2 NSCHED.
      apply big_nat_eq0; move=> t NEQ.
      by apply no_service_not_scheduled, NSCHED.
    Qed.

    (** If a job is scheduled at some point in an interval, it receives
       positive cumulative service during the interval... *)
    Lemma scheduled_implies_cumulative_service:
      forall t1 t2,
        (exists t,
            t1 <= t < t2 /\
            scheduled_at sched j t) ->
        service_during sched j t1 t2 > 0.
    Proof.
      move=> t1 t2 [t' [TIMES SCHED]].
      rewrite service_during_service_at.
      exists t'; split => //.
      move: SCHED. rewrite /scheduled_at /service_at.
        by apply (H_scheduled_implies_serviced j (sched t')).
    Qed.

    (** ...which again applies to total service, too. *)
    Corollary scheduled_implies_nonzero_service:
      forall t,
        (exists t',
            t' < t /\
            scheduled_at sched j t') ->
        service sched j t > 0.
    Proof.
      move=> t [t' [TT SCHED]].
      rewrite /service. apply scheduled_implies_cumulative_service.
      exists t'; split => //.
    Qed.

  End GuaranteedService.

  (** Furthermore, if we know that jobs are not released early, then we can
      narrow the interval during which they must have been scheduled. *)
  Section AfterArrival.

    Context `{JobArrival Job}.

    (** Assume that jobs must arrive to execute. *)
    Hypothesis H_jobs_must_arrive:
      jobs_must_arrive_to_execute sched.

    (** We prove that any job with positive cumulative service at time [t] must
       have been scheduled some time since its arrival and before time [t]. *)
    Lemma positive_service_implies_scheduled_since_arrival:
      forall t,
        service sched j t > 0 ->
        exists t', (job_arrival j <= t' < t /\ scheduled_at sched j t').
    Proof.
      move=> t SERVICE.
      have EX_SCHED := positive_service_implies_scheduled_before t SERVICE.
      inversion EX_SCHED as [t'' [TIMES SCHED_AT]].
      exists t''; split; last by assumption.
      rewrite /(_ && _) ifT //.
      move: H_jobs_must_arrive. rewrite /jobs_must_arrive_to_execute /has_arrived => ARR.
        by apply: ARR; exact.
    Qed.

    Lemma not_scheduled_before_arrival:
      forall t, t < job_arrival j -> ~~ scheduled_at sched j t.
    Proof.
      move=> t EARLY.
      apply: (contra (H_jobs_must_arrive j t)).
      rewrite /has_arrived -ltnNge //.
   Qed.

    (** We show that job [j] does not receive service at any time [t] prior to its
        arrival. *)
    Lemma service_before_job_arrival_zero:
      forall t,
        t < job_arrival j ->
        service_at sched j t = 0.
    Proof.
      move=> t NOT_ARR.
      rewrite not_scheduled_implies_no_service // not_scheduled_before_arrival //.
    Qed.

    (** Note that the same property applies to the cumulative service. *)
    Lemma cumulative_service_before_job_arrival_zero :
      forall t1 t2 : instant,
        t2 <= job_arrival j ->
        service_during sched j t1 t2 = 0.
    Proof.
      move=> t1 t2 EARLY.
      rewrite /service_during.
      have ZERO_SUM: \sum_(t1 <= t < t2) service_at sched j t = \sum_(t1 <= t < t2) 0;
        last by rewrite ZERO_SUM sum0.
      rewrite big_nat_cond [in RHS]big_nat_cond.
      apply: eq_bigr => i /andP [TIMES _]. move: TIMES => /andP [le_t1_i lt_i_t2].
      apply (service_before_job_arrival_zero i).
        by apply leq_trans with (n := t2); auto.
    Qed.

    (** Hence, one can ignore the service received by a job before its arrival
       time... *)
    Lemma ignore_service_before_arrival:
      forall t1 t2,
        t1 <= job_arrival j ->
        t2 >= job_arrival j ->
        service_during sched j t1 t2 = service_during sched j (job_arrival j) t2.
    Proof.
      move=> t1 t2 le_t1 le_t2.
      rewrite -(service_during_cat sched j t1 (job_arrival j) t2).
      rewrite cumulative_service_before_job_arrival_zero //.
        by apply/andP; split; exact.
    Qed.

    (** ... which we can also state in terms of cumulative service. *)
    Corollary no_service_before_arrival:
      forall t,
        t <= job_arrival j -> service sched j t = 0.
    Proof.
      move=> t EARLY.
      rewrite /service cumulative_service_before_job_arrival_zero //.
    Qed.

  End AfterArrival.

  (** In this section, we prove some lemmas about time instants with same
      service. *)
  Section TimesWithSameService.

    (** Consider any time instants [t1] and [t2]... *)
    Variable t1 t2: instant.

    (** ...where [t1] is no later than [t2]... *)
    Hypothesis H_t1_le_t2: t1 <= t2.

    (** ...and where job [j] has received the same amount of service. *)
    Hypothesis H_same_service: service sched j t1 = service sched j t2.

    (** First, we observe that this means that the job receives no service
       during <<[t1, t2)>>... *)
    Lemma constant_service_implies_no_service_during:
      service_during sched j t1 t2 = 0.
    Proof.
      move: H_same_service.
      rewrite -(service_cat sched j t1 t2) // -[service sched j t1 in LHS]addn0 => /eqP.
      by rewrite eqn_add2l => /eqP //.
    Qed.

    (** ...which of course implies that it does not receive service at any
       point, either. *)
    Lemma constant_service_implies_not_scheduled:
      forall t,
        t1 <= t < t2 -> service_at sched j t = 0.
    Proof.
      move=> t /andP [GE_t1 LT_t2].
      move: constant_service_implies_no_service_during.
      rewrite /service_during big_nat_eq0 => IS_ZERO.
      apply IS_ZERO. apply /andP; split => //.
    Qed.

    (** We show that job [j] receives service at some point [t < t1]
       iff [j] receives service at some point [t' < t2]. *)
    Lemma same_service_implies_serviced_at_earlier_times:
      [exists t: 'I_t1, service_at sched j t > 0] =
      [exists t': 'I_t2, service_at sched j t' > 0].
    Proof.
      apply /idP/idP => /existsP [t SERVICED].
      {
        have LE: t < t2
          by apply: (leq_trans _ H_t1_le_t2) => //.
        by apply /existsP; exists (Ordinal LE).
      }
      {
        case (boolP (t < t1)) => LE.
        - by apply /existsP; exists (Ordinal LE).
        - exfalso.
          have TIMES: t1 <= t < t2
            by apply /andP; split => //; rewrite leqNgt //.
          have NO_SERVICE := constant_service_implies_not_scheduled t TIMES.
          by rewrite NO_SERVICE in SERVICED.
      }
    Qed.


    (** Then, under the assumption that scheduled jobs receives service,
        we can translate this into a claim about scheduled_at. *)

    (** Assume [j] always receives some positive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** We show that job [j] is scheduled at some point [t < t1] iff [j] is scheduled
       at some point [t' < t2].  *)
    Lemma same_service_implies_scheduled_at_earlier_times:
      [exists t: 'I_t1, scheduled_at sched j t] =
      [exists t': 'I_t2, scheduled_at sched j t'].
    Proof.
      have CONV: forall B, [exists b: 'I_B, scheduled_at sched j b]
                           = [exists b: 'I_B, service_at sched j b > 0].
      {
        move=> B. apply/idP/idP => /existsP [b P]; apply /existsP; exists b.
        - by move: P; rewrite /scheduled_at /service_at;
            apply (H_scheduled_implies_serviced j (sched b)).
        - by apply service_at_implies_scheduled_at.
      }
      rewrite !CONV.
      apply same_service_implies_serviced_at_earlier_times.
    Qed.
  End TimesWithSameService.

End RelationToScheduled.

Section ServiceInTwoSchedules.
  
  (** Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any two given schedules... *)
  Variable sched1 sched2: schedule PState.
  
  (** Given an interval in which the schedules provide the same service 
      to a job at each instant, we can prove that the cumulative service 
      received during the interval has to be the same. *)
  Section ServiceDuringEquivalentInterval.
    
    (** Consider two time instants...  *)
    Variable t1 t2 : instant.

    (** ...and a given job that is to be scheduled. *)
    Variable j: Job.

    (** Assume that, in any instant between [t1] and [t2] the service 
        provided to [j] from the two schedules is the same. *)
    Hypothesis H_sched1_sched2_same_service_at:
      forall t, t1 <= t < t2 ->
           service_at sched1 j t = service_at sched2 j t.

    (** It follows that the service provided during [t1] and [t2]
        is also the same. *)
    Lemma same_service_during:
      service_during sched1 j t1 t2 = service_during sched2 j t1 t2.
    Proof.
      rewrite /service_during.
      apply eq_big_nat.
      by apply H_sched1_sched2_same_service_at.
    Qed.

  End ServiceDuringEquivalentInterval.

  (** We can leverage the previous lemma to conclude that two schedules
      that match in a given interval will also have the same cumulative
      service across the interval. *)
  Corollary equal_prefix_implies_same_service_during:
    forall t1 t2,
      (forall t, t1 <= t < t2 -> sched1 t = sched2 t) ->
      forall j, service_during sched1 j t1 t2 = service_during sched2 j t1 t2.
  Proof.
    move=> t1 t2 SCHED_EQ j.
    apply same_service_during => t' RANGE.
    by rewrite /service_at SCHED_EQ.
  Qed.

End ServiceInTwoSchedules.
