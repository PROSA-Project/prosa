Require Export prosa.util.all.
Require Export prosa.behavior.all.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.analysis.definitions.schedule_prefix.
Require Export prosa.model.task.concept.

(** * Service *)

(** In this file, we establish basic facts about the service received by
    jobs. *)

(** To begin with, we provide some simple but handy rewriting rules for
      [service] and [service_during]. *)
Section Composition.

  (** Consider any job type and any processor state. *)
  Context {Job: JobType}.
  Context {PState: ProcessorState Job}.

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
  Proof. by move=> ? ? ?; rewrite /service_during big_geq. Qed.

  (** Conversely, if a job receives some service in some interval, then the
      interval is not empty. *)
  Corollary service_during_ge :
    forall t1 t2 k,
      service_during sched j t1 t2 > k ->
      t1 < t2.
  Proof.
    move=> t1 t2 k GT.
    apply: (contraPltn _ GT) => LEQ.
    by move: (service_during_geq _ _ LEQ) => ->.
  Qed.

  (** Equally trivially, no job has received service prior to time zero. *)
  Corollary service0:
    service sched j 0 = 0.
  Proof. by rewrite /service service_during_geq. Qed.

  (** Trivially, an interval consisting of one time unit is equivalent to
     [service_at].  *)
  Lemma service_during_instant:
    forall t,
      service_during sched j t t.+1 = service_at sched j t.
  Proof. by move=> ?; rewrite /service_during big_nat_recr// big_geq. Qed.

  (** Next, we observe that we can look at the service received during an
     interval <<[t1, t3)>> as the sum of the service during [t1, t2) and [t2, t3)
     for any t2 \in [t1, t3]. (The "_cat" suffix denotes the concatenation of
     the two intervals.) *)
  Lemma service_during_cat:
    forall t1 t2 t3,
      t1 <= t2 <= t3 ->
      (service_during sched j t1 t2) + (service_during sched j t2 t3)
      = service_during sched j t1 t3.
  Proof. by move => ? ? ? /andP[? ?]; rewrite -big_cat_nat. Qed.

  (** Since [service] is just a special case of [service_during], the same holds
     for [service]. *)
  Lemma service_cat:
    forall t1 t2,
      t1 <= t2 ->
      (service sched j t1) + (service_during sched j t1 t2)
      = service sched j t2.
  Proof. move=> ? ? ?; exact: service_during_cat. Qed.

  (** As a special case, we observe that the service during an interval can be
     decomposed into the first instant and the rest of the interval. *)
  Lemma service_during_first_plus_later:
    forall t1 t2,
      t1 < t2 ->
      (service_at sched j t1) + (service_during sched j t1.+1 t2)
      = service_during sched j t1 t2.
  Proof.
    by move=> ? ? ?; rewrite -service_during_instant service_during_cat// leqnSn.
  Qed.

  (** Symmetrically, we have the same for the end of the interval. *)
  Lemma service_during_last_plus_before:
    forall t1 t2,
      t1 <= t2 ->
      (service_during sched j t1 t2) + (service_at sched j t2)
      = service_during sched j t1 t2.+1.
  Proof.
    move=> t1 t2 ?; rewrite -(service_during_cat t1 t2 t2.+1) ?leqnSn ?andbT//.
    by rewrite service_during_instant.
  Qed.

  (** And hence also for [service]. *)
  Corollary service_last_plus_before:
    forall t,
      (service sched j t) + (service_at sched j t)
      = service sched j t.+1.
  Proof. move=> ?; exact: service_during_last_plus_before. Qed.

  (** Finally, we deconstruct the service received during an interval <<[t1, t3)>>
     into the service at a midpoint t2 and the service in the intervals before
     and after. *)
  Lemma service_split_at_point:
    forall t1 t2 t3,
      t1 <= t2 < t3 ->
      (service_during sched j t1 t2) + (service_at sched j t2) + (service_during sched j t2.+1 t3)
      = service_during sched j t1 t3.
  Proof.
    move => t1 t2 t3 /andP[t1t2 t2t3].
    rewrite -addnA service_during_first_plus_later// service_during_cat//.
    by rewrite t1t2 ltnW.
  Qed.

End Composition.

(** As a common special case, we establish facts about schedules in which a
    job receives either 1 or 0 service units at all times. *)
Section UnitService.

  (** Consider any job type and any processor state. *)
  Context {Job : JobType}.
  Context {PState : ProcessorState Job}.

  (** Let's consider a unit-service model... *)
  Hypothesis H_unit_service: unit_service_proc_model PState.

  (** ...and a given schedule. *)
  Variable sched : schedule PState.

  (** Let [j] be any job that is to be scheduled. *)
  Variable j : Job.

  (** First, we prove that the instantaneous service cannot be greater than 1, ... *)
  Lemma service_at_most_one:
    forall t, service_at sched j t <= 1.
  Proof. by rewrite /service_at. Qed.

  (** ... which implies that the instantaneous service always equals to 0 or 1.  *)
  Corollary service_is_zero_or_one:
    forall t, service_at sched j t = 0 \/ service_at sched j t = 1.
  Proof.
    move=> t.
    by case: service_at (service_at_most_one t) => [|[|//]] _; [left|right].
  Qed.

  (** Next we prove that the cumulative service received by job [j] in
      any interval of length [delta] is at most [delta]. *)
  Lemma cumulative_service_le_delta:
    forall t delta, service_during sched j t (t + delta) <= delta.
  Proof.
    move=> t delta; rewrite -[X in _ <= X](sum_of_ones t).
    apply: leq_sum => t' _; exact: service_at_most_one.
  Qed.

  (** Conversely, we prove that if the cumulative service received by
      job [j] in an interval of length [delta] is greater than or
      equal to [ρ], then [ρ ≤ delta]. *)
  Lemma cumulative_service_ge_delta :
    forall t delta ρ,
      ρ <= service_during sched j t (t + delta) ->
      ρ <= delta.
  Proof. move=> ??? /leq_trans; apply; exact: cumulative_service_le_delta. Qed.

  Section ServiceIsUnitGrowthFunction.

    (** We show that the service received by any job [j] during any interval is
        a unit growth function... *)
    Lemma service_during_is_unit_growth_function :
      forall t0,
        unit_growth_function (service_during sched j t0).
    Proof.
      move=> t0 t1.
      have [LEQ|LT]:= leqP t0 t1; last by rewrite service_during_geq; lia.
      rewrite addn1 -service_during_last_plus_before // leq_add2l.
      exact: service_at_most_one.
    Qed.

    (** ... and restate the same observation in terms of [service]. *)
    Corollary  service_is_unit_growth_function :
      unit_growth_function (service sched j).
    Proof. by apply: service_during_is_unit_growth_function. Qed.

    (** It follows that [service_during] does not skip over any values. *)
    Corollary exists_intermediate_service_during :
      forall t0 t1 t2 s,
        t0 <= t1 <= t2 ->
        service_during sched j t0 t1 <= s < service_during sched j t0 t2 ->
      exists t,
        t1 <= t < t2 /\
        service_during sched j t0 t = s.
    Proof.
      move=> t0 t1 t2 s /andP [t0t1 t1t2] SERV.
      apply: exists_intermediate_point => //.
      exact: service_during_is_unit_growth_function.
    Qed.

    (** To restate this observation in terms of [service], let [s] be any value
       less than the service received by job [j] by time [t]. *)
    Variable t : instant.
    Variable s : duration.
    Hypothesis H_less_than_s: s < service sched j t.

    (** There necessarily exists an earlier time [t'] where job [j] had [s]
       units of service. *)
    Corollary exists_intermediate_service :
      exists t',
        t' < t /\
        service sched j t' = s.
    Proof.
      apply: (exists_intermediate_point _ service_is_unit_growth_function 0) => //.
      by rewrite service0.
    Qed.

  End ServiceIsUnitGrowthFunction.

End UnitService.

(** We establish a basic fact about the monotonicity of service. *)
Section Monotonicity.

  (** Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: ProcessorState Job}.

  (** Consider any given schedule... *)
  Variable sched: schedule PState.

  (** ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (** We observe that the amount of service received is monotonic by definition. *)
  Lemma service_monotonic:
    forall t1 t2,
      t1 <= t2 ->
      service sched j t1 <= service sched j t2.
  Proof. by move=> t1 t2 ?; rewrite -(service_cat _ _ t1 t2)// leq_addr. Qed.

End Monotonicity.

(** Consider any job type and any processor model. *)
Section RelationToScheduled.

  Context {Job: JobType}.
  Context {PState: ProcessorState Job}.

  (** Consider any given schedule... *)
  Variable sched: schedule PState.

  (** ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (** We observe that a job that isn't scheduled in a given processor
      state cannot possibly receive service in that state. *)
  Lemma service_in_implies_scheduled_in :
    forall s,
      ~~ scheduled_in j s -> service_in j s = 0.
  Proof.
    move=> s.
    move=> /existsP Hsched; apply/eqP; rewrite sum_nat_eq0; apply/forallP => c.
    rewrite service_on_implies_scheduled_on//.
    by apply/negP => ?; apply: Hsched; exists c.
  Qed.

  (** In particular, it cannot receive service at any given time. *)
  Corollary not_scheduled_implies_no_service:
    forall t,
      ~~ scheduled_at sched j t -> service_at sched j t = 0.
  Proof. move=> ?; exact: service_in_implies_scheduled_in. Qed.

  (** Conversely, if a job receives service, then it must be scheduled. *)
  Lemma service_at_implies_scheduled_at :
    forall t,
      service_at sched j t > 0 -> scheduled_at sched j t.
  Proof.
    move=> t; case SCHEDULED: scheduled_at => //.
    by rewrite not_scheduled_implies_no_service// negbT.
  Qed.

  (** Thus, if the cumulative amount of service changes, then it must be
     scheduled, too. *)
  Lemma service_delta_implies_scheduled :
    forall t,
      service sched j t < service sched j t.+1 -> scheduled_at sched j t.
  Proof.
    move=> t; rewrite -service_last_plus_before -ltn_subLR// subnn.
    exact: service_at_implies_scheduled_at.
  Qed.

  (** We observe that a job receives cumulative service during some interval iff
     it receives services at some specific time in the interval. *)
  Lemma service_during_service_at :
    forall t1 t2,
      service_during sched j t1 t2 > 0
      <->
      exists t,
        t1 <= t < t2 /\
        service_at sched j t > 0.
  Proof.
    move=> t1 t2.
    split=> [|[t [titv nz_serv]]].
    - rewrite sum_nat_gt0 filter_predT => /hasP [t IN GT0].
      by exists t; split; [rewrite -mem_index_iota|].
    - rewrite sum_nat_gt0; apply/hasP.
      by exists t; [rewrite filter_predT mem_index_iota|].
  Qed.

  (** Thus, any job that receives some service during an interval must be
      scheduled at some point during the interval... *)
  Corollary cumulative_service_implies_scheduled :
    forall t1 t2,
      service_during sched j t1 t2 > 0 ->
      exists t,
        t1 <= t < t2 /\
        scheduled_at sched j t.
  Proof.
    move=> t1 t2; rewrite service_during_service_at => -[t' [TIMES SERVICED]].
    exists t'; split=> //; exact: service_at_implies_scheduled_at.
  Qed.

  (** ...which implies that any job with positive cumulative service must have
     been scheduled at some point. *)
  Corollary positive_service_implies_scheduled_before:
    forall t,
      service sched j t > 0 -> exists t', (t' < t /\ scheduled_at sched j t').
  Proof.
    by move=> t /cumulative_service_implies_scheduled[t' ?]; exists t'.
  Qed.

  (** We can further strengthen [service_during_service_at] to yield the
      earliest point in time at which a job receives service in an interval... *)
  Corollary service_during_service_at_earliest :
    forall t1 t2,
      service_during sched j t1 t2 > 0 ->
      exists t,
        t1 <= t < t2
        /\ service_at sched j t > 0
        /\ service_during sched j t1 t = 0.
  Proof.
    move=> t1 t2.
    rewrite service_during_service_at => [[t [IN SAT]]].
    set P := fun t' => (service_at sched j t' > 0) && (t1 <= t' < t2).
    have WITNESS: exists t', P t' by exists t; apply/andP.
    have [t' /andP [SCHED' IN'] LEAST] := ex_minnP WITNESS.
    exists t'; repeat (split => //).
    apply/eqP/contraT.
    rewrite -lt0n service_during_service_at => [[t'' [IN'' SAT'']]].
    have: t' <= t''; last by lia.
    apply/LEAST/andP; split => //.
    by lia.
  Qed.

  (** ... and make a similar observation about the same point in time
      w.r.t. [scheduled_at]. *)
  Corollary service_during_scheduled_at_earliest :
    forall t1 t2,
      service_during sched j t1 t2 > 0 ->
      exists t,
        t1 <= t < t2
        /\ scheduled_at sched j t
        /\ service_during sched j t1 t = 0.
  Proof.
    move=> t1 t2 SERVICED.
    have [t [IN [SAT NONE]]] := service_during_service_at_earliest t1 t2 SERVICED.
    exists t; repeat (split => //).
    exact: service_at_implies_scheduled_at.
  Qed.

  (** If we can assume that a scheduled job always receives service, then we can
      further relate above observations to [scheduled_at]. *)
  Section GuaranteedService.

    (** Assume [j] always receives some positive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** In other words, not being scheduled is equivalent to receiving zero
       service. *)
    Lemma no_service_not_scheduled:
      forall t,
        ~~ scheduled_at sched j t <-> service_at sched j t = 0.
    Proof.
      move=> t.
      split => [|NO_SERVICE]; first exact: service_in_implies_scheduled_in.
      apply: (contra (H_scheduled_implies_serviced j (sched t))).
      by rewrite -eqn0Ngt -NO_SERVICE.
    Qed.

    (** Then, if a job does not receive any service during an interval, it
       is not scheduled. *)
    Lemma no_service_during_implies_not_scheduled:
      forall t1 t2,
        service_during sched j t1 t2 = 0 ->
        forall t,
          t1 <= t < t2 -> ~~ scheduled_at sched j t.
    Proof.
      move=> t1 t2.
      by move=> + t titv; rewrite no_service_not_scheduled big_nat_eq0; apply.
    Qed.

    (** Conversely, if a job is not scheduled during an interval, then
        it does not receive any service in that interval *)
    Lemma not_scheduled_during_implies_zero_service:
      forall t1 t2,
        (forall t, t1 <= t < t2 -> ~~ scheduled_at sched j t) ->
        service_during sched j t1 t2 = 0.
    Proof.
      move=> t1 t2; rewrite big_nat_eq0 => + t titv => /(_ t titv).
      by rewrite no_service_not_scheduled.
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
      move=> t1 t2 [t [titv sch]]; rewrite service_during_service_at.
      exists t; split=> //; exact: H_scheduled_implies_serviced.
    Qed.

    (** ...which again applies to total service, too. *)
    Corollary scheduled_implies_nonzero_service:
      forall t,
        (exists t',
            t' < t /\
            scheduled_at sched j t') ->
        service sched j t > 0.
    Proof.
      move=> t.
      by move=> [t' ?]; apply: scheduled_implies_cumulative_service; exists t'.
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
      move=> t /positive_service_implies_scheduled_before[t' [t't sch]].
      exists t'; split=> //; rewrite t't andbT; exact: H_jobs_must_arrive.
    Qed.

    Lemma not_scheduled_before_arrival:
      forall t, t < job_arrival j -> ~~ scheduled_at sched j t.
    Proof.
      by move=> t ?; apply: (contra (H_jobs_must_arrive j t)); rewrite -ltnNge.
    Qed.

    (** We show that job [j] does not receive service at any time [t] prior to its
        arrival. *)
    Lemma service_before_job_arrival_zero:
      forall t,
        t < job_arrival j ->
        service_at sched j t = 0.
    Proof.
      move=> t NOT_ARR; rewrite not_scheduled_implies_no_service//.
      exact: not_scheduled_before_arrival.
    Qed.

    (** Note that the same property applies to the cumulative service. *)
    Lemma cumulative_service_before_job_arrival_zero :
      forall t1 t2 : instant,
        t2 <= job_arrival j ->
        service_during sched j t1 t2 = 0.
    Proof.
      move=> t1 t2 early; rewrite big_nat_eq0 => t /andP[_ t_lt_t2].
      apply: service_before_job_arrival_zero; exact: leq_trans early.
    Qed.

    (** Hence, one can ignore the service received by a job before its arrival
       time... *)
    Lemma ignore_service_before_arrival:
      forall t1 t2,
        t1 <= job_arrival j ->
        t2 >= job_arrival j ->
        service_during sched j t1 t2 = service_during sched j (job_arrival j) t2.
    Proof.
      move=> t1 t2 t1_le t2_ge.
      rewrite -(service_during_cat sched _ _ (job_arrival j)); last exact/andP.
      by rewrite cumulative_service_before_job_arrival_zero.
    Qed.

    (** ... which we can also state in terms of cumulative service. *)
    Corollary no_service_before_arrival:
      forall t,
        t <= job_arrival j -> service sched j t = 0.
    Proof. exact: cumulative_service_before_job_arrival_zero. Qed.

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
      move: H_same_service; rewrite -(service_cat _ _ t1 t2)// => /eqP.
      by rewrite -[X in X == _]addn0 eqn_add2l => /eqP.
    Qed.

    (** ...which of course implies that it does not receive service at any
       point, either. *)
    Lemma constant_service_implies_not_scheduled:
      forall t,
        t1 <= t < t2 -> service_at sched j t = 0.
    Proof.
      move=> t titv.
      have := constant_service_implies_no_service_during.
      rewrite big_nat_eq0; exact.
    Qed.

    (** We show that job [j] receives service at some point [t < t1]
       iff [j] receives service at some point [t' < t2]. *)
    Lemma same_service_implies_serviced_at_earlier_times:
      [exists t: 'I_t1, service_at sched j t > 0] =
      [exists t': 'I_t2, service_at sched j t' > 0].
    Proof.
      apply/idP/idP => /existsP[t serv].
      { by apply/existsP; exists (widen_ord H_t1_le_t2 t). }
      have [t_lt_t1|t1_le_t] := ltnP t t1.
      { by apply/existsP; exists (Ordinal t_lt_t1). }
      exfalso; move: serv; apply/negP; rewrite -eqn0Ngt.
      by apply/eqP/constant_service_implies_not_scheduled; rewrite t1_le_t /=.
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
      have CONV B : [exists b: 'I_B, scheduled_at sched j b]
                    = [exists b: 'I_B, service_at sched j b > 0].
      { apply/idP/idP => /existsP[b P]; apply/existsP; exists b.
        - exact: H_scheduled_implies_serviced.
        - exact: service_at_implies_scheduled_at. }
      by rewrite !CONV same_service_implies_serviced_at_earlier_times.
    Qed.

  End TimesWithSameService.

End RelationToScheduled.

(** * Incremental Service in Unit-Service Schedules  *)
(** In unit-service schedules, any job gains at most one unit of service at any
    time. Hence, no job "skips" an service values, which we note with the lemma
    [incremental_service_during] below. *)
Section IncrementalService.

  (** Consider any job type, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any unit-service schedule of this arrival sequence. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Hypothesis H_unit_service: unit_service_proc_model PState.

  (** We prove that if in some time interval <<[t1,t2)>> a job [j] receives [k]
      units of service, then there exists a time instant <<t ∈ [t1,t2)>> such
      that [j] is scheduled at time [t] and service of job [j] within interval
      <<[t1,t)>> is equal to [k]. *)
  Lemma incremental_service_during:
    forall j t1 t2 k,
      service_during sched j t1 t2 > k ->
      exists t, t1 <= t < t2 /\ scheduled_at sched j t /\ service_during sched j t1 t = k.
  Proof.
    move=> j t1 t2 k SERV.
    have LE: t1 < t2 by move: (service_during_ge _ _ _ _ _ SERV).
    case: k SERV => [|k] SERV; first by apply service_during_scheduled_at_earliest in SERV.
    set P := fun t' => service_during sched j t1 t' >= k.+1.
    have: exists t' : nat, t1 < t' <= t2 /\ (forall x : nat, t1 <= x < t' -> ~~ P x) /\ P t'.
    { apply: (exists_first_intermediate_point P t1 t2); first by lia.
      - by rewrite /P service_during_geq //.
      - by rewrite /P;  lia. }
    rewrite /P; move=> [t' [IN' [LIMIT Pt']]]; clear P.
    set P'' := fun t'' => (t' <= t'' < t2) && (service_at sched j t'' > 0).
    have WITNESS: exists t'', P'' t''.
    { have: 0 < service_during sched j t' t2;
        last by rewrite service_during_service_at => [[t'' [IN'' SERVICED]]]
                ; exists t''; apply/andP; split.
      move: SERV; rewrite -(service_during_cat _ _ t1 t'.-1 t2); last by lia. move=> SERV.
      have SERV2: service_during sched j t1 t'.-1 <= k
        by rewrite leqNgt; apply (LIMIT t'.-1); lia.
      have: service_during sched j t'.-1 t2 >= 2 by lia.
      rewrite -service_during_first_plus_later; last by lia.
      move: (IN') => /andP [LE' _]; rewrite (ltn_predK LE').
      by case: (service_is_zero_or_one _ sched j t'.-1) =>  [//|->|->]; try lia. }
    have [t''' /andP [IN''' SCHED'''] MIN] := ex_minnP WITNESS.
    exists t'''; repeat split; [by lia|by apply: service_at_implies_scheduled_at|].
    have ->:  service_during sched j t1 t''' = service_during sched j t1 t'.
    { rewrite -(service_during_cat _ _ t1 t' t'''); last by lia.
      have [Z|POS] := leqP (service_during sched j t' t''') 0; first by lia.
      exfalso.
      move: POS; rewrite service_during_service_at => [[x [xIN xSERV]]].
      have xP'': P'' x by apply/andP;split; [by lia| by[]].
      by move: (MIN x xP''); lia. }
    move: Pt'; rewrite leq_eqVlt => /orP [/eqP -> //|XL].
    exfalso. move: XL.
    have ->: service_during sched j t1 t' = service_during sched j t1 t'.-1.+1
      by move: (IN') => /andP [LE' _]; rewrite (ltn_predK LE').
    rewrite -service_during_last_plus_before; last by lia. move=> ABOVE.
    have BELOW: service_during sched j t1 t'.-1 <= k
      by rewrite leqNgt; apply (LIMIT t'.-1); lia.
    have: service_at sched j t'.-1 > 1 by lia.
    have: service_at sched j t'.-1 <= 1 by apply/service_at_most_one.
    by lia.
  Qed.

End IncrementalService.


Section ServiceInTwoSchedules.

  (** Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: ProcessorState Job}.

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
    Proof. exact/eq_big_nat/H_sched1_sched2_same_service_at. Qed.

  End ServiceDuringEquivalentInterval.

  (** We can leverage the previous lemma to conclude that two schedules
      that match in a given interval will also have the same cumulative
      service across the interval. *)
  Corollary equal_prefix_implies_same_service_during:
    forall t1 t2,
      (forall t, t1 <= t < t2 -> sched1 t = sched2 t) ->
      forall j, service_during sched1 j t1 t2 = service_during sched2 j t1 t2.
  Proof.
    move=> t1 t2 sch j; apply: same_service_during => t' t'itv.
    by rewrite /service_at sch.
  Qed.

  (** For convenience, we restate the corollary also at the level of
      [service] for identical prefixes. *)
  Corollary identical_prefix_service:
    forall h,
      identical_prefix sched1 sched2 h ->
      forall j, service sched1 j h = service sched2 j h.
  Proof. move=> ? ? ?; exact: equal_prefix_implies_same_service_during. Qed.

End ServiceInTwoSchedules.

(** In this section we prove a lemma on the service received by a job
    in a uniprocessor schedule. *)
Section UniProcessor.
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Allow for any uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** Next, consider any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** We prove that if two jobs [j1] and [j2] receive service at the
      same instant then [j1] is equal to [j2]. *)
  Lemma recv_service_impl_same_job :
    forall j1 j2 t,
      receives_service_at sched j1 t ->
      receives_service_at sched j2 t ->
      j1 = j2.
  Proof.
    move => j1 j2 t SERV1 SERV2.
    apply service_at_implies_scheduled_at in SERV1.
    apply service_at_implies_scheduled_at in SERV2.
    by apply (H_uniproc j1 j2 sched t).
  Qed.

End UniProcessor.
