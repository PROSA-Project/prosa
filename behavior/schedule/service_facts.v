From rt.behavior.schedule Require Export schedule.
From rt.util Require Import tactics step_function.

(** In this file, we establish basic facts about the service received by
    jobs. *)


Section UnitService.
  (** To begin with, we establish facts about schedules in which a job receives
      either 1 or 0 service units at all times. *)

  (* Consider any job type and any processor state. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* We say that a kind processor state provides unit service if no
     job ever receives more than one unit of service at any time. *)
  Definition unit_service_proc_model := forall j s, service_in j s <= 1.

  (* Let's consider a unit-service model... *)
  Hypothesis H_unit_service: unit_service_proc_model.

  (* ...and a given schedule. *)
  Variable sched: schedule PState.

  (* Let j be any job that is to be scheduled. *)
  Variable j: Job.

  (* First, we prove that the instantaneous service cannot be greater than 1, ... *)
  Lemma service_at_most_one:
    forall t, service_at sched j t <= 1.
  Proof.
      by move=> t; rewrite /service_at.
  Qed.

  (* ...which implies that the cumulative service received by job j in any
     interval of length delta is at most delta. *)
  Lemma cumulative_service_le_delta:
    forall t delta,
      service_during sched j t (t + delta) <= delta.
  Proof.
    unfold service_during; intros t delta.
    apply leq_trans with (n := \sum_(t <= t0 < t + delta) 1);
      last by simpl_sum_const; rewrite addKn leqnn.
      by apply: leq_sum => t' _; apply: service_at_most_one.
  Qed.

End UnitService.

Section Composition.

  (* Consider any job type and any processor state. *)
  Context {Job: eqType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* For any given schedule... *)
  Variable sched: schedule PState.

  (* ...and any given job... *)
  Variable j: Job.

  (* ...we establish a number of useful rewriting rules that decompose
     the service received during an interval into smaller intervals. *)

  (* As a trivial base case, no job receives any service during an empty
     interval. *)
  Lemma service_during_geq:
    forall t1 t2,
      t1 >= t2 -> service_during sched j t1 t2 = 0.
  Proof.
    move=> t1 t2 t1t2.
    rewrite /service_during big_geq //.
  Qed.

  (* Equally trivially, no job has received service prior to time zero. *)
  Corollary service0:
    service sched j 0 = 0.
  Proof.
    rewrite /service service_during_geq //.
  Qed.

  (* Trivially, an interval consiting of one time unit is equivalent to
     service_at.  *)
  Lemma service_during_instant:
    forall t,
      service_during sched j t t.+1 = service_at sched j t.
  Proof.
    move => t.
     by rewrite /service_during big_nat_recr ?big_geq //.
  Qed.

  (* Next, we observe that we can look at the service received during an
     interval [t1, t3) as the sum of the service during [t1, t2) and [t2, t3)
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

  (* Since [service] is just a special case of [service_during], the same holds
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

  (* As a special case, we observe that the service during an interval can be
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

  (* Symmetrically, we have the same for the end of the interval. *)
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

    (* And hence also for [service]. *)
    Corollary service_last_plus_before:
      forall t,
        (service sched j t) + (service_at sched j t)
        = service sched j t.+1.
    Proof.
      move=> t.
      rewrite /service. rewrite -service_during_last_plus_before //.
    Qed.

  (* Finally, we deconstruct the service received during an interval [t1, t3)
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

Section Monotonicity.
  (** We establish a basic fact about the monotonicity of service. *)

  (* Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* Consider any given schedule... *)
  Variable sched: schedule PState.

  (* ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (* We observe that the amount of service received is monotonic by definition. *)
  Lemma service_monotonic:
    forall t1 t2,
      t1 <= t2 ->
      service sched j t1 <= service sched j t2.
  Proof.
    move=> t1 t2 let1t2.
      by rewrite -(service_cat sched j t1 t2 let1t2); apply: leq_addr.
  Qed.

End Monotonicity.

Section RelationToScheduled.
  (* Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* Consider any given schedule... *)
  Variable sched: schedule PState.

  (* ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (* We observe that a job that isn't scheduled cannot possibly receive service. *)
  Lemma not_scheduled_implies_no_service:
    forall t,
      ~~ scheduled_at sched j t -> service_at sched j t = 0.
  Proof.
    rewrite /service_at /scheduled_at.
    move=> t NOT_SCHED.
    rewrite service_implies_scheduled //.
      by apply: negbTE.
  Qed.

  (* Conversely, if a job receives service, then it must be scheduled. *)
  Lemma service_at_implies_scheduled_at:
    forall t,
      service_at sched j t > 0 -> scheduled_at sched j t.
  Proof.
    move=> t.
    destruct (scheduled_at sched j t) eqn:SCHEDULED; first trivial.
    rewrite not_scheduled_implies_no_service // negbT //.
  Qed.

  (* Thus, if the cumulative amount of service changes, then it must be
     scheduled, too. *)
  Lemma service_delta_implies_scheduled:
    forall t,
      service sched j t < service sched j t.+1 -> scheduled_at sched j t.
  Proof.
    move => t.
    rewrite -service_last_plus_before -{1}(addn0 (service sched j t)) ltn_add2l.
    apply: service_at_implies_scheduled_at.
  Qed.

  (* Similarly, any job with positive cumulative service must have been
     scheduled before. *)
  Lemma positive_service_implies_scheduled_before:
    forall t,
      service sched j t > 0 -> exists t', (t' < t /\ scheduled_at sched j t').
  Proof.
    move=> t.
    elim: t => [|t IND SERVICE].
    - rewrite service0 //.
    - destruct (scheduled_at sched j t) eqn:SCHED.
      * exists t; split; auto.
      * move: SERVICE. rewrite -service_last_plus_before not_scheduled_implies_no_service; last by apply negbT; assumption. rewrite addn0.
        move=> SERVICE. apply IND in SERVICE. inversion SERVICE as [t'' [t''t SCHED_AT]].
        exists t''; split; auto.
  Qed.

  Section AfterArrival.
    (* Futhermore, if we know that jobs are not released early, then we can
       narrow the interval during which they must have been scheduled. *)

    Context `{JobArrival Job}.

    (* Assume that jobs must arrive to execute. *)
    Hypothesis H_jobs_must_arrive:
      jobs_must_arrive_to_execute sched.

    (* We prove that any job with positive cumulative service at time [t] must
       have been scheduled some time since its arrival and before time [t]. *)
    Lemma positive_service_implies_scheduled_since_arrival:
      forall t,
        service sched j t > 0 -> exists t', (job_arrival j <= t' < t /\ scheduled_at sched j t').
    Proof.
      move=> t SERVICE.
      have EX_SCHED := positive_service_implies_scheduled_before t SERVICE.
      inversion EX_SCHED as [t'' [TIMES SCHED_AT]].
      exists t''; split; last by assumption.
      rewrite /(_ && _) ifT //.
      move: H_jobs_must_arrive. rewrite /jobs_must_arrive_to_execute /has_arrived => ARR.
        by apply: ARR; exact.
    Qed.

  End AfterArrival.

End RelationToScheduled.
