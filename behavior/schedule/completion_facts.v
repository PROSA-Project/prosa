From rt.behavior.schedule Require Export schedule service_facts.

(** In this file, we establish basic facts about job completions. *)


Section CompletionFacts.
  (* Consider any job type,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.

  (* ...any kind of processor model,... *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* ...and a given schedule. *)
  Variable sched: schedule PState.

  (* Let j be any job that is to be scheduled. *)
  Variable j: Job.

  (* We prove that after job j completes, it remains completed. *)
  Lemma completion_monotonic:
    forall t t',
      t <= t' ->
      completed_by sched j t ->
      completed_by sched j t'.
  Proof.
    move => t t' LE. rewrite /completed_by /service => COMP.
    apply leq_trans with (n := service_during sched j 0 t); auto.
    by apply service_monotonic.
  Qed.

  (* We observe that being incomplete is the same as not having received
     sufficient service yet... *)
  Lemma less_service_than_cost_is_incomplete:
    forall t,
      service sched j t < job_cost j
      <->
      ~~ completed_by sched j t.
  Proof.
    move=> t. by split; rewrite /completed_by; [rewrite -ltnNge // | rewrite ltnNge //].
  Qed.

  (* ...which is also the same as having positive remaining cost. *)
  Lemma incomplete_is_positive_remaining_cost:
    forall t,
      ~~ completed_by sched j t
      <->
      remaining_cost sched j t > 0.
  Proof.
    move=> t. by split; rewrite /remaining_cost -less_service_than_cost_is_incomplete subn_gt0 //.
  Qed.

  (* Assume that completed jobs do not execute. *)
  Hypothesis H_completed_jobs:
    completed_jobs_dont_execute sched.

  (* Further, we note that if a job receives service at some time t, then its
     remaining cost at this time is positive. *)
  Lemma serviced_implies_positive_remaining_cost:
    forall t,
      service_at sched j t > 0 ->
      remaining_cost sched j t > 0.
  Proof.
    move=> t SERVICE.
    rewrite subn_gt0 /service /service_during.
    apply leq_trans with (\sum_(0 <= t0 < t.+1) service_at sched j t0);
      last by rewrite H_completed_jobs.
      by rewrite big_nat_recr //= -addn1 leq_add2l.
  Qed.

  (* Consequently, if we have a have processor model where scheduled jobs
   * necessarily receive service, we can conclude that scheduled jobs have
   * remaining positive cost. *)

  (* Assume a scheduled job always receives some positive service. *)
  Hypothesis H_scheduled_implies_serviced:
    forall j s, scheduled_in j s -> service_in j s > 0.

  (* Then a scheduled job has positive remaining cost. *)
  Corollary scheduled_implies_positive_remaining_cost:
    forall t,
      scheduled_at sched j t ->
      remaining_cost sched j t > 0.
  Proof.
    rewrite /scheduled_at => t SCHEDULED.
      by apply: serviced_implies_positive_remaining_cost; rewrite /service_at; apply: H_scheduled_implies_serviced.
  Qed.

  (* We also prove that a completed job cannot be scheduled... *)
  Lemma completed_implies_not_scheduled:
    forall t,
      completed_by sched j t ->
      ~~ scheduled_at sched j t.
  Proof.
    rename H_completed_jobs into COMP.
    unfold completed_jobs_dont_execute in *.
    intros t COMPLETED.
    apply/negP; red; intro SCHED.
    have BUG := COMP j t.+1.
    rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
    rewrite /service /service_during big_nat_recr // /= -addn1.
    apply leq_add.
    * by rewrite -/(service_during sched j 0 t) -/(completed_by sched j t).
    * by rewrite /service_at; apply: H_scheduled_implies_serviced; rewrite -/(scheduled_at _ _ _).
  Qed.

  (* ... and that a scheduled job cannot be completed. *)
  Lemma scheduled_implies_not_completed:
    forall t,
      scheduled_at sched j t ->
      ~~ completed_by sched j t.
  Proof.
    move=> t SCHED.
    have REMPOS := scheduled_implies_positive_remaining_cost t SCHED.
    rewrite /remaining_cost subn_gt0 in REMPOS.
      by rewrite -less_service_than_cost_is_incomplete.
  Qed.

  (* We further observe that [service] and [remaining_cost] are complements of
     one another. *)
  Lemma service_cost_invariant:
    forall t,
      (service sched j t) + (remaining_cost sched j t) = job_cost j.
  Proof.
    move=> t. rewrite /remaining_cost subnKC //.
  Qed.

End CompletionFacts.


Section ServiceAndCompletionFacts.
  (** In this section, we establish some facts that are really about service,
      but are also related to completion and rely on some of the above lemmas.
      Hence they are in this file, rather than service_facts.v. *)

  (* Consider any job type,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.

  (* ...any kind of processor model,... *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* ...and a given schedule. *)
  Variable sched: schedule PState.

  (* Assume that completed jobs do not execute. *)
  Hypothesis H_completed_jobs:
    completed_jobs_dont_execute sched.

  (* Let j be any job that is to be scheduled. *)
  Variable j: Job.

  (* Assume that a scheduled job receives exactly one time unit of service. *)
  Hypothesis H_unit_service: unit_service_proc_model.

  Section GuaranteedService.

    (* Assume a scheduled job always receives some positive service. *)
    Hypothesis H_scheduled_implies_serviced:
      forall j s, scheduled_in j s -> service_in j s > 0.

    (* Then we can easily show that the service never exceeds the total cost of
       the job. *)
    Lemma service_le_cost:
      forall t,
        service sched j t <= job_cost j.
    Proof.
      elim => [| n IH]; first by rewrite service0 //.
      rewrite leq_eqVlt in IH.
      case/orP: IH => [EQ | LT]; rewrite -service_last_plus_before.
      * rewrite not_scheduled_implies_no_service; first by rewrite addn0 //.
        apply: completed_implies_not_scheduled; auto. unfold unit_service_proc_model in H_unit_service.
        move /eqP in EQ.
        rewrite /completed_by EQ //.
      * apply leq_trans with (n := service sched j n + 1).
        - rewrite leq_add2l /service_at //.
        - rewrite -(ltnS (service sched j n + 1) _) -(addn1 (job_cost j)) ltn_add2r //.
    Qed.

    (* We show that the service received by job j in any interval is no larger
       than its cost. *)
    Lemma cumulative_service_le_job_cost:
      forall t t',
        service_during sched j t t' <= job_cost j.
    Proof.
      move=> t t'.
      case/orP: (leq_total t t') => [tt'|tt']; last by rewrite service_during_geq //.
      apply leq_trans with (n := service sched j t'); last by apply: service_le_cost.
      rewrite /service. rewrite -(service_during_cat sched j 0 t t') // leq_addl //.
    Qed.

    Section ProperReleases.
      Context `{JobArrival Job}.

      (* Assume that jobs are not released early. *)
      Hypothesis H_jobs_must_arrive:
        jobs_must_arrive_to_execute sched.

      (* We show that if job j is scheduled, then it must be pending. *)
      Lemma scheduled_implies_pending:
        forall t,
          scheduled_at sched j t ->
          pending sched j t.
      Proof.
        move=> t SCHED.
        rewrite /pending.
        apply /andP; split;
          first by apply: H_jobs_must_arrive => //.
        apply: scheduled_implies_not_completed => //.
      Qed.

    End ProperReleases.
  End GuaranteedService.

  (* If a job isn't complete at time t, it can't be completed at time (t +
     remaining_cost j t - 1). *)
  Lemma job_doesnt_complete_before_remaining_cost:
    forall t,
      ~~ completed_by sched j t ->
      ~~ completed_by sched j (t + remaining_cost sched j t - 1).
  Proof.
    move=> t.
    rewrite incomplete_is_positive_remaining_cost => REMCOST.
    rewrite -less_service_than_cost_is_incomplete -(service_cat sched j t);
      last by rewrite -addnBA //; apply: leq_addr.
    apply leq_ltn_trans with (n := service sched j t + remaining_cost sched j t - 1).
    - by rewrite -!addnBA //; rewrite leq_add2l; apply cumulative_service_le_delta; exact.
    - rewrite service_cost_invariant // -subn_gt0 subKn //.
      move: REMCOST. rewrite /remaining_cost subn_gt0 => SERVICE.
      by apply leq_ltn_trans with (n := service sched j t).
 Qed.

End ServiceAndCompletionFacts.

Section PositiveCost.
  (** In this section, we establish facts that on jobs with non-zero costs that
      must arrive to execute. *)

  (* Consider any type of jobs with cost and arrival-time attributes,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (* ...any kind of processor model,... *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (* ...and a given schedule. *)
  Variable sched: schedule PState.

  (* Let j be any job that is to be scheduled. *)
  Variable j: Job.

  (* We assume that job j has positive cost, from which we can
     infer that there always is a time in which j is pending, ... *)
  Hypothesis H_positive_cost: job_cost j > 0.

  (* ...and that jobs must arrive to execute. *)
  Hypothesis H_jobs_must_arrive:
    jobs_must_arrive_to_execute sched.

  (* Then, we prove that the job with a positive cost
     must be scheduled to be completed. *)
  Lemma completed_implies_scheduled_before:
    forall t,
      completed_by sched j t ->
      exists t',
        job_arrival j <= t' < t
        /\ scheduled_at sched j t'.
  Proof.
    rewrite /completed_by.
    move=> t COMPLETE.
    have POSITIVE_SERVICE: 0 < service sched j t
      by apply leq_trans with (n := job_cost j); auto.
    by apply: positive_service_implies_scheduled_since_arrival; assumption.
 Qed.

  (* We also prove that the job is pending at the moment of its arrival. *)
  Lemma job_pending_at_arrival:
    pending sched j (job_arrival j).
  Proof.
    rewrite /pending.
    apply/andP; split;
      first by rewrite /has_arrived //.
    rewrite /completed_by no_service_before_arrival // -ltnNge //.
  Qed.

End PositiveCost.
