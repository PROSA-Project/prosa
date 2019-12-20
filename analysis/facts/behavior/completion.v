Require Export prosa.analysis.facts.behavior.service.
Require Export prosa.analysis.facts.behavior.arrivals.

(** * Completion *)

(** In this file, we establish basic facts about job completions. *)
Section CompletionFacts.
  
  (** Consider any job type,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.

  (** ...any kind of processor model,... *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** ...and a given schedule. *)
  Variable sched: schedule PState.

  (** Let j be any job that is to be scheduled. *)
  Variable j: Job.

  (** We prove that after job j completes, it remains completed. *)
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

  (** We observe that being incomplete is the same as not having received
     sufficient service yet... *)
  Lemma less_service_than_cost_is_incomplete:
    forall t,
      service sched j t < job_cost j
      <-> ~~ completed_by sched j t.
  Proof.
    move=> t. by split; rewrite /completed_by; [rewrite -ltnNge // | rewrite ltnNge //].
  Qed.

  (** ...which is also the same as having positive remaining cost. *)
  Lemma incomplete_is_positive_remaining_cost:
    forall t,
      ~~ completed_by sched j t
      <-> remaining_cost sched j t > 0.
  Proof.
    move=> t. by split; rewrite /remaining_cost -less_service_than_cost_is_incomplete subn_gt0 //.
  Qed.

  (** Assume that completed jobs do not execute. *)
  Hypothesis H_completed_jobs:
    completed_jobs_dont_execute sched.

  (** Further, we note that if a job receives service at some time t, then its
     remaining cost at this time is positive. *)
  Lemma serviced_implies_positive_remaining_cost:
    forall t,
      service_at sched j t > 0 ->
      remaining_cost sched j t > 0.
  Proof.
    move=> t SERVICE.
    rewrite -incomplete_is_positive_remaining_cost -less_service_than_cost_is_incomplete.
    apply H_completed_jobs.
    by apply service_at_implies_scheduled_at.
  Qed.

  (** Consequently, if we have a have processor model where scheduled jobs
      necessarily receive service, we can conclude that scheduled jobs have
      remaining positive cost. *)

  (** Assume a scheduled job always receives some positive service. *)
  Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

  (** Then a scheduled job has positive remaining cost. *)
  Corollary scheduled_implies_positive_remaining_cost:
    forall t,
      scheduled_at sched j t ->
      remaining_cost sched j t > 0.
  Proof.
    rewrite /scheduled_at => t SCHEDULED.
      by apply: serviced_implies_positive_remaining_cost; rewrite /service_at; apply: H_scheduled_implies_serviced.
  Qed.

  (** We also prove that a completed job cannot be scheduled... *)
  Lemma completed_implies_not_scheduled:
    forall t,
      completed_by sched j t ->
      ~~ scheduled_at sched j t.
  Proof.
    move=> t COMP.
    apply contra with (b := ~~ completed_by sched j t);
      last by apply /negPn.
    move=> SCHED. move: (H_completed_jobs j t SCHED).
    by rewrite less_service_than_cost_is_incomplete.
  Qed.

  (** ... and that a scheduled job cannot be completed. *)
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

End CompletionFacts.

(** In this section, we establish some facts that are really about service,
    but are also related to completion and rely on some of the above lemmas.
    Hence they are in this file rather than in the service facts file. *)
Section ServiceAndCompletionFacts.  

  (** Consider any job type,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.

  (** ...any kind of processor model,... *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** ...and a given schedule. *)
  Variable sched: schedule PState.

  (** Assume that completed jobs do not execute. *)
  Hypothesis H_completed_jobs:
    completed_jobs_dont_execute sched.

  (** Let [j] be any job that is to be scheduled. *)
  Variable j: Job.

  (** Assume that a scheduled job receives exactly one time unit of service. *)
  Hypothesis H_unit_service: unit_service_proc_model PState.

  (** To begin with, we establish that the cumulative service never exceeds a
     job's total cost if service increases only by one at each step since
     completed jobs don't execute. *)
  Lemma service_at_most_cost:
    forall t,
      service sched j t <= job_cost j.
  Proof.
    move=> t.
    elim: t => [|t]; first by rewrite service0.
    rewrite -service_last_plus_before.
    rewrite leq_eqVlt => /orP [/eqP EQ|LT].
    - rewrite not_scheduled_implies_no_service;
        first by rewrite addn0 EQ.
      apply completed_implies_not_scheduled => //.
      by rewrite /completed_by EQ.
    - apply leq_trans with (n := service sched j t + 1);
        last by rewrite addn1.
      rewrite leq_add2l.
      by apply H_unit_service.
  Qed.

  (** This lets us conclude that [service] and [remaining_cost] are complements
     of one another. *)
  Lemma service_cost_invariant:
    forall t,
      (service sched j t) + (remaining_cost sched j t) = job_cost j.
  Proof.
    move=> t.
    rewrite /remaining_cost subnKC //.
    by apply service_at_most_cost.
  Qed.

  (** We show that the service received by job [j] in any interval is no larger
     than its cost. *)
  Lemma cumulative_service_le_job_cost:
    forall t t',
      service_during sched j t t' <= job_cost j.
  Proof.
    move=> t t'.
    case/orP: (leq_total t t') => [tt'|tt']; last by rewrite service_during_geq //.
    apply leq_trans with (n := service sched j t'); last by apply: service_at_most_cost.
    rewrite /service. rewrite -(service_during_cat sched j 0 t t') // leq_addl //.
  Qed.

  (** If a job isn't complete at time [t], it can't be completed at time [t +
     remaining_cost j t - 1]. *)
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

  Section GuaranteedService.

    (** Assume a scheduled job always receives some positive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** Assume that jobs are not released early. *)
    Context `{JobArrival Job}.
    Hypothesis H_jobs_must_arrive: jobs_must_arrive_to_execute sched.

    (** We show that if job j is scheduled, then it must be pending. *)
    Lemma scheduled_implies_pending:
      forall t,
        scheduled_at sched j t ->
        pending sched j t.
    Proof.
      move=> t SCHED.
      rewrite /pending.
      apply /andP; split;
        first by apply: H_jobs_must_arrive => //.
      by apply: scheduled_implies_not_completed => //.
    Qed.

  End GuaranteedService.

End ServiceAndCompletionFacts.

(** In this section, we establish facts that on jobs with non-zero costs that
    must arrive to execute. *)
Section PositiveCost.

  (** Consider any type of jobs with cost and arrival-time attributes,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** ...any kind of processor model,... *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** ...and a given schedule. *)
  Variable sched: schedule PState.

  (** Let [j] be any job that is to be scheduled. *)
  Variable j: Job.

  (** We assume that job [j] has positive cost, from which we can
     infer that there always is a time in which [j] is pending, ... *)
  Hypothesis H_positive_cost: job_cost j > 0.

  (** ...and that jobs must arrive to execute. *)
  Hypothesis H_jobs_must_arrive:
    jobs_must_arrive_to_execute sched.

  (** Then, we prove that the job with a positive cost
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

  (** We also prove that the job is pending at the moment of its arrival. *)
  Lemma job_pending_at_arrival:
    pending sched j (job_arrival j).
  Proof.
    rewrite /pending.
    apply/andP; split;
    first by rewrite /has_arrived //.
    rewrite /completed_by no_service_before_arrival // -ltnNge //.
  Qed.

End PositiveCost.

Section CompletedJobs.
  
  (** Consider any kinds of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any schedule... *)
  Variable sched : schedule PState.

  (** ...and suppose that jobs have a cost, an arrival time, and a notion of
     readiness. *)
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobReady Job PState}.

  (** We observe that a given job is ready only if it is also incomplete... *)
  Lemma ready_implies_incomplete:
    forall j t, job_ready sched j t -> ~~ completed_by sched j t.
  Proof.
    move=> j t READY.
    move: (any_ready_job_is_pending sched j t READY).
    by rewrite /pending => /andP [_ INCOMPLETE].
  Qed.

  (** ...and lift this observation also to the level of whole schedules. *)
  Lemma completed_jobs_are_not_ready:
    jobs_must_be_ready_to_execute sched ->
    completed_jobs_dont_execute sched.
  Proof.
    rewrite /jobs_must_be_ready_to_execute /completed_jobs_dont_execute.
    move=> READY_IF_SCHED j t SCHED.
    move: (READY_IF_SCHED j t SCHED) => READY.
    rewrite less_service_than_cost_is_incomplete.
    by apply ready_implies_incomplete.
  Qed.

  (** We further observe that completed jobs don't execute if scheduled jobs
     always receive non-zero service and cumulative service never exceeds job
     costs. *)
  Lemma ideal_progress_completed_jobs:
    ideal_progress_proc_model PState ->
    (forall j t, service sched j t <= job_cost j) ->
    completed_jobs_dont_execute sched.
  Proof.
    move=> IDEAL SERVICE_BOUND j t SCHED.
    have UB := SERVICE_BOUND j t.+1.
    have POS := IDEAL _ _ SCHED.
    apply ltn_leq_trans with (n := service sched j t.+1) => //.
    rewrite -service_last_plus_before /service_at.
    by rewrite -{1}(addn0 (service sched j t)) ltn_add2l.
  Qed.

End CompletedJobs.
