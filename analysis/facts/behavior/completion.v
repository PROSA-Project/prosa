Require Export prosa.model.job.properties.
Require Export prosa.analysis.facts.behavior.service.
Require Export prosa.analysis.facts.behavior.arrivals.
Require Export prosa.analysis.definitions.schedule_prefix.

(** * Completion *)

(** In this file, we establish basic facts about job completions. *)
Section CompletionFacts.

  (** Consider any job type,...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** ...any kind of processor model,... *)
  Context {PState: ProcessorState Job}.

  (** ...and a given schedule. *)
  Variable sched: schedule PState.

  (** Let [j] be any job that is to be scheduled. *)
  Variable j: Job.

  (** We prove that after job [j] completes, it remains completed. *)
  Lemma completion_monotonic:
    forall t t',
      t <= t' ->
      completed_by sched j t ->
      completed_by sched j t'.
  Proof. move=> ? ? ? /leq_trans; apply; exact: service_monotonic. Qed.

  (** We prove that if [j] is not completed by [t'], then it's also not
      completed by any earlier instant. *)
  Lemma incompletion_monotonic:
    forall t t',
      t <= t' ->
      ~~ completed_by sched j t' ->
      ~~ completed_by sched j t.
  Proof. move=> ? ? ?; exact/contra/completion_monotonic. Qed.

  (** We observe that being incomplete is the same as not having received
      sufficient service yet, ... *)
  Lemma less_service_than_cost_is_incomplete:
    forall t,
      service sched j t < job_cost j
      <-> ~~ completed_by sched j t.
  Proof. by move=> ?; rewrite -ltnNge. Qed.

  (** ... which is also the same as having positive remaining cost. *)
  Lemma incomplete_is_positive_remaining_cost:
    forall t,
      ~~ completed_by sched j t
      <-> remaining_cost sched j t > 0.
  Proof.
    by move=> ?; rewrite -less_service_than_cost_is_incomplete subn_gt0.
  Qed.

  (** Trivially, it follows that an incomplete job has a positive cost. *)
  Corollary incomplete_implies_positive_cost:
    forall t,
      ~~ completed_by sched j t ->
      job_cost_positive j.
  Proof.
    move=> t INCOMP; apply: leq_trans (leq_subr (service sched j t) _).
    by rewrite -incomplete_is_positive_remaining_cost.
  Qed.

  (** In the remainder of this section, we assume that schedules are
      "well-formed": jobs are scheduled neither before their arrival
      nor after their completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs : completed_jobs_dont_execute sched.

  (** Clearly, if a job is scheduled, its cost is positive. *)
  Lemma scheduled_implies_positive_cost :
    forall t,
      scheduled_at sched j t ->
      0 < job_cost j.
  Proof.
    move=> t SCHED; move_neq_up ZE; move: ZE.
    by rewrite leqn0 => /eqP ZE; apply H_completed_jobs in SCHED; rewrite ZE in SCHED.
  Qed.

  (** To simplify subsequent proofs, we restate the assumption
      [H_completed_jobs] as a trivial corollary. *)
  Corollary service_lt_cost :
    forall t,
      scheduled_at sched j t -> service sched j t < job_cost j.
  Proof. exact: H_completed_jobs. Qed.

  (** We observe that a job that is completed at the instant of its
      arrival has a cost of zero. *)
  Lemma completed_on_arrival_implies_zero_cost :
    completed_by sched j (job_arrival j) ->
    job_cost j = 0.
  Proof.
    by rewrite /completed_by no_service_before_arrival// leqn0 => /eqP.
  Qed.

  (** Further, we note that if a job receives service at some time t, then its
      remaining cost at this time is positive. *)
  Lemma serviced_implies_positive_remaining_cost:
    forall t,
      service_at sched j t > 0 ->
      remaining_cost sched j t > 0.
  Proof.
    move=> t SERVICE.
    rewrite -incomplete_is_positive_remaining_cost.
    rewrite -less_service_than_cost_is_incomplete.
    exact/service_lt_cost/service_at_implies_scheduled_at.
  Qed.

  (** Consequently, if we have a processor model where scheduled jobs
      necessarily receive service, we can conclude that scheduled jobs have
      remaining positive cost. *)

  (** Assume a scheduled job always receives some positive service. *)
  Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

  (** To simplify subsequent proofs, we restate the assumption
      [H_scheduled_implies_serviced] as a trivial corollary. *)
  Corollary scheduled_implies_serviced :
    forall s,
      scheduled_in j s -> 0 < service_in j s.
  Proof. exact: H_scheduled_implies_serviced. Qed.

  (** Then a scheduled job has positive remaining cost. *)
  Corollary scheduled_implies_positive_remaining_cost:
    forall t,
      scheduled_at sched j t ->
      remaining_cost sched j t > 0.
  Proof.
    move=> t sch.
    exact/serviced_implies_positive_remaining_cost/scheduled_implies_serviced.
  Qed.

  (** We also prove that a scheduled job cannot be completed, ... *)
  Lemma scheduled_implies_not_completed :
    forall t,
      scheduled_at sched j t -> ~~ completed_by sched j t.
  Proof.
    move=> t sch.
    by rewrite -less_service_than_cost_is_incomplete service_lt_cost.
  Qed.

  (** ... that an incomplete job that is not scheduled remains incomplete, ... *)
  Lemma not_scheduled_remains_incomplete :
    forall t,
      ~~ completed_by sched j t ->
      ~~ scheduled_at sched j t ->
      (~~ completed_by sched j t.+1).
  Proof.
    move=> t + NSCHED.
    rewrite /completed_by/service -service_during_last_plus_before //.
    by rewrite not_scheduled_implies_no_service // addn0.
  Qed.

  (** ... and that a completed job cannot be scheduled. *)
  Lemma completed_implies_not_scheduled :
    forall t,
      completed_by sched j t -> ~~ scheduled_at sched j t.
  Proof. move=> ? /negPn; exact/contra/scheduled_implies_not_completed. Qed.

  (** Job [j] cannot be pending before and at time [0]. *)
  Remark not_pending_earlier_and_at_0 :
    ~~ pending_earlier_and_at sched j 0.
  Proof.
    rewrite /pending_earlier_and_at negb_and; apply/orP; left.
    by rewrite /arrived_before -ltnNge.
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
  Context {PState: ProcessorState Job}.

  (** ...and a given schedule. *)
  Variable sched: schedule PState.

  (** Assume that completed jobs do not execute. *)
  Hypothesis H_completed_jobs:
    completed_jobs_dont_execute sched.

  (** Let [j] be any job that is to be scheduled. *)
  Variable j: Job.

  (** Assume that a scheduled job receives exactly one time unit of service. *)
  Hypothesis H_unit_service: unit_service_proc_model PState.

  (** To simplify subsequent proofs, we restate the assumption
      [H_unit_service] as a trivial corollary. *)
  Lemma unit_service :
    forall s,
      service_in j s <= 1.
  Proof. exact: H_unit_service. Qed.

  (** To begin with, we establish that the cumulative service never exceeds a
     job's total cost if service increases only by one at each step since
     completed jobs don't execute. *)
  Lemma service_at_most_cost:
    forall t,
      service sched j t <= job_cost j.
  Proof.
    elim=> [|t]; first by rewrite service0.
    rewrite -service_last_plus_before.
    rewrite leq_eqVlt => /orP[/eqP EQ|LT].
    - rewrite not_scheduled_implies_no_service ?EQ ?addn0//.
      apply: completed_implies_not_scheduled => //.
      by rewrite /completed_by EQ.
    - have: service_at sched j t <= 1 by exact: unit_service.
      rewrite -(leq_add2l (service sched j t)) => /leq_trans; apply.
      by rewrite addn1.
  Qed.

  (** This lets us conclude that [service] and [remaining_cost] are complements
     of one another. *)
  Lemma service_cost_invariant:
    forall t,
      (service sched j t) + (remaining_cost sched j t) = job_cost j.
  Proof. by move=> ?; rewrite subnKC// service_at_most_cost. Qed.

  (** We show that the service received by job [j] in any interval is no larger
     than its cost. *)
  Lemma cumulative_service_le_job_cost:
    forall t t',
      service_during sched j t t' <= job_cost j.
  Proof.
    move=> t t'.
    have [t'_le_t|t_lt_t'] := leqP t' t; first by rewrite service_during_geq.
    apply: leq_trans (service_at_most_cost t').
    by rewrite -(service_cat _ _ _ _ (ltnW t_lt_t')) leq_addl.
  Qed.

  (** If a job isn't complete at time [t], it can't be completed at time [t +
     remaining_cost j t - 1]. *)
  Lemma job_doesnt_complete_before_remaining_cost:
    forall t,
      ~~ completed_by sched j t ->
      ~~ completed_by sched j (t + remaining_cost sched j t - 1).
  Proof.
    move=> t; rewrite incomplete_is_positive_remaining_cost => rem_cost.
    rewrite -less_service_than_cost_is_incomplete -(service_cat sched j t);
      last by rewrite -addnBA//; exact: leq_addr.
    have: service sched j t + remaining_cost sched j t - 1 < job_cost j.
    { rewrite service_cost_invariant -subn_gt0 subKn//.
      exact/(leq_trans rem_cost)/leq_subr. }
    apply: leq_ltn_trans.
    by rewrite -!addnBA// leq_add2l cumulative_service_le_delta.
  Qed.

  Section GuaranteedService.

    (** Assume a scheduled job always receives some positive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** Assume that jobs are not released early. *)
    Context `{JobArrival Job}.
    Hypothesis H_jobs_must_arrive: jobs_must_arrive_to_execute sched.

    (** To simplify subsequent proofs, we restate the assumption
        [H_jobs_must_arrive] as a trivial corollary. *)
    Corollary has_arrived_scheduled :
      forall t,
        scheduled_at sched j t -> has_arrived j t.
    Proof. exact: H_jobs_must_arrive. Qed.

    (** We show that if job j is scheduled, then it must be pending. *)
    Lemma scheduled_implies_pending:
      forall t,
        scheduled_at sched j t ->
        pending sched j t.
    Proof.
      move=> t sch; apply/andP; split; first exact: has_arrived_scheduled.
      exact: scheduled_implies_not_completed.
    Qed.

  End GuaranteedService.

End ServiceAndCompletionFacts.

(** In this section, we establish facts about jobs with non-zero costs that must
    arrive to execute. *)
Section PositiveCost.

  (** Consider any type of jobs with cost and arrival-time attributes, ...*)
  Context {Job: JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** ...any kind of processor model,... *)
  Context {PState: ProcessorState Job}.

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
    move=> t comp.
    have: 0 < service sched j t by exact: leq_trans comp.
    exact: positive_service_implies_scheduled_since_arrival.
  Qed.

  (** We also prove that the job is pending at the moment of its arrival. *)
  Lemma job_pending_at_arrival:
    pending sched j (job_arrival j).
  Proof.
    apply/andP; split; first by rewrite /has_arrived.
    by rewrite /completed_by no_service_before_arrival// -ltnNge.
  Qed.

End PositiveCost.

Section CompletedJobs.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any schedule ... *)
  Variable sched : schedule PState.

  (** ... and suppose that jobs have a cost, an arrival time, and a notion of
     readiness. *)
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

  (** We observe that a given job is ready only if it is also incomplete ... *)
  Lemma ready_implies_incomplete:
    forall j t, job_ready sched j t -> ~~ completed_by sched j t.
  Proof. by move=> ? ? /any_ready_job_is_pending /andP[]. Qed.

  (** ... and lift this observation also to the level of whole schedules. *)
  Lemma completed_jobs_are_not_ready:
    jobs_must_be_ready_to_execute sched ->
    completed_jobs_dont_execute sched.
  Proof.
    move=> + j t sch => /(_ j t sch) ready.
    by rewrite less_service_than_cost_is_incomplete ready_implies_incomplete.
  Qed.

  (** Furthermore, in a valid schedule, completed jobs don't execute. *)
  Corollary valid_schedule_implies_completed_jobs_dont_execute:
    forall arr_seq, 
    valid_schedule sched arr_seq ->
    completed_jobs_dont_execute sched.
  Proof. move=> ? [? ?]; exact: completed_jobs_are_not_ready. Qed.

  (** We further observe that completed jobs don't execute if scheduled jobs
     always receive non-zero service and cumulative service never exceeds job
     costs. *)
  Lemma ideal_progress_completed_jobs:
    ideal_progress_proc_model PState ->
    (forall j t, service sched j t <= job_cost j) ->
    completed_jobs_dont_execute sched.
  Proof.
    move=> IDEAL SERVICE_BOUND j t SCHED.
    apply: leq_trans (SERVICE_BOUND j t.+1).
    by rewrite -service_last_plus_before -addn1 leq_add2l IDEAL.
  Qed.

End CompletedJobs.

(** We add the above lemma into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply it automatically. *)
Global Hint Resolve valid_schedule_implies_completed_jobs_dont_execute : basic_rt_facts.

(** Next, we relate the completion of jobs in schedules with identical prefixes. *)
Section CompletionInTwoSchedules.
  (** Consider any processor model and any type of jobs with costs, arrival times, and a notion of readiness. *)
  Context {Job: JobType} {PState: ProcessorState Job}.
  Context {jc : JobCost Job} {ja : JobArrival Job} {jr : JobReady Job PState}.

  (** If two schedules share a common prefix, then (in the prefix) jobs
      complete in one schedule iff they complete in the other. *)
  Lemma identical_prefix_completed_by:
    forall sched1 sched2 h,
      identical_prefix sched1 sched2 h ->
      forall j t,
        t <= h ->
        completed_by sched1 j t = completed_by sched2 j t.
  Proof.
    move=> sched1 sched2 h PREFIX j t LE_h.
    rewrite /completed_by (identical_prefix_service sched1 sched2)//.
    exact: identical_prefix_inclusion PREFIX.
  Qed.

  (** For convenience, we restate the previous lemma in terms of [pending]. *)
  Corollary identical_prefix_pending:
    forall sched1 sched2 h,
      identical_prefix sched1 sched2 h ->
      forall j t,
        t <= h ->
        pending sched1 j t = pending sched2 j t.
  Proof.
    move=> sched1 sched2 h PREFIX j t t_le_h.
    by rewrite /pending (identical_prefix_completed_by _ sched2 h).
  Qed.

End CompletionInTwoSchedules.
