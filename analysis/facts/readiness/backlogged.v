Require Export prosa.model.schedule.work_conserving.
Require Export prosa.analysis.facts.behavior.arrivals.
Require Export prosa.analysis.definitions.readiness.

(** In this file, we establish basic facts about backlogged jobs. *)

Section BackloggedJobs.

  (** Consider any kind of jobs with arrival times and costs... *)
  Context {Job : JobType} `{JobCost Job} `{JobArrival Job}.

  (** ... and any kind of processor model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... and allow for any notion of job readiness. *)
  Context {jr : JobReady Job PState}.

  (** Given an arrival sequence and a schedule ... *)
  Variable arr_seq : arrival_sequence Job.
  Variable sched : schedule PState.

  (** ... with consistent arrival times, ... *)
  Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

  (** ... we observe that any backlogged job is indeed in the set of backlogged
     jobs. *)
  Lemma mem_backlogged_jobs :
    forall j t,
      arrives_in arr_seq j ->
      backlogged sched j t ->
      j \in jobs_backlogged_at arr_seq sched t.
  Proof.
    move=> j t ARRIVES BACKLOGGED.
    rewrite /jobs_backlogged_at /arrivals_up_to.
    rewrite mem_filter.
    apply /andP; split; first by exact.
    apply arrived_between_implies_in_arrivals => //.
    rewrite /arrived_between.
    apply /andP; split => //.
    rewrite ltnS -/(has_arrived _ _).
    now apply (backlogged_implies_arrived sched).
  Qed.

  (** Trivially, it is also the case that any backlogged job comes from the
      respective arrival sequence. *)
  Lemma backlogged_job_arrives_in :
    forall j t,
      j \in jobs_backlogged_at arr_seq sched t ->
      arrives_in arr_seq j.
  Proof.
    move=> j t.
    rewrite  /jobs_backlogged_at mem_filter => /andP [_ IN].
    move: IN. rewrite /arrivals_up_to.
    now apply in_arrivals_implies_arrived.
  Qed.

End BackloggedJobs.

(** In the following section, we make one more crucial assumption: namely, that
    the readiness model is non-clairvoyant, which allows us to relate
    backlogged jobs in schedules with a shared prefix. *)
Section NonClairvoyance.

  (** Consider any kind of jobs with arrival times and costs... *)
  Context {Job : JobType} `{JobCost Job} `{JobArrival Job}.

  (** ... any kind of processor model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... and allow for any non-clairvoyant notion of job readiness. *)
  Context {RM : JobReady Job PState}.
  Hypothesis H_nonclairvoyant_job_readiness : nonclairvoyant_readiness RM.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (**  ... and two schedules  ... *)
  Variable sched sched' : schedule PState.

  (** ... with a shared prefix to a fixed horizon. *)
  Variable h : instant.
  Hypothesis H_shared_prefix : identical_prefix sched sched' h.

  (** We observe that a job is backlogged at a time in the prefix in one
      schedule iff it is backlogged in the other schedule due to the
      non-clairvoyance of the notion of job readiness ... *)
  Lemma backlogged_prefix_invariance :
    forall t j,
      t < h ->
      backlogged sched j t = backlogged sched' j t.
  Proof.
    move=> t j IN_PREFIX.
    rewrite /backlogged.
    rewrite (H_nonclairvoyant_job_readiness sched sched' j h) //.
    by rewrite /scheduled_at H_shared_prefix.
  Qed.

  (** As a corollary, if we further know that j is not scheduled at time [h],
      we can expand the previous lemma to [t <= h]. *)
  Corollary backlogged_prefix_invariance' :
    forall t j,
      ~~ scheduled_at sched  j t ->
      ~~ scheduled_at sched' j t ->
      t <= h ->
      backlogged sched j t = backlogged sched' j t.
  Proof.
    move=> t j NOT_SCHED NOT_SCHED'.
    rewrite leq_eqVlt => /orP [/eqP EQ | LT]; last by apply backlogged_prefix_invariance.
    rewrite /backlogged.
    rewrite (H_nonclairvoyant_job_readiness sched sched' j h) //;
            last by rewrite EQ.
    now rewrite NOT_SCHED NOT_SCHED'.
  Qed.

  (** ... and also lift this observation to the set of all backlogged jobs at
      any given time in the shared prefix. *)
  Lemma backlogged_jobs_prefix_invariance :
    forall t,
      t < h ->
      jobs_backlogged_at arr_seq sched t = jobs_backlogged_at arr_seq sched' t.
  Proof.
    move=> t IN_PREFIX.
    rewrite /jobs_backlogged_at.
    apply eq_filter.
    rewrite /eqfun => j.
    now apply backlogged_prefix_invariance.
  Qed.

End NonClairvoyance.
