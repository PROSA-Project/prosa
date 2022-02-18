Require Export prosa.analysis.facts.behavior.completion.

(** * Deadlines *)

(** In this file, we observe basic properties of the behavioral job
    model w.r.t. deadlines. *)
Section DeadlineFacts.

  (** Consider any given type of jobs with costs and deadlines... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job}.

  (** ... any given type of processor states. *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** First, we derive two properties from the fact that a job is incomplete at
      some point in time. *)
  Section Incompletion.

    (** Consider any given schedule. *)
    Variable sched: schedule PState.

    (** Trivially, a job that both meets its deadline and is incomplete at a
        time [t] must have a deadline later than [t]. *)
    Lemma incomplete_implies_later_deadline:
      forall j t,
        job_meets_deadline sched j ->
        ~~ completed_by sched j t ->
        t < job_deadline j.
    Proof.
      move=> j t MET INCOMP.
      apply contraT; rewrite -leqNgt => PAST_DL.
      have DL_MISS: ~~ completed_by sched j (job_deadline j)
        by apply incompletion_monotonic with (t' := t) => //.
      by move: DL_MISS => /negP.
    Qed.

    (** Furthermore, a job that both meets its deadline and is incomplete at a
        time [t] must be scheduled at some point between [t] and its
        deadline. *)
    Lemma incomplete_implies_scheduled_later:
      forall j t,
        job_meets_deadline sched j ->
        ~~ completed_by sched j t ->
        exists t', t <= t' < job_deadline j /\ scheduled_at sched j t'.
    Proof.
      move=> j t MET INCOMP.
      apply: cumulative_service_implies_scheduled.
      rewrite -(ltn_add2l (service sched j t)) addn0.
      rewrite service_cat;
        last by (apply ltnW; apply incomplete_implies_later_deadline).
      apply leq_trans with (n := job_cost j);
        first by rewrite less_service_than_cost_is_incomplete.
      by apply MET.
    Qed.

  End Incompletion.

  (** Next, we look at schedules / processor models in which scheduled jobs
      always receive service. *)
  Section IdealProgressSchedules.

    (** Consider a given reference schedule... *)
    Variable sched: schedule PState.

    (** ...in which complete jobs don't execute... *)
    Hypothesis H_completed_jobs: completed_jobs_dont_execute sched.

    (** ...and scheduled jobs always receive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** We observe that if a job meets its deadline and is scheduled at time
        [t], then then its deadline is at a time later than t. *)
    Lemma scheduled_at_implies_later_deadline:
      forall j t,
        job_meets_deadline sched j ->
        scheduled_at sched j t ->
        t < job_deadline j.
    Proof.
      move=> j t MET SCHED_AT.
      apply (incomplete_implies_later_deadline sched) => //.
      by apply scheduled_implies_not_completed.
    Qed.

  End IdealProgressSchedules.

  (** In the following section, we observe that it is sufficient to
      establish that service is invariant across two schedules at a
      job's deadline to establish that it either meets its deadline in
      both schedules or none. *)
  Section EqualProgress.

    (** Consider any two schedules [sched] and [sched']. *)
    Variable sched sched': schedule PState.

    (** We observe that, if the service is invariant at the time of a
       job's absolute deadline, and if the job meets its deadline in one of the schedules, 
       then it meets its deadline also in the other schedule. *)
    Lemma service_invariant_implies_deadline_met:
      forall j,
        service sched j (job_deadline j) = service sched' j (job_deadline j) ->
        (job_meets_deadline sched j <-> job_meets_deadline sched' j).
    Proof.
      move=> j SERVICE.
      split;
        by rewrite /job_meets_deadline /completed_by -SERVICE.
    Qed.

  End EqualProgress.

End DeadlineFacts.
