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

  (** We begin with schedules / processor models in which scheduled jobs
    always receive service. *)
  Section IdealProgressSchedules.

    (** Consider a given reference schedule... *)
    Variable sched: schedule PState.

    (** ...in which complete jobs don't execute... *)
    Hypothesis H_completed_jobs: completed_jobs_dont_execute sched.

    (** ...and scheduled jobs always receive service. *)
    Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

    (** We observe that, if a job is known to meet its deadline, then
       its deadline must be later than any point at which it is
       scheduled. That is, if a job that meets its deadline is
       scheduled at time t, we may conclude that its deadline is at a
       time later than t. *)
    Lemma scheduled_at_implies_later_deadline:
      forall j t,
        job_meets_deadline sched j ->
        scheduled_at sched j t ->
        t < job_deadline j.
    Proof.
      move=> j t.
      rewrite /job_meets_deadline => COMP SCHED.
      case: (boolP (t < job_deadline j)) => //.
      rewrite -leqNgt => AFTER_DL.
      apply completion_monotonic with (t' := t) in COMP => //.
      apply scheduled_implies_not_completed in SCHED => //.
      move/negP in SCHED. contradiction.
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
