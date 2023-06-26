Require Export prosa.model.schedule.scheduled.
Require Export prosa.analysis.definitions.service.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.analysis.facts.behavior.arrivals.
Require Export prosa.util.tactics.

(** * Correctness of the Scheduled Job(s) *)

(** In this file, we establish the correctness of the computable definition of
    the (set of) scheduled job(s) and a useful case-analysis lemma. *)

Section ScheduledJobs.
  (**  Consider any type of jobs with arrival times. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any valid arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Now we establish the validity conditions under which these definitions
      yield the expected results: all jobs must come from the arrival sequence
      and do not execute before their arrival.

      NB: We do not use [valid_schedule] here to avoid introducing a dependency
      on a readiness mode. *)
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** ** The Set of Jobs Scheduled at a Given Time *)

  (** Under these assumptions, [scheduled_jobs_at] is correct: a job is included
      in the sequence if and only if it scheduled. *)
  Lemma scheduled_jobs_at_iff :
    forall j t,
      j \in scheduled_jobs_at arr_seq sched t = scheduled_at sched j t.
  Proof.
    move=> j t; rewrite mem_filter; apply: andb_idr => SCHED.
    exact: arrivals_before_scheduled_at.
  Qed.

  (** Conversely, if no jobs are in the sequence, then no job is scheduled. *)
  Lemma scheduled_jobs_at_nil :
    forall t,
      nilp (scheduled_jobs_at arr_seq sched t)
      <-> (forall j, ~~ scheduled_at sched j t).
  Proof.
    move=> t; split => [/nilP NIL j|NS]
    ; first by apply: contraT => /negbNE
               ; rewrite -scheduled_jobs_at_iff NIL in_nil.
    apply /nilP.
    case NN: (scheduled_jobs_at _) => [//|j js].
    exfalso.
    have: scheduled_at sched j t; last by move: (NS j) => /negP.
    rewrite -scheduled_jobs_at_iff NN.
    exact: mem_head.
  Qed.

  (** ** The Job Scheduled on an Ideal Progress Processor *)

  (** In this section, we prove a simple fact about the relation
      between [scheduled_at] and [served_at]. *)
  Section IdealProgress.

    (** Assume a scheduled job always receives some positive service. *)
    Hypothesis H_ideal_progress_model : ideal_progress_proc_model PState.

    (** We prove that if a job [j] is scheduled at time [t], then [j]
        is in the set of jobs that are served at time [t]. *)
    Lemma scheduled_at_implies_in_served_at :
      forall j t,
        scheduled_at sched j t ->
        j \in served_at arr_seq sched t.
    Proof.
      move=> j t SCHED.
      rewrite mem_filter; apply/andP; split.
      - by apply H_ideal_progress_model.
      - by eapply arrivals_before_scheduled_at => //.
    Qed.

  End IdealProgress.

  (** ** The Job Scheduled on a Uniprocessor *)

  (** For convenience, we note similar rewriting rules for uniprocessors. *)
  Section Uniprocessors.

    (** Suppose we are looking at a uniprocessor. *)
    Hypothesis H_uni : uniprocessor_model PState.

    (** Then clearly there is at most one job scheduled at any time [t]. *)
    Corollary scheduled_jobs_at_seq1 :
      forall t,
        size (scheduled_jobs_at arr_seq sched t) <= 1.
    Proof.
      move=> t; set sja := scheduled_jobs_at _ _ _; rewrite leqNgt.
      have uniq_sja : uniq sja by apply/filter_uniq/arrivals_uniq.
      apply/negP => /exists_two/(_ uniq_sja)[j1 [j2 [j1j2 [j1sja j2sja]]]].
      by apply/j1j2/(H_uni j1 j2 sched t); rewrite  -scheduled_jobs_at_iff.
    Qed.

    (** Then [scheduled_job_at t] is correct: it yields some job [j] if and only
        if [j] is scheduled at time [t]. *)
    Corollary scheduled_job_at_iff :
      forall j t,
        scheduled_job_at arr_seq sched t = Some j <-> scheduled_at sched j t.
    Proof.
      move=> j t; rewrite -scheduled_jobs_at_iff /scheduled_job_at.
      have := scheduled_jobs_at_seq1 t.
      case: scheduled_jobs_at => [//|j' [|//]] _ /=.
      by rewrite in_cons in_nil orbF; split => [[]->|/eqP ->].
    Qed.

    (** Conversely, if [scheduled_job_at t] returns [None], then no job is
        scheduled at time [t]. *)
    Corollary scheduled_job_at_none :
      forall t,
        scheduled_job_at arr_seq sched t = None
        <-> (forall j, ~~ scheduled_at sched j t).
    Proof.
      move=> t. rewrite /scheduled_job_at -scheduled_jobs_at_nil.
      by case: (scheduled_jobs_at arr_seq sched t).
    Qed.

    (** For convenience, we state a similar observation also for the [is_idle]
        wrapper, both for the idle case ... *)
    Corollary is_idle_iff :
      forall t,
        is_idle arr_seq sched t = (scheduled_job_at arr_seq sched t == None).
    Proof.
      move=> t; rewrite /is_idle/scheduled_job_at.
      by case: (scheduled_jobs_at _ _ _).
    Qed.

    (** ... and the non-idle case. *)
    Corollary is_nonidle_iff :
      forall t,
        ~~ is_idle arr_seq sched t <-> exists j, scheduled_at sched j t.
    Proof.
      move=> t. rewrite is_idle_iff.
      split => [|[j]]; last by rewrite -scheduled_job_at_iff => ->.
      case SJA: (scheduled_job_at _ _ _) => [j|//] _.
      by exists j; rewrite -scheduled_job_at_iff.
    Qed.

  End Uniprocessors.

  (** ** Case Analysis: a Scheduled Job Exists or no Job is Scheduled*)

  (** Last but not least, we note a case analysis that results from the above
      considerations: at any point in time, either some job is scheduled, or it
      holds that all jobs are not scheduled. *)
  Lemma scheduled_at_dec :
    forall t,
      {exists j, scheduled_at sched j t} + {forall j, ~~ scheduled_at sched j t}.
  Proof.
    move=> t.
    case SJA: (scheduled_jobs_at arr_seq sched t) => [|j js].
    - by right; rewrite -scheduled_jobs_at_nil SJA.
    - left; exists j.
      rewrite -scheduled_jobs_at_iff SJA.
      exact: mem_head.
  Qed.

End ScheduledJobs.
