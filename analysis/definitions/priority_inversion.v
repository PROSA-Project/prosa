Require Export prosa.analysis.definitions.busy_interval.classical.
Require Export prosa.analysis.facts.model.scheduled.

(** * Priority Inversion *)
(** In this section, we define the notion of priority inversion for
    arbitrary processors. *)
Section PriorityInversion.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider an arbitrary job. *)
  Variable j : Job.

  (** We say that job [j] incurs _priority inversion_ at a given time [t]
      if it is not scheduled at time [t] and has higher priority than a
      scheduled job. Note that this definition is oblivious to whether
      job [j] is ready. Therefore, additional consideration must be given
      in models with jitter or self-suspensions.

      For generality, we restrict the definition here to priority
      inversion due to jobs satisfying a given predicate [P] and derive
      the more common classical definitions (that apply to all jobs) as
      special cases below. *)
  Definition priority_inversion_cond (P : pred Job) (t : instant) :=
    (j \notin scheduled_jobs_at arr_seq sched t)
    && has (fun jlp => P jlp && ~~ hep_job jlp j) (scheduled_jobs_at arr_seq sched t).

  (** Cumulative priority inversion (w.r.t. condition [P]) within some
      time interval <<[t1, t2)>> is the total number of time points
      within <<[t1, t2)>> at which job [j] incurred priority inversion
      (due to jobs satisfying [P]). *)
  Definition cumulative_priority_inversion_cond (P : pred Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) priority_inversion_cond P t.

  (** Suppose the priority inversion (w.r.t. condition [P]) experienced
      by job [j] depends on its relative arrival time w.r.t. the
      beginning of its busy interval at a time [t1]. We say that the
      priority inversion of job [j] is bounded by a function
      [B : duration -> duration] if the cumulative priority inversion
      (due to jobs satisfying [P]) within any busy interval prefix is
      bounded by [B (job_arrival j - t1)]. *)
  Definition priority_inversion_of_job_cond_is_bounded_by (P : pred Job) (B : duration -> duration) :=
    forall (t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      cumulative_priority_inversion_cond P t1 t2 <= B (job_arrival j - t1).

  (** We obtain the corresponding classical notions for all jobs by
      choosing [predT] as the predicate [P]: priority inversion, ... *)
  Definition priority_inversion (t : instant) :=
    priority_inversion_cond predT t.

  (** ... cumulative priority inversion, ... *)
  Definition cumulative_priority_inversion (t1 t2 : instant) :=
    cumulative_priority_inversion_cond predT t1 t2.

  (** ... and bounded priority inversion. *)
  Definition priority_inversion_of_job_is_bounded_by (B : duration -> duration) :=
    priority_inversion_of_job_cond_is_bounded_by predT B.

End PriorityInversion.

(** In this section, we define a notion of the bounded priority inversion
    for tasks. *)
Section TaskPriorityInversionBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** We say that task [tsk] has bounded priority inversion from jobs
      satisfying a predicate [P] if all its jobs have bounded cumulative
      priority inversion due to such jobs. The bound depends on each
      job's relative arrival time w.r.t. the beginning of its busy
      interval. *)
  Definition priority_inversion_cond_is_bounded_by (P : pred Job) (B : duration -> duration) :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      priority_inversion_of_job_cond_is_bounded_by arr_seq sched j P B.

  (** Choosing [predT] gives a bound on total priority inversion. *)
  Definition priority_inversion_is_bounded_by (B : duration -> duration) :=
    priority_inversion_cond_is_bounded_by predT B.

End TaskPriorityInversionBound.
