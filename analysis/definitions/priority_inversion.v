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

  (** We say that the job incurs priority inversion if it has higher
      priority than the scheduled job. Note that this definition is
      oblivious to whether job [j] is ready. Therefore, it may not
      apply as intuitively expected in models with jitter or
      self-suspensions. Further generalization of the concept is
      likely necessary to efficiently analyze models in which jobs may
      be pending without being ready. *)
  Definition priority_inversion (t : instant) :=
    (j \notin scheduled_jobs_at arr_seq sched t)
    && has (fun jlp => ~~ hep_job jlp j) (scheduled_jobs_at arr_seq sched t).

  (** Similarly we define priority inversion occurring only due to jobs
      satisfying the predicate [P]. In other words, the lower-priority job
      scheduled instead of [j] satisfies the predicate [P]. *)
  Definition priority_inversion_cond (P : pred Job) (t : instant) :=
    (j \notin scheduled_jobs_at arr_seq sched t)
    && has (fun jlp => ~~ hep_job jlp j && P jlp) (scheduled_jobs_at arr_seq sched t).

  (** Cumulative priority inversion incurred by a job within some time
      interval <<[t1, t2)>> is the total number of time instances
      within <<[t1,t2)>> at which job [j] incurred priority
      inversion. *)
  Definition cumulative_priority_inversion (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) priority_inversion t.

  (** Cumulative priority inversion incurred by a job from jobs satisfying
      a predefined condition [P] within some time interval <<[t1, t2)>>
      is the total number of time instances within <<[t1, t2)>>
      at which job [j] incurred priority inversion due to jobs satisfying [P]. *)
  Definition cumulative_priority_inversion_cond (P : pred Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) priority_inversion_cond P t.

  (** Suppose the priority inversion experienced by job [j] depends on
      its relative arrival time w.r.t. the beginning of its busy
      interval at a time [t1]. We say that the priority inversion of
      job [j] is bounded by a function [B : duration -> duration] if
      the cumulative priority inversion within any busy interval
      prefix is bounded by [B (job_arrival j - t1)]. *)
  Definition priority_inversion_of_job_is_bounded_by (B : duration -> duration) :=
    forall (t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      cumulative_priority_inversion t1 t2 <= B (job_arrival j - t1).

  (** We define a similar notion as defined above for the priority
      inversion that is experienced by a job due to jobs satisfying
      the predicate [P]. *)
  Definition priority_inversion_of_job_cond_is_bounded_by (P : pred Job) (B : duration -> duration) :=
    forall (t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      cumulative_priority_inversion_cond P t1 t2 <= B (job_arrival j - t1).

End PriorityInversion.

(** In this section, we define a notion of the bounded priority inversion for tasks. *)
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

  (** We say that task [tsk] has bounded priority inversion if all its
      jobs have bounded cumulative priority inversion that depends on
      its relative arrival time w.r.t. the beginning of the busy
      interval. *)
  Definition priority_inversion_is_bounded_by (B : duration -> duration) :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      priority_inversion_of_job_is_bounded_by arr_seq sched j B.

  (** Analogous to the above definition, we say that task [tsk] has bounded
      priority inversion from jobs satisfying a predicate [P] if all its
      jobs have bounded cumulative priority inversion that depends on its
      relative arrival time w.r.t. the beginning of the busy interval. *)
  Definition priority_inversion_cond_is_bounded_by (P: pred Job) (B : duration -> duration) :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      priority_inversion_of_job_cond_is_bounded_by arr_seq sched j P B.

End TaskPriorityInversionBound.
