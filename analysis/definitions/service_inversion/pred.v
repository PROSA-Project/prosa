Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.definitions.service.

(** * Service Inversion *)
(** In this section, we define the notion of service inversion for
    arbitrary processors. *)
Section ServiceInversion.

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

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume a given JLDP policy. *)
  Context `{JLDP_policy Job}.

  (** Consider an arbitrary predicate on time intervals. *)
  Variable P : Job -> instant -> instant -> Prop.

  (** Consider a job [j]. *)
  Variable j : Job.

  (** We say that the job incurs service inversion if it has higher
      priority than the job receiving service. Note that this
      definition is oblivious to whether job [j] is ready. Therefore,
      it may not apply as intuitively expected in models with jitter
      or self-suspensions. Further generalization of the concept is
      likely necessary to efficiently analyze models in which jobs may
      be pending without being ready. *)
  Definition service_inversion (t : instant) :=
    (j \notin served_jobs_at arr_seq sched t)
    && has (fun jlp => ~~ hep_job_at t jlp j) (served_jobs_at arr_seq sched t).

  (** Then we compute the cumulative service inversion incurred by a
      job within some time interval <<[t1, t2)>>. *)
  Definition cumulative_service_inversion (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) service_inversion t.

  (** For proof purposes, it is often useful to bound the cumulative
      service interference in a time interval <<[t1, t2)>> that
      satisfies a given predicate (e.g., <<[t1, t2)>> is a busy
      interval prefix). To this end, we say that the cumulative
      service inversion of job [j] is bounded by a function [B :
      duration -> duration] w.r.t. to predicate [P] iff, for any
      interval <<[t1, t2)>> that satisfies [P j], the cumulative
      priority inversion in <<[t1, t2)>> is bounded by [B (job_arrival
      j - t1)]. *)
  Definition pred_service_inversion_of_job_is_bounded_by (B : duration -> duration) :=
    forall (t1 t2 : instant),
      P j t1 t2 ->
      cumulative_service_inversion t1 t2 <= B (job_arrival j - t1).

End ServiceInversion.

(** In this section, we define a notion of the bounded service
    inversion for tasks. *)
Section TaskServiceInversionBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLDP policy. *)
  Context `{JLDP_policy Job}.

  (** Consider an arbitrary predicate on jobs and time intervals. *)
  Variable P : Job -> instant -> instant -> Prop.

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** We say that task [tsk] has bounded service inversion if all its
      jobs have cumulative service inversion bounded by function [B :
      duration -> duration]. *)
  Definition pred_service_inversion_is_bounded_by (B : duration -> duration) :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      pred_service_inversion_of_job_is_bounded_by arr_seq sched P j B.

End TaskServiceInversionBound.
