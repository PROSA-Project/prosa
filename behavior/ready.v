Require Export prosa.behavior.execution.

(** * Readiness of a Job *)

(** We define a general notion of readiness of a job: a job can be
    scheduled only when it is ready, as determined by the predicate
    [job_ready]. This notion of readiness is a general concept that is
    used to model jitter, self-suspensions, etc. Crucially, we require
    that any sensible notion of readiness is a refinement of the notion
    of a pending job, i.e., any ready job must also be pending. *)
Class JobReady (Job : JobType) (PState : ProcessorState Job)
      {jc : JobCost Job} {ja : JobArrival Job} :=
  {
    job_ready : schedule PState -> Job -> instant -> bool;

    (** What follows is the consistency requirement: We require any
        reasonable readiness model to consider only pending jobs to be
        ready. *)
    _ : forall sched j t, job_ready sched j t -> pending sched j t;
  }.

(** * Backlogged Jobs *)

(** Based on the general notion of readiness, we define what it means to be
    backlogged, i.e., ready to run but not executing. *)
Section Backlogged.
  (** Consider any kinds of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Allow for any notion of readiness. *)
  Context {jc : JobCost Job} {ja : JobArrival Job} {jr : JobReady Job PState}.

  (** Job j is backlogged at time t iff it is ready and not scheduled. *)
  Definition backlogged (sched : schedule PState) (j : Job) (t : instant) :=
    job_ready sched j t && ~~ scheduled_at sched j t.

End Backlogged.


(** * Compliance with Job Readiness *)

(** With the readiness concept in place, we define whether a schedule respects it. *)
Section RespectsJobReadiness.
  (** Consider any kind of jobs with arrival times, and any kind of processor state. *)
  Context {Job : JobType} `{JobArrival Job} {PState : ProcessorState Job}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Furthermore, for jobs that have execution costs and a notion of
      readiness ... *)
  Context `{JobCost Job} `{!JobReady Job PState}.

  (** ... we define whether a job can only be scheduled if it is ready. *)
  Definition respects_job_readiness :=
    forall j t,
      scheduled_at sched j t ->
      job_ready sched j t.

End RespectsJobReadiness.
