From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
Require Export prosa.behavior.service.

(** * Readiness of a Job *)

(** We define a general notion of readiness of a job: a job can be
   scheduled only when it is ready, as determined by the predicate
   [job_ready]. This notion of readiness is a general concept that is
   used to model jitter, self-suspensions, etc.  Crucially, we require
   that any sensible notion of readiness is a refinement of the notion
   of a pending job, i.e., any ready job must also be pending. *)
Class JobReady (Job : JobType) (PState : Type)
      `{ProcessorState Job PState} `{JobCost Job} `{JobArrival Job} :=
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
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Allow for any notion of readiness. *)
  Context `{JobReady Job PState}.

  (** Job j is backlogged at time t iff it is ready and not scheduled. *)
  Definition backlogged (sched : schedule PState) (j : Job) (t : instant) :=
    job_ready sched j t && ~~ scheduled_at sched j t.

End Backlogged.


(** * Validity of a Schedule *)

(** With the readiness concept in place, we define the notion of valid schedules. *)
Section ValidSchedule.
  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  Context `{JobArrival Job}.

  (** We define whether jobs come from some arrival sequence... *)
  Definition jobs_come_from_arrival_sequence (arr_seq : arrival_sequence Job) :=
    forall j t, scheduled_at sched j t -> arrives_in arr_seq j.

  (** ..., whether a job can only be scheduled if it has arrived ... *)
  Definition jobs_must_arrive_to_execute :=
    forall j t, scheduled_at sched j t -> has_arrived j t.

  Context `{JobCost Job}.
  Context `{JobReady Job PState}.

  (** ..., whether a job can only be scheduled if it is ready ... *)
  Definition jobs_must_be_ready_to_execute :=
    forall j t, scheduled_at sched j t -> job_ready sched j t.

  (** ... and whether a job cannot be scheduled after it completes. *)
  Definition completed_jobs_dont_execute :=
    forall j t, scheduled_at sched j t -> service sched j t < job_cost j.

  (** We say that the schedule is valid iff
     - jobs come from some arrival sequence
     - a job is scheduled if it is ready *)
  Definition valid_schedule (arr_seq : arrival_sequence Job) :=
    jobs_come_from_arrival_sequence arr_seq /\
    jobs_must_be_ready_to_execute.

  (** Note that we do not explicitly require that a valid schedule satisfies
     [jobs_must_arrive_to_execute] or [completed_jobs_dont_execute] because these
     properties are implied by jobs_must_be_ready_to_execute. *)

End ValidSchedule.
