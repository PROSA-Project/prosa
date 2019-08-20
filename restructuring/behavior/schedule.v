From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
From rt.restructuring.behavior Require Export arrival_sequence.

(* We define the notion of a generic processor state. The processor state type
   determines aspects of the execution environment are modeled (e.g., overheads, spinning).
   In the most simple case (i.e., Ideal.processor_state), at any time,
   either a particular job is either scheduled or it is idle. *)
Class ProcessorState (Job : JobType) (State : Type) :=
  {
    (* For a given processor state, the [scheduled_in] predicate checks whether a given
       job is running in that state. *)
    scheduled_in: Job -> State -> bool;
    (* For a given processor state, the [service_in] function determines how much
       service a given job receives in that state. *)
    service_in: Job -> State -> nat;
    (* For a given processor state, a job does not receive service if it is not scheduled
       in that state *)
    service_implies_scheduled :
      forall j s, scheduled_in j s = false -> service_in j s = 0
  }.

(* A schedule maps an instant to a processor state *)
Definition schedule (PState : Type) := instant -> PState.

Section Schedule.
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  Variable sched : schedule PState.

  (* First, we define whether a job j is scheduled at time t, ... *)
  Definition scheduled_at (j : Job) (t : instant) := scheduled_in j (sched t).

  (* ... and the instantaneous service received by
           job j at time t. *)
  Definition service_at (j : Job) (t : instant) := service_in j (sched t).

  (* Based on the notion of instantaneous service, we define the
           cumulative service received by job j during any interval [t1, t2). *)
  Definition service_during (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) service_at j t.

  (* Using the previous definition, we define the cumulative service
           received by job j up to time t, i.e., during interval [0, t). *)
  Definition service (j : Job) (t : instant) := service_during j 0 t.

  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  Context `{JobArrival Job}.

  (* Next, we say that job j has completed by time t if it received enough
           service in the interval [0, t). *)
  Definition completed_by (j : Job) (t : instant) := service j t >= job_cost j.

  (* We say that job j completes at time t if it has completed by time t but
     not by time t - 1 *)
  Definition completes_at (j : Job) (t : instant) := ~~ completed_by j t.-1 && completed_by j t.

  (* We say that R is a response time bound of a job j if j has completed
     by R units after its arrival *)
  Definition job_response_time_bound (j : Job) (R : duration) :=
    completed_by j (job_arrival j + R).

  (* We say that a job meets its deadline if it completes by its absolute deadline *)
  Definition job_meets_deadline (j : Job) :=
    completed_by j (job_deadline j).

  (* Job j is pending at time t iff it has arrived but has not yet completed. *)
  Definition pending (j : Job) (t : instant) := has_arrived j t && ~~ completed_by j t.

  (* Job j is pending earlier and at time t iff it has arrived before time t
           and has not been completed yet. *)
  Definition pending_earlier_and_at (j : Job) (t : instant) :=
    arrived_before j t && ~~ completed_by j t.

  (* Let's define the remaining cost of job j as the amount of service
     that has to be received for its completion. *)
  Definition remaining_cost j t :=
    job_cost j - service j t.

End Schedule.

(* We next define a general notion of readiness of a job: a job can be
   scheduled only when it is ready. This notion of readiness is a general
   concept that is used to model jitter, self-suspensions, etc.  Crucially, we
   require that any sensible notion of readiness is a refinement of the notion
   of a pending job, i.e., any ready job must also be ready. *)
Class JobReady (Job : JobType) (PState : Type)
      `{ProcessorState Job PState} `{JobCost Job} `{JobArrival Job} :=
  {
    job_ready : schedule PState -> Job -> instant -> bool;
    any_ready_job_is_pending : forall sched j t, job_ready sched j t -> pending sched j t;
  }.

(* Based on the general notion of readiness, we define what it means to be
   backlogged, i.e., ready to run but not executing. *)
Section Backlogged.
  (* Conside any kinds of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (* Allow for any notion of readiness. *)
  Context `{JobReady Job PState}.

  (* Job j is backlogged at time t iff it is ready and not scheduled. *)
  Definition backlogged (sched : schedule PState) (j : Job) (t : instant) :=
    job_ready sched j t && ~~ scheduled_at sched j t.

End Backlogged.


(* In this section, we define valid schedules. *)
Section ValidSchedule.
  (* Consider any kinds of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (* Consider any schedule. *)
  Variable sched : schedule PState.

  Context `{JobArrival Job}.

  (* We define whether jobs come from some arrival sequence... *)
  Definition jobs_come_from_arrival_sequence (arr_seq : arrival_sequence Job) :=
    forall j t, scheduled_at sched j t -> arrives_in arr_seq j.

  (* ..., whether a job can only be scheduled if it has arrived ... *)
  Definition jobs_must_arrive_to_execute :=
    forall j t, scheduled_at sched j t -> has_arrived j t.

  Context `{JobCost Job}.
  Context `{JobReady Job PState}.

  (* ..., whether a job can only be scheduled if it is ready ... *)
  Definition jobs_must_be_ready_to_execute :=
    forall j t, scheduled_at sched j t -> job_ready sched j t.

  (* ... and whether a job cannot be scheduled after it completes. *)
  Definition completed_jobs_dont_execute :=
    forall j t, service sched j t <= job_cost j.

  (* We say that the schedule is valid iff
     - jobs come from some arrival sequence
     - a job is scheduled if it is ready *)
  Definition valid_schedule (arr_seq : arrival_sequence Job) :=
    jobs_come_from_arrival_sequence arr_seq /\
    jobs_must_be_ready_to_execute.

  (* Note that we do not explicitly require that a valid schedule satisfies
     jobs_must_arrive_to_execute or completed_jobs_dont_execute because these
     properties are implied by jobs_must_be_ready_to_execute. *)

End ValidSchedule.
