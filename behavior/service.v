From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
Require Export prosa.behavior.schedule.

Section Service.

  (** * Service of a Job *)

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** First, we define whether a job [j] is scheduled at time [t], ... *)
  Definition scheduled_at (j : Job) (t : instant) := scheduled_in j (sched t).

  (** ... and the instantaneous service received by job j at time t. *)
  Definition service_at (j : Job) (t : instant) := service_in j (sched t).

  (** Based on the notion of instantaneous service, we define the cumulative
      service received by job j during any interval from [t1] until (but not
      including) [t2]. *)
  Definition service_during (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) service_at j t.

  (** Using the previous definition, we define the cumulative service received
      by job [j] up to (but not including) time [t]. *)
  Definition service (j : Job) (t : instant) := service_during j 0 t.

  (** * Job Completion and Response Time *)

  (** In the following, consider jobs that have a cost, a deadline, and an
      arbitrary arrival time. *)
  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  Context `{JobArrival Job}.

  (** We say that job [j] has completed by time [t] if it received all required
      service in the interval from [0] until (but not including) [t]. *)
  Definition completed_by (j : Job) (t : instant) := service j t >= job_cost j.

  (** We say that job [j] completes at time [t] if it has completed by time [t] but
      not by time [t - 1]. *)
  Definition completes_at (j : Job) (t : instant) := ~~ completed_by j t.-1 && completed_by j t.

  (** We say that a constant [R] is a response time bound of a job [j] if [j]
      has completed by [R] units after its arrival. *)
  Definition job_response_time_bound (j : Job) (R : duration) :=
    completed_by j (job_arrival j + R).

  (** We say that a job meets its deadline if it completes by its absolute deadline. *)
  Definition job_meets_deadline (j : Job) :=
    completed_by j (job_deadline j).

  (** * Pending or Incomplete Jobs *)

  (** Job [j] is pending at time [t] iff it has arrived but has not yet completed. *)
  Definition pending (j : Job) (t : instant) := has_arrived j t && ~~ completed_by j t.

  (** Job [j] is pending earlier and at time [t] iff it has arrived before time [t]
      and has not been completed yet. *)
  Definition pending_earlier_and_at (j : Job) (t : instant) :=
    arrived_before j t && ~~ completed_by j t.

  (** Let's define the remaining cost of job [j] as the amount of service that
      has yet to be received for it to complete. *)
  Definition remaining_cost j t :=
    job_cost j - service j t.

End Service.
