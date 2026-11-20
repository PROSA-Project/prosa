Require Export prosa.behavior.service.

(** * Validity of Schedules of Arriving Jobs *)

(** In the following, we define some basic validity conditions for schedules. *)
Section ValidScheduleOfArrivals.

  (** Consider jobs with arrival times and any processor model. *)
  Context {Job : JobType} `{JobArrival Job} {PState : ProcessorState Job}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Scheduled jobs must belong to the given arrival sequence. *)
  Definition jobs_come_from_arrival_sequence (arr_seq : arrival_sequence Job) :=
    forall j t,
      scheduled_at sched j t ->
      arrives_in arr_seq j.

  (** Jobs can execute only after they have arrived. *)
  Definition jobs_must_arrive_to_execute :=
    forall j t,
      scheduled_at sched j t ->
      has_arrived j t.

  (** Further, suppose jobs have execution costs. *)
  Context `{JobCost Job}.

  (** Completed jobs cannot execute. *)
  Definition completed_jobs_dont_execute :=
    forall j t,
      scheduled_at sched j t ->
      service sched j t < job_cost j.

  (** We combine the above three properties into one composite validity constraint. *)
  Definition valid_schedule_of_arrivals (arr_seq : arrival_sequence Job) :=
    jobs_come_from_arrival_sequence arr_seq
    /\ jobs_must_arrive_to_execute
    /\ completed_jobs_dont_execute.

End ValidScheduleOfArrivals.
