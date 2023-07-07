Require Export prosa.behavior.service.

(** * Service Definitions *)

(** In this section, we define a set of jobs that receive service at a
    given time. *)
Section ServedAt.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** The set of jobs served at time [t] can be obtained by filtering
      the set of all jobs that arrive at or before time [t]. *)
  Definition served_jobs_at (t : instant) :=
    [seq j <- arrivals_up_to arr_seq t | receives_service_at sched j t].

  (** For the special case of uniprocessors, we define a convenience
      wrapper that reduces the sequence of scheduled jobs to an
      [option Job]. *)
  Definition served_job_at t := ohead (served_jobs_at t).

End ServedAt.
