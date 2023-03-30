Require Export prosa.behavior.all.
Require Export prosa.util.epsilon.

(** * The Scheduled Job(s) *)

(** In this file, we provide a computable definition of the (set of) scheduled
    job(s) at a given point in time. Importantly, the below definition is
    independent of the type of processor state. Consequently, it can be used for
    case analyses in generic analyses (e.g., something is scheduled or not,
    without making assumptions on the specific type of processor state). *)

Section ScheduledJobs.
  (**  Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... _any_ kind of processor, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** The set of jobs scheduled at time [t] can be obtained by filtering the set
      of all jobs that arrive at or before time [t]. *)
  Definition scheduled_jobs_at t :=
    [seq j <- arrivals_up_to arr_seq t | scheduled_at sched j t].

  (** For the special case of uniprocessors, we define a convenience wrapper
      that reduces the sequence of scheduled jobs to an [option Job]. *)
  Definition scheduled_job_at t := ohead (scheduled_jobs_at t).

  (** We also provide a convenience wrapper to express the absence of scheduled
      jobs. *)
  Definition is_idle t := scheduled_jobs_at t == [::].

End ScheduledJobs.
