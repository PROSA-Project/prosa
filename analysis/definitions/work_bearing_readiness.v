Require Export prosa.model.priority.classes.

(** * Work-Bearing Readiness *)

(** In this module, we introduce a property of readiness models that
    is called work-bearing readiness. Work-bearing readiness extracts
    the useful property of the classic readiness model stating that,
    if there is a job pending at a time instant [t], then there also
    exists a job that is ready at time [t]. In other words, we say
    that a readiness model is a work-bearing readiness model if, for
    any job [j] and any time instant [t], if job [j] is pending but
    not ready at [t], then there is a job with higher or equal
    priority [j_hp] that is both pending and ready at time [t]. *)

Section WorkBearingReadiness.

  (** Consider any type of job associated with any type of tasks ... *)
  Context {Job : JobType} {Task : TaskType} `{JobArrival Job} `{JobCost Job}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Further, allow for any notion of job readiness. *)
  Context {jr : JobReady Job PState}.

  (** Consider any job arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... any schedule of these jobs, ... *)
  Variable sched : schedule PState.

  (** ... and a JLFP policy that indicates a higher-or-equal priority relation. *)
  Context `{JLFP_policy Job}.

  (** If a job [j] is pending at a time instant [t], then (even if it
      is not ready at time [t]) there is a job [j_hp] with
      higher-or-equal priority that is ready at time instant [t]. *)
  Definition work_bearing_readiness :=
    forall (j : Job) (t : instant),
      arrives_in arr_seq j ->
      pending sched j t ->
      exists j_hp,
        arrives_in arr_seq j_hp /\
        job_ready sched j_hp t /\
        hep_job j_hp j.

End WorkBearingReadiness.
