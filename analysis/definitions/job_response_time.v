Require Export prosa.behavior.all.

(** In this section we define what it means for the response time 
    of a job to exceed some given duration. *)
Section JobResponseTimeExceeds.

  (** Consider any kind of jobs ... *)
  Context {Job : JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** ... and any kind of processor state. *)
  Context `{PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** We say that a job [j] has a response time exceeding a number [x] 
      if [j] is pending [x] units of time after its arrival. *)
  Definition job_response_time_exceeds (j : Job) (x : duration) :=
    ~~ completed_by sched j ((job_arrival j) + x).

End JobResponseTimeExceeds.
