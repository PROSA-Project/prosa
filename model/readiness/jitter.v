Require Export prosa.behavior.all.
Require Import prosa.util.nat.


(** * Job Model Parameter for Jobs Exhibiting Release Jitter *)

(** If a job exhibits release jitter, it is not immediately available for
    execution upon arrival, and can be scheduled only after its release, which
    occurs some (bounded) time after its arrival. We model this with the
    [job_jitter] parameter, which maps each job to its jitter duration. *)

Class JobJitter (Job : JobType) := { job_jitter : Job -> duration }.

(** * Readiness of Jobs with Release Jitter *)

(** Based on the job model's jitter parameter, we specify the readiness
   predicate for jobs with release jitter (and no self-suspensions). *)

Section ReadinessOfJitteryJobs.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Suppose jobs have an arrival time, a cost, and exhibit release jitter. *)
  Context `{JobArrival Job} `{JobCost Job} `{JobJitter Job}.

  (** We say that a job is released at a time [t] after its arrival if the
      job's release jitter has passed. *)
  Definition is_released (j : Job) (t : instant) := job_arrival j + job_jitter j <= t.

  (** A readiness model satisfies jitter readiness iff a job is ready exactly
      when it is released and not yet complete. *)
  Definition jitter_readiness (RM : JobReady Job PState) :=
    forall sched j t,
      job_ready sched j t = is_released j t && ~~ completed_by sched j t.

End ReadinessOfJitteryJobs.
