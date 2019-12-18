From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
Require Export prosa.behavior.all.

Require Import prosa.util.nat.


(** * Job Model Parameter for Jobs Exhibiting Release Jitter *)

(** If a job exhibits release jitter, it is not immediately available for
    execution upon arrival, and can be scheduled only after its release, which
    occurs some (bounded) time after its arrival. We model this with the
    [job_jitter] parameter, which maps each job to its jitter duration. *)

Class JobJitter (Job : JobType) := job_jitter : Job -> duration.

(** * Readiness of Jobs with Release Jitter *)

(** Based on the job model's jitter parameter, we define the readiness
   predicate for jogs with release jitter (and no self-suspensions). *)

Section ReadinessOfJitteryJobs.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Suppose jobs have an arrival time, a cost, and exhibit release jitter. *)
  Context `{JobArrival Job} `{JobCost Job} `{JobJitter Job}.

  (** We say that a job is released at a time [t] after its arrival if the
      job's release jitter has passed. *)
  Definition is_released (j : Job) (t : instant) := job_arrival j + job_jitter j <= t.

  (** Based on the predicate [is_released], it is easy to state the notion of
      readiness for jobs subject to release jitter: a job is ready only if it
      is released and not yet complete. *)
  Global Program Instance jitter_ready_instance : JobReady Job PState :=
    {
      job_ready sched j t := is_released j t && ~~ completed_by sched j t
    }.
  Next Obligation.
    move: H3 => /andP [REL UNFINISHED].
    rewrite /pending. apply /andP. split => //.
    move: REL. rewrite /is_released /has_arrived.
    by apply leq_addk.
  Defined.

End ReadinessOfJitteryJobs.
