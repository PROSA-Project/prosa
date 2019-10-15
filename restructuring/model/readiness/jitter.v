From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
From rt.restructuring.behavior Require Export schedule.

From rt.util Require Import nat.

(* We define the readiness indicator function for models with release jitter
   (and no self-suspensions). *)

(* Definition of a generic type of release jitter parameter. *)
Class JobJitter (Job : JobType) := job_jitter : Job -> duration.

Section ReadinessOfJitteryJobs.
  (* Consider any kind of jobs... *)
  Context {Job : JobType}.

  (* ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (* Supose jobs have an arrival time, a cost, and a release jitter bound. *)
  Context `{JobArrival Job} `{JobCost Job} `{JobJitter Job}.

  (* We say that a job is released at a time after its arrival if the job's
     release jitter has passed. *)
  Definition is_released (j : Job) (t : instant) := job_arrival j + job_jitter j <= t.

  (* A job that experiences jitter is ready only when the jitter-induced delay
     has passed after its arrival and if it is not yet complete. *)
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
