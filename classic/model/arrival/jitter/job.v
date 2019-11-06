Require Import rt.model.time rt.model.arrival.basic.task.
From mathcomp Require Import ssrnat ssrbool eqtype.  

Require Export rt.model.arrival.basic.job.

(* In this file, we define properties of jobs with jitter. *)
Module JobWithJitter.

  Import Time.
  Export Job.
  
  Section ValidSporadicTaskJobWithJitter.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    Variable task_jitter: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Let j be any job. *)
    Variable j: Job.

    (* First, we define whether the actual jitter of the job is no larger
       than the jitter of its task. *)
    Definition job_jitter_leq_task_jitter :=
      job_jitter j <= task_jitter (job_task j).

    (* Then, based on the definition of valid sporadic job, ...*)
    Let j_is_valid_job :=
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* ...we define a valid sporadic job with jitter. *)
    Definition valid_sporadic_job_with_jitter :=
      j_is_valid_job /\ job_jitter_leq_task_jitter.

  End ValidSporadicTaskJobWithJitter.

End JobWithJitter.