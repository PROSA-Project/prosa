Require Import rt.model.time rt.model.arrival.basic.task.
From mathcomp Require Import ssrnat ssrbool eqtype.  

Require Export rt.model.arrival.basic.job.

(* Properties of different types of job: *)
Module JobWithJitter.

  Import Time.
  Export Job.
  
  (* 4) Job of sporadic task with jitter *)
  Section ValidSporadicTaskJobWithJitter.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    Variable task_jitter: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> time.
    
    Variable j: Job.

    (* The job jitter cannot be larger than the task (maximum) jitter.*)
    Definition job_jitter_leq_task_jitter :=
      job_jitter j <= task_jitter (job_task j).

    Let j_is_valid_job :=
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    Definition valid_sporadic_job_with_jitter :=
      j_is_valid_job /\ job_jitter_leq_task_jitter.

  End ValidSporadicTaskJobWithJitter.

End JobWithJitter.