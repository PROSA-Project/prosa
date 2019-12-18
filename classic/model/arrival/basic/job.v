Require Import prosa.classic.model.time prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssrnat ssrbool eqtype.  
  
(* Properties of different types of job: *)
Module Job.

  Import Time ArrivalSequence.
  
  (* 1) Basic Job *)
  Section ValidJob.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    Variable j: Job.

    (* The job cost must be positive. *)
    Definition job_cost_positive := job_cost j > 0.

  End ValidJob.

  (* 2) Real-time job (with a deadline) *)
  Section ValidRealtimeJob.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    
    Variable j: Job.

    (* The job deadline must be positive and no less than its cost. *)
    Definition job_deadline_positive := job_deadline j > 0.
    Definition job_cost_le_deadline := job_cost j <= job_deadline j.
        
    Definition valid_realtime_job :=
      job_cost_positive job_cost j /\
      job_cost_le_deadline /\
      job_deadline_positive.

  End ValidRealtimeJob.
  
  (* 3) Job of sporadic task *)
  Section ValidSporadicTaskJob.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    Variable j: Job.

    (* The job cost cannot be larger than the task cost. *)
    Definition job_cost_le_task_cost :=
      job_cost j <= task_cost (job_task j).

    (* The job deadline must be equal to the task deadline. *)
    Definition job_deadline_eq_task_deadline :=
      job_deadline j = task_deadline (job_task j).

    Definition valid_sporadic_job :=
      valid_realtime_job job_cost job_deadline j /\
      job_cost_le_task_cost /\
      job_deadline_eq_task_deadline.

  End ValidSporadicTaskJob.

  (* 4) Job of task *)
  Section ValidTaskJob.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time. 
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    
    (* The job cost from the arrival sequence 
       cannot be larger than the task cost. *)
    Definition cost_of_jobs_from_arrival_sequence_le_task_cost :=
      forall j,
        arrives_in arr_seq j ->
        job_cost_le_task_cost task_cost job_cost job_task j.

  End ValidTaskJob.

End Job.
