Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq bigop.

Module Suspension.

  Import ArrivalSequence.

  (* First, we define the actual job suspension times. *)
  Section SuspensionTimes.

    (* Consider any type of job. *)
    Variable Job: eqType.

    (* We define job suspension as a function that takes a job in the arrival
       sequence and its current service and returns how long the job must
       suspend next. *)
    Definition job_suspension := Job ->    (* job *)
                                 time ->   (* current service *)
                                 duration. (* duration of next suspension *)

  End SuspensionTimes.

  (* Next, we define the total suspension time incurred by a job. *)
  Section TotalSuspensionTime.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    
    (* Consider any job suspension function. *)
    Variable next_suspension: job_suspension Job.
      
    (* Let j be any job. *)
    Variable j: Job.

    (* We define the total suspension time incurred by job j as the cumulative
       duration of each suspension point t in the interval [0, job_cost j). *)
    Definition total_suspension :=
      \sum_(0 <= t < job_cost j) (next_suspension j t).

  End TotalSuspensionTime.
    
  (* In this section, we define the dynamic self-suspension model as an
     upper bound on the total suspension times. *)
  Section DynamicSuspensions.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence subject to job suspensions. *)
    Variable next_suspension: job_suspension Job.

    (* Recall the definition of total suspension time. *)
    Let total_job_suspension := total_suspension job_cost next_suspension.
    
    (* Next, assume that for each task a suspension bound is known. *)
    Variable suspension_bound: Task -> duration.

    (* Then, we say that the arrival sequence satisfies the dynamic
       suspension model iff the total suspension time of each job is no
       larger than the suspension bound of its task. *)
    Definition dynamic_suspension_model :=
      forall j, total_job_suspension j <= suspension_bound (job_task j).

  End DynamicSuspensions.

End Suspension.