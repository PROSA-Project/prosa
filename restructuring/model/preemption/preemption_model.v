From rt.restructuring.behavior Require Import all.
From rt.restructuring.model Require Import job task.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
(** * Platform with limited preemptions *)
(** Since the notion of preemption points is based on an user-provided 
    predicate (variable job_can_be_preempted), it does not guarantee that 
    the scheduler will enforce correct behavior. For that, we must 
    define additional predicates. *)

(** Definition of a generic type of parameter relating jobs to their preemption points. *)
Class JobPreemptable (Job : JobType) := job_preemptable : Job -> duration -> bool.

Section ValidPreemptionModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume the existence of a function
     maping jobs to theirs preemption points ... *)
  Context `{JobPreemptable Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched: schedule PState.

  (** For simplicity, let's define some local names. *)
  Let job_pending := pending sched.
  Let job_completed_by := completed_by sched.
  Let job_scheduled_at := scheduled_at sched.

  (** We require that a job has to be executed at least one time instant
     in order to reach a nonpreemptive segment. In other words, a job 
     must start execution to become non-preemptive. *)
  Definition job_cannot_become_nonpreemptive_before_execution (j : Job) :=
    job_preemptable j 0.
    
  (** And vice versa, a job cannot remain non-preemptive after its completion. *)
  Definition job_cannot_be_nonpreemptive_after_completion (j : Job) := 
    job_preemptable j (job_cost j).
  
  (** Next, if a job j is not preemptive at some time instant t, 
     then j must be scheduled at time t. *)
  Definition not_preemptive_implies_scheduled (j : Job) :=
    forall t,
      ~~ job_preemptable j (service sched j t) ->
      job_scheduled_at j t. 

  (** A job can start its execution only from a preemption point. *)
  Definition execution_starts_with_preemption_point (j : Job) := 
    forall prt,
      ~~ job_scheduled_at j prt ->
      job_scheduled_at j prt.+1 ->
      job_preemptable j (service sched j prt.+1).

  (** We say that a preemption model is a valid preemption model if 
     all the assumptions given above are satisfied for any job. *)
  Definition valid_preemption_model :=
    forall j,
      arrives_in arr_seq j ->
      job_cannot_become_nonpreemptive_before_execution j
      /\ job_cannot_be_nonpreemptive_after_completion j
      /\ not_preemptive_implies_scheduled j
      /\ execution_starts_with_preemption_point j.
  
End ValidPreemptionModel.