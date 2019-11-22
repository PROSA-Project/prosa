Require Export rt.restructuring.model.priority.classes.
Require Export rt.restructuring.model.processor.ideal.
     
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** * Service Received by Sets of Jobs *)
(** In this file, we define the notion of service received by a set of jobs. *)
Section ServiceOfJobs.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *) 
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.
  
  (** First, we define the service received by a generic set of jobs. *)
  Section ServiceOfSetOfJobs.

    (** Let P be any predicate over jobs, ...*)
    Variable P : Job -> bool.
    
    (** ... and let jobs denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** Then we define the cumulative service received at 
       time t by the jobs that satisfy this predicate ... *)
    Definition service_of_jobs_at (t : instant) :=
      \sum_(j <- jobs | P j) service_at sched j t.
    
    (** ... and the cumulative service received during time 
       interval [t1, t2) by the jobs that satisfy the predicate. *)
    Definition service_of_jobs (t1 t2 : instant) :=
      \sum_(j <- jobs | P j) service_during sched j t1 t2.

  End ServiceOfSetOfJobs.
  
  (** Next, we define the service received by tasks with 
     higher-or-equal priority under a given FP policy. *)
  Section PerTaskPriority.

    (** Consider any FP policy. *)
    Variable higher_eq_priority : FP_policy Task.
    
    (** Let jobs denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** Let tsk be the task to be analyzed. *)
    Variable tsk : Task.

    (** Based on the definition of jobs of higher or equal priority (with respect to tsk), ... *)
    Let of_higher_or_equal_priority j := higher_eq_priority (job_task j) tsk.
    
    (** ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
    Definition service_of_higher_or_equal_priority_tasks (t1 t2 : instant) :=
      service_of_jobs of_higher_or_equal_priority jobs t1 t2.

  End PerTaskPriority.
  
  (** Next, we define the service received by jobs with 
     higher-or-equal  priority under JLFP policies. *)
  Section PerJobPriority.

    (** Consider any JLDP policy. *)
    Variable higher_eq_priority : JLFP_policy Job.
    
    (** Let jobs denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** Let j be the job to be analyzed. *)
    Variable j : Job.

    (** Based on the definition of jobs of higher or equal priority, ... *)
    Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
    
    (** ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
    Definition service_of_higher_or_equal_priority_jobs (t1 t2 : instant) :=
      service_of_jobs of_higher_or_equal_priority jobs t1 t2.

  End PerJobPriority.

  (** In this section, we define the notion of workload for sets of jobs. *)  
  Section ServiceOfTask.
    
    (** Let tsk be the task to be analyzed... *)
    Variable tsk : Task. 

    (** ... and let jobs denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** We define the cumulative task service received by 
       the jobs from the task within time interval [t1, t2). *)
    Definition task_service_of_jobs_in t1 t2 :=
      service_of_jobs (job_of_task tsk) jobs t1 t2.

  End ServiceOfTask.

End ServiceOfJobs.
