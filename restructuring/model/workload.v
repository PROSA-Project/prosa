From rt.restructuring.behavior Require Import schedule.
From rt.restructuring.model Require Import task schedule.priority_based.priorities.
From rt.restructuring.analysis Require Import basic_facts.arrivals.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** * Workload of Sets of Jobs *)
(** In this section, we define the notion of workload for sets of jobs. *)  
Section WorkloadOfJobs.

  (* Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (*  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (* Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (* First, we define the workload for generic sets of jobs. *)
  Section WorkloadOfJobs.
    
    (* Given any predicate over Jobs, ... *)
    Variable P : Job -> bool.

    (* ... and any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (* We define the total workload of the jobs that satisfy predicate P. *)
    Definition workload_of_jobs := \sum_(j <- jobs | P j) job_cost j.
    
  End WorkloadOfJobs.

  (* Next, we define the workload of tasks with higher or 
     equal priority under FP policies. *)
  Section PerTaskPriority.

    (* Consider any FP policy that indicates whether a task has
       higher or equal priority. *)
    Variable higher_eq_priority : FP_policy Task.

    (* Let tsk be the task to be analyzed. *)
    Variable tsk : Task.

    (* Recall the notion of a job of higher or equal priority. *)
    Let of_higher_or_equal_priority j :=
      higher_eq_priority (job_task j) tsk.
    
    (* Then, we define the workload of all jobs of tasks with
       higher-or-equal priority than tsk. *)
    Definition workload_of_higher_or_equal_priority_tasks :=
      workload_of_jobs of_higher_or_equal_priority.

  End PerTaskPriority.

  (* Then, we define the workload of jobs with higher or
     equal priority under JLFP policies. *)
  Section PerJobPriority.

    (* Consider any JLFP policy that indicates whether a job has
       higher or equal priority. *)
    Variable higher_eq_priority : JLFP_policy Job.

    (* Let j be the job to be analyzed. *)
    Variable j : Job.

    (* Recall the notion of a job of higher or equal priority. *)
    Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
    
    (* Then, we define the workload of higher or equal priority of all jobs
       with higher-or-equal priority than j. *)
    Definition workload_of_higher_or_equal_priority_jobs :=
      workload_of_jobs of_higher_or_equal_priority.

  End PerJobPriority.

  (* We also define workload of a task. *)
  Section TaskWorkload.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk : Task.
    
    (* We define the task workload as the workload of jobs of task tsk. *)
    Definition task_workload jobs := workload_of_jobs (job_of_task tsk) jobs.

    (* Next, we recall the definition of the task workload in interval [t1, t2). *)
    Definition task_workload_between (t1 t2 : instant) :=
      task_workload (arrivals_between arr_seq t1 t2).
    
  End TaskWorkload.  
  
End WorkloadOfJobs.