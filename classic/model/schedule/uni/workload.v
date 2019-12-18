Require Import prosa.classic.util.all.
Require Import prosa.classic.model.time prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.priority.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Workload.

  Import Time ArrivalSequence Priority.

  (* In this section, we define the notion of workload for sets of jobs. *)  
  Section WorkloadDefs.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
      
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any (finite) set of jobs. *)
    Variable jobs: seq Job.

    (* First, we define the workload for generic sets of jobs. *)
    Section WorkloadOfJobs.

      (* Given any predicate over Jobs, ... *)
      Variable P: Job -> bool.

      (* ...we define the total workload of the jobs that satisfy such a predicate. *)
      Definition workload_of_jobs := \sum_(j <- jobs | P j) job_cost j.

    End WorkloadOfJobs.

    (* Then, we define the workload of tasks with higher or equal priority
       under FP policies. *)
    Section PerTaskPriority.

      (* Consider any FP policy that indicates whether a task has
         higher or equal priority. *)
      Variable higher_eq_priority: FP_policy Task.

      (* Let tsk be the task to be analyzed. *)
      Variable tsk: Task.

      (* Recall the notion of a job of higher or equal priority. *)
      Let of_higher_or_equal_priority j :=
        higher_eq_priority (job_task j) tsk.
      
      (* Then, we define the workload of all jobs of tasks with
         higher-or-equal priority than tsk. *)
      Definition workload_of_higher_or_equal_priority_tasks :=
        workload_of_jobs of_higher_or_equal_priority.

    End PerTaskPriority.

    (* Then, we define the workload of jobs with higher or equal priority
       under JLFP policies. *)
    Section PerJobPriority.

      (* Consider any JLFP policy that indicates whether a job has
         higher or equal priority. *)
      Variable higher_eq_priority: JLFP_policy Job.

      (* Let j be the job to be analyzed. *)
      Variable j: Job.

      (* Recall the notion of a job of higher or equal priority. *)
      Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
      
      (* Then, we define the workload of higher or equal priority of all jobs
         with higher-or-equal priority than j. *)
      Definition workload_of_higher_or_equal_priority_jobs :=
        workload_of_jobs of_higher_or_equal_priority.

    End PerJobPriority.
    
  End WorkloadDefs.
  
  (* We also define the workload of a task. *)
  Section TaskWorkload.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: Task.
    
    (* Recall the notion of a job of task tsk. *)
    Let of_task_tsk j := job_task j == tsk.
    
    (* We define the task workload as the workload of jobs of task tsk. *)
    Definition task_workload jobs := workload_of_jobs job_cost jobs of_task_tsk.

    (* Next, we recall the definition of the task workload in interval [t1, t2). *)
    Definition task_workload_between (t1 t2: time) :=
      task_workload (jobs_arrived_between arr_seq t1 t2).
    
  End TaskWorkload.  

  (* In this section, we prove a few basic lemmas about the workload. *)
  Section BasicLemmas.
   
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* For simplicity, let's define some local names. *)
    Let arrivals_between := jobs_arrived_between arr_seq.  
    
    (* We prove that workload can be splited into two parts. *)
    Lemma workload_of_jobs_cat:
      forall t t1 t2 P,
        t1 <= t <= t2 ->
        workload_of_jobs job_cost (arrivals_between t1 t2) P =
        workload_of_jobs job_cost (arrivals_between t1 t) P
        + workload_of_jobs job_cost (arrivals_between t t2) P.
    Proof.
      move => t t1 t2 P /andP [GE LE].
      rewrite /workload_of_jobs /arrivals_between.
        by rewrite (job_arrived_between_cat _ _ t) // big_cat.
    Qed.

  End BasicLemmas.
    
End Workload.