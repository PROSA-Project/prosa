Require Export prosa.model.priority.classes.

(** * Cumulative Workload of Sets of Jobs *)

(** In this module, we define the notion of the cumulative workload of
    a set of jobs. *)  
Section WorkloadOfJobs.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs with execution costs that are
      associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** First, we define the workload for generic sets of jobs. *)
  Section WorkloadOfJobs.
    
    (** Given any computable predicate on jobs, ... *)
    Variable P : pred Job.

    (** ... and any (finite) set of jobs, ... *)
    Variable jobs : seq Job.

    (** ... we define the total workload of the jobs that satisfy
        predicate [P]. *)
    Definition workload_of_jobs := \sum_(j <- jobs | P j) job_cost j.
    
  End WorkloadOfJobs.

  (** Next, we define the workload of jobs with higher or
      equal priority under JLFP policies. *)
  Section PerJobPriority.

    (** Consider any JLFP policy that indicates whether a job has
        higher or equal priority. *)
    Context `{JLFP_policy Job}.

    (** Let j be the job to be analyzed. *)
    Variable j : Job.

    (** Recall the notion of a job of higher or equal priority. *)
    Let of_higher_or_equal_priority j_hp := hep_job j_hp j.

    (** Then, we define the workload of higher or equal priority of all jobs
        with higher-or-equal priority than j. *)
    Definition workload_of_higher_or_equal_priority_jobs jobs :=
      workload_of_jobs of_higher_or_equal_priority jobs.

    (** We extend the prior notion to define the workload all jobs
        with higher-or-equal priority than [j] in a given interval. *)
    Definition workload_of_hep_jobs (j : Job) (t1 t2 : instant) :=
      workload_of_jobs
        (fun jhp => hep_job jhp j)
        (arrivals_between arr_seq t1 t2).

    (** We define a similar _non-reflexive_ notion of higher-or-equal
        priority workload in an interval. *)
    Definition workload_of_other_hep_jobs (j : Job) (t1 t2 : instant) :=
      workload_of_jobs
        (fun jhp => another_hep_job jhp j)
        (arrivals_between arr_seq t1 t2).

    (** For analysis purposes, we define the workload of a given job. *)
    Definition workload_of_job (j : Job) (t1 t2 : instant) :=
      workload_of_jobs (xpred1 j) (arrivals_between arr_seq t1 t2).

  End PerJobPriority.

  (** We also define workload of a task. *)
  Section TaskWorkload.

    (** Let [tsk] be the task to be analyzed. *)
    Variable tsk : Task.

    (** We define the task workload as the workload of jobs of task
        [tsk]. *)
    Definition task_workload jobs := workload_of_jobs (job_of_task tsk) jobs.

    (** Finally, we define the task's workload in a given interval [[t1,
        t2)]. *)
    Definition task_workload_between (t1 t2 : instant) :=
      task_workload (arrivals_between arr_seq t1 t2).

  End TaskWorkload.

End WorkloadOfJobs.
