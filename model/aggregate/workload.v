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

  (** We define the workload of jobs that satisfy a predicate. *)
  Definition workload_of_jobs (P : pred Job) (jobs : seq Job) :=
    \sum_(j <- jobs | P j) job_cost j.

  (** We define the task workload as the workload of jobs of task [tsk]. *)
  Definition task_workload (tsk : Task) (jobs : seq Job) :=
    workload_of_jobs (job_of_task tsk) jobs.

  (** Now consider an arbitrary job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We define a task's workload in a given interval <<[t1, t2)>>. *)
  Definition task_workload_between (tsk : Task) (t1 t2 : instant) :=
    task_workload tsk (arrivals_between arr_seq t1 t2).

  (** Further, we define (trivially) the workload of a given job. While this
      definition may appear of little use, it is in fact useful for certain
      rewriting steps. *)
  Definition workload_of_job (j : Job) (t1 t2 : instant) :=
    workload_of_jobs (xpred1 j) (arrivals_between arr_seq t1 t2).

  (** In this section, we add definitions for total workload. *)
  Section TotalWorkload.

    (** We define the total workload as the sum of workloads of all incoming jobs. *)
    Definition total_workload (jobs : seq Job) := workload_of_jobs predT jobs.

    (** We also define the total workload in a given interval <<[t1, t2)>>. *)
    Definition total_workload_between (t1 t2 : instant) :=
      total_workload (arrivals_between arr_seq t1 t2).

  End TotalWorkload.

  (** Next, we define the workload of jobs with higher or
      equal priority under JLFP policies. *)
  Section PerJobPriority.

    (** Consider any JLFP policy that indicates whether a job has
        higher or equal priority. *)
    Context `{JLFP_policy Job}.

    (** We extend the prior notion to define the workload all jobs
        with higher-or-equal priority than [j] in a given interval. *)
    Definition workload_of_hep_jobs (j : Job) (t1 t2 : instant) :=
      let is_hep j' := hep_job j' j in
        workload_of_jobs is_hep (arrivals_between arr_seq t1 t2).

    (** We define a similar _non-reflexive_ notion of higher-or-equal
        priority workload in an interval. *)
    Definition workload_of_other_hep_jobs (j : Job) (t1 t2 : instant) :=
      let is_ahep j' := another_hep_job j' j in
        workload_of_jobs is_ahep (arrivals_between arr_seq t1 t2).

  End PerJobPriority.

End WorkloadOfJobs.
