Require Export prosa.model.task.arrivals.

(** In this section we define the notion of an infinite release
    of jobs by a task. *)
Section InfiniteJobs.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that a task [tsk] releases an infinite number of jobs
      if for every integer [n] there exists a job [j] of task [tsk]
      such that [job_index] of [j] is equal to [n]. *)
  Definition infinite_jobs :=
    forall tsk n, exists j,
      arrives_in arr_seq j /\
      job_task j = tsk /\
      job_index arr_seq j = n.

End InfiniteJobs.
