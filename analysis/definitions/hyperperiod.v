Require Export prosa.model.task.arrival.periodic.
Require Export prosa.util.lcmseq.

(** In this file we define the notion of a hyperperiod for periodic tasks. *)
Section Hyperperiod.

  (** Consider any type of periodic tasks ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... and any task set [ts]. *)
  Variable ts : TaskSet Task.

  (** The hyperperiod of a task set is defined as the least common multiple
      (LCM) of the periods of all tasks in the task set. **)
  Definition hyperperiod : duration := lcml (map task_period ts).

  (** It is sometimes useful to count a task's releases per hyperperiod. *)
  Definition jobs_per_hyperperiod (tsk : Task) :=
    hyperperiod %/ task_period tsk.

End Hyperperiod.

(** We characterize the workload of a periodic task set independently of
    any particular arrival sequence or schedule. *)
Section HyperperiodWorkload.

  (** Consider periodic tasks with worst-case execution costs ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{TaskCost Task}.

  (** ... and the task set whose workload is to be analyzed. *)
  Variable ts : TaskSet Task.

  (** Hyperperiod workload lets us compare periodic execution demand with
      available service using integer arithmetic rather than utilization
      fractions. *)
  Definition hyperperiod_workload :=
    \sum_(tsk <- ts) jobs_per_hyperperiod ts tsk * task_cost tsk.

End HyperperiodWorkload.

(** In this section we provide basic definitions concerning the hyperperiod
    of all tasks in a task set. *)
Section HyperperiodDefinitions.

  (** Consider any type of periodic tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{PeriodicModel Task}.

  (** ... and any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any task set [ts] ... *)
  Variable ts : TaskSet Task.

  (** ... and any arrival sequence [arr_seq]. *)
  Variable arr_seq : arrival_sequence Job.

  (** Let [O_max] denote the maximum offset of all tasks in [ts] ... *)
  Let O_max := max_task_offset ts.

  (** ... and let [HP] denote the hyperperiod of all tasks in [ts]. *)
  Let HP := hyperperiod ts.

  (** We define a hyperperiod index based on an instant [t]
      which lies in it. *)
  (** Note that we consider the first hyperperiod to start at time [O_max],
      i.e., shifted by the maximum offset (and not at time zero as can also
      be found sometimes in the literature) *)
  Definition hyperperiod_index (t : instant) :=
    (t - O_max) %/ HP.

  (** Given an instant [t], we define the starting instant of the hyperperiod
      that contains [t]. *)
  Definition starting_instant_of_hyperperiod (t : instant) :=
    hyperperiod_index t * HP + O_max.

  (** Given a job [j], we define the starting instant of the hyperperiod
      in which [j] arrives. *)
  Definition starting_instant_of_corresponding_hyperperiod (j : Job) :=
    starting_instant_of_hyperperiod (job_arrival j).

  (** We define the sequence of jobs of a task [tsk] that arrive in a hyperperiod
      given the starting instant [h] of the hyperperiod. *)
  Definition jobs_in_hyperperiod (h : instant) (tsk : Task) :=
    task_arrivals_between arr_seq tsk h (h + HP).

  (** We define the index of a job [j] of task [tsk] in a hyperperiod starting at [h]. *)
  Definition job_index_in_hyperperiod (j : Job) (h : instant) (tsk : Task) :=
    index j (jobs_in_hyperperiod h tsk).

  (** Given a job [j] of task [tsk] and the hyperperiod starting at [h], we define a
      [corresponding_job_in_hyperperiod] which is the job that arrives in this hyperperiod
      and has the same [job_index] as [j]. *)
  Definition corresponding_job_in_hyperperiod (j : Job) (h : instant) (tsk : Task) :=
    nth j (jobs_in_hyperperiod h tsk) (job_index_in_hyperperiod j (starting_instant_of_corresponding_hyperperiod j) tsk).

End HyperperiodDefinitions.

(** ** Jobs in Adjacent Hyperperiods *)

(** These mappings let us compare successive repetitions of a task's
    release pattern, starting from any arriving job. *)
Section AdjacentHyperperiodJobs.

  (** Consider periodic tasks and their jobs. *)
  Context {Task : TaskType} `{PeriodicModel Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Consider a given task set ... *)
  Variable ts : TaskSet Task.

  (** ... and an arrival sequence of these tasks. *)
  Variable arr_seq : arrival_sequence Job.

  (** We define the "matching" occurrence of a job in the next hyperperiod ... *)
  Definition next_hyperperiod_job (j : Job) :=
    head j [seq j' <- arr_seq (job_arrival j + hyperperiod ts) | same_task j' j].

  (** ... and also in the previous hyperperiod (if any). *)
  Definition prev_hyperperiod_job (j : Job) :=
    head j [seq j' <- arr_seq (job_arrival j - hyperperiod ts) | same_task j' j].

End AdjacentHyperperiodJobs.
