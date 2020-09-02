Require Export prosa.model.task.arrival.periodic.
Require Export prosa.util.lcmseq.
From mathcomp Require Import div.

(** In this file we define the notion of a hyperperiod for periodic tasks. *)
Section Hyperperiod.

  (** Consider any type of periodic tasks ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... and any task set [ts]. *)
  Variable ts : TaskSet Task.

  (** The hyperperiod of a task set is defined as the least common multiple
      (LCM) of the periods of all tasks in the task set. **)
  Definition hyperperiod : duration := lcml (map task_period ts).        

End Hyperperiod.

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
      [corresponding_job_in_hyperperiod] which is the job that arrives in given hyperperiod 
      and has the same [job_index] as [j]. *)
  Definition corresponding_job_in_hyperperiod (j : Job) (h : instant) (tsk : Task) :=
    nth j (jobs_in_hyperperiod h tsk) (job_index_in_hyperperiod j (starting_instant_of_corresponding_hyperperiod j) tsk).

End HyperperiodDefinitions.
