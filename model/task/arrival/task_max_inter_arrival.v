Require Export prosa.model.task.concept.
Require Export prosa.model.task.arrivals.

(** * Task Max Inter-Arrival *)

(** We define a task-model parameter [task_max_inter_arrival_time] as
    the maximum time difference between the arrivals of consecutive jobs. *)
Class TaskMaxInterArrival (Task : TaskType) :=
  task_max_inter_arrival_time : Task -> duration.

(** In the following section, we define two properties that a task must satisfy 
for its maximum inter-arrival time to be valid. *)
Section ValidTaskMaxInterArrival.

  (** Consider any type of tasks, ... *)
  Context {Task : TaskType}.
  Context `{TaskMaxInterArrival Task}.

  (** ... any type of jobs associated with the tasks, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** ... and any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** Firstly, the task maximum inter-arrival time for a task is positive. *)
  Definition positive_task_max_inter_arrival_time (tsk : Task) :=
    task_max_inter_arrival_time tsk > 0. 

  (** Secondly, for any job [j] (with a positive [job_index]) of a task [tsk], 
      there exists a job [j'] of task [tsk] that arrives before [j] 
      with [j] not arriving any later than the task maximum inter-arrival 
      time of [tsk] after [j']. *)
  Definition arr_sep_task_max_inter_arrival (tsk : Task) :=
    forall (j : Job), 
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_index arr_seq j > 0 ->
      exists (j' : Job), 
        j <> j' /\
        arrives_in arr_seq j' /\
        job_task j' = tsk /\            
        job_arrival j' <= job_arrival j <= job_arrival j' + task_max_inter_arrival_time tsk.

  (** Finally, we say that the maximum inter-arrival time of a task [tsk] is 
      valid iff it satisfies the above two properties. *)
  Definition valid_task_max_inter_arrival_time (tsk : Task) :=
    positive_task_max_inter_arrival_time tsk /\
    arr_sep_task_max_inter_arrival tsk. 

  (** A task set is said to respect the task max inter-arrival model iff all tasks
   in the task set have valid task max inter-arrival times as defined above. *)
  Definition taskset_respects_task_max_inter_arrival_model (ts : TaskSet Task) := 
    forall tsk,
      tsk \in ts ->
      valid_task_max_inter_arrival_time tsk.

End ValidTaskMaxInterArrival.
