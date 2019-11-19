Require Export rt.restructuring.behavior.all.
Require Export rt.restructuring.model.task.

Section TaskMinInterArrivalTime.
  Context {Task : TaskType}.

  Variable (task_min_inter_arrival_time : duration).

  Definition valid_task_min_inter_arrival_time :=
    task_min_inter_arrival_time > 0.

  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  Variable arr_seq : arrival_sequence Job.

  Definition respects_sporadic_task_model (tsk : Task) (d : duration) :=
    forall (j j': Job),
      j <> j' -> (** Given two different jobs j and j' ... *)
      arrives_in arr_seq j -> (** ...that belong to the arrival sequence... *)
      arrives_in arr_seq j' ->
      job_task j = tsk ->
      job_task j' = tsk -> (** ... and that are spawned by the same task, ... *)
      job_arrival j <= job_arrival j' -> (** ... if the arrival of j precedes the arrival of j' ...,  *)
      (** then the arrival of j and the arrival of j' are separated by at least one period. *)
      job_arrival j' >= job_arrival j + d.

End TaskMinInterArrivalTime.

(** Definition of a generic type of parameter for task
   minimum inter arrival times *)

Class SporadicModel (Task : TaskType) :=
  task_min_inter_arrival_time : Task -> duration.

Section SporadicModel.
  Context {Task : TaskType} `{SporadicModel Task}.

  Variable ts : seq Task.

  Definition valid_taskset_min_inter_arrival_times :=
    forall tsk : Task,
      tsk \in ts ->
      task_min_inter_arrival_time tsk > 0.

  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  Variable arr_seq : arrival_sequence Job.

  (** Then, we define the sporadic task model as follows.*)
  Definition taskset_respects_sporadic_task_model :=
    forall tsk,
      tsk \in ts ->
      respects_sporadic_task_model arr_seq tsk (task_min_inter_arrival_time tsk).

End SporadicModel.
