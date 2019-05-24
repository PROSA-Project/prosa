From rt.restructuring.behavior Require Export arrival.arrival_sequence task.

Section TaskMinInterArrivalTime.
  Context {T : TaskType}.

  Variable (task_min_inter_arrival_time : duration).

  Definition valid_task_min_inter_arrival_time :=
    task_min_inter_arrival_time > 0.
End TaskMinInterArrivalTime.

(* Definition of a generic type of parameter for task
   minimum inter arrival times *)

Class SporadicModel (T : TaskType) :=
  task_min_inter_arrival_time : T -> duration.

Section SporadicModel.
  Context {T : TaskType} `{SporadicModel T}.

  Variable ts : seq T.

  Definition valid_taskset_min_inter_arrival_times :=
    forall tsk : T,
      tsk \in ts ->
      task_min_inter_arrival_time tsk > 0.

  Context {J : JobType} `{JobTask J T} `{JobArrival J}.

  Variable arr_seq : arrival_sequence J.

  (* Then, we define the sporadic task model as follows.*)
  Definition respects_sporadic_task_model :=
    forall (j j': J),
      j <> j' -> (* Given two different jobs j and j' ... *)
      arrives_in arr_seq j -> (* ...that belong to the arrival sequence... *)
      arrives_in arr_seq j' ->
      job_task j = job_task j' -> (* ... and that are spawned by the same task, ... *)
      job_arrival j <= job_arrival j' -> (* ... if the arrival of j precedes the arrival of j' ...,  *)
      (* then the arrival of j and the arrival of j' are separated by at least one period. *)
      job_arrival j' >= job_arrival j + task_min_inter_arrival_time (job_task j).

End SporadicModel.
