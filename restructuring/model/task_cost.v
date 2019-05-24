From rt.restructuring.behavior Require Export task arrival.arrival_sequence.

Section TaskCost.
  Context {T : TaskType}.

  Variable (task_cost : duration).

  Definition valid_task_cost := task_cost > 0.
End TaskCost.

(* Definition of a generic type of parameter for task cost *)

Class TaskCost (T : TaskType) := task_cost : T -> duration.

Section TasksetCosts.
  Context {T : TaskType} `{TaskCost T}.

  Variable ts : seq T.

  Definition valid_taskset_costs :=
    forall tsk : T,
      tsk \in ts ->
      task_cost tsk > 0.

  Context {J : JobType} `{JobTask J T} `{JobCost J}.

  Variable arr_seq : arrival_sequence J.

  Definition respects_taskset_costs :=
    forall j,
      arrives_in arr_seq j ->
      job_cost j <= task_cost (job_task j).

End TasksetCosts.
