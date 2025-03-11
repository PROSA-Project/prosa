Require Export prosa.analysis.definitions.request_bound_function.
Require Import prosa.model.priority.elf.

(** * Bound on Higher-or-Equal Priority Workload under ELF Scheduling  *)

(** In this file, we define an upper bound on workload incurred by a
    job from jobs with higher-or-equal priority that come from other
    tasks under ELF scheduling. *)
Section ELFWorkloadBound.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], and an arrival curve [max_arrivals]. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.

  (** Suppose the tasks have relative priority points. *)
  Context `{PriorityPoint Task}.

  (** Now consider any task set [ts]. *)
  Variable ts : seq Task.

  (** Consider any FP Policy. *)
  Context {FP : FP_policy Task}.

  (** Now we define, given the arrival offset [A], the length of the interval in which
     a higher or equal priority job from a task [tsk_o] in the same priority band as [tsk]
     may arrive. *)
  Definition ep_task_interfering_interval_length (tsk tsk_o : Task) (A : duration) :=
    ((A + ε)%:R + task_priority_point tsk - task_priority_point tsk_o)%R.

  (** Using the above definition, we now define a bound on the higher-or-equal priority workload
      from tasks in the same priority band as [tsk]. *)
  Definition bound_on_ep_task_workload (tsk : Task) (A : duration) (delta : duration) :=
    let rbf_duration (tsk_o : Task) := minn `|Num.max 0%R (ep_task_interfering_interval_length tsk tsk_o A)| delta in
      \sum_(tsk_o <- ts | ep_task tsk tsk_o && (tsk_o != tsk))
        task_request_bound_function tsk_o (rbf_duration tsk_o).

  (** Next we define a bound on the higher-priority workload from tasks in
      higher priority bands than [tsk]. *)
  Definition bound_on_hp_task_workload (tsk : Task) (delta : duration) :=
    total_hp_request_bound_function_FP ts tsk delta.

  (** Finally, we define an upper bound on the workload received from jobs
      with higher-than-or-equal priority that come from other
      tasks. *)
  Definition bound_on_athep_workload tsk A delta :=
    bound_on_hp_task_workload tsk delta + bound_on_ep_task_workload tsk A delta.

End ELFWorkloadBound.
