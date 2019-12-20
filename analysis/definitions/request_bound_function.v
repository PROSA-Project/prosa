Require Export prosa.model.task.arrival.curves.
Require Export prosa.model.priority.classes.

(** The following definitions assume ideal uni-processor schedules.
    This restriction exists for historic reasons; the defined concepts
    could be generalized in future work. *)
Require Import prosa.analysis.facts.model.ideal_schedule.

(** * Request Bound Function (RBF) *)

(** We define the notion of a task's request-bound function (RBF), as well as
    the total request bound function of a set of tasks. *)

Section TaskWorkloadBoundedByArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks, where each task has
      a cost. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Consider any ideal uni-processor schedule of these jobs... *)
  Variable sched : schedule (ideal.processor_state Job).

  (** ... and an FP policy that indicates a higher-or-equal priority
      relation. *)
  Context `{FP_policy Task}.

  (** Let [MaxArrivals] denote any function that takes a task and an interval length
      and returns the associated number of job arrivals of the task. *)
  Context `{MaxArrivals Task}.

  (** ** RBF of a Single Task *)

  (** In this section, we define a bound for the workload of a single task
      under uni-processor FP scheduling. *)
  Section SingleTask.

    (** Consider any task [tsk] that is to be scheduled in an interval of length delta. *)
    Variable tsk : Task.
    Variable delta : duration.

    (** We define the following workload bound for the task. *)
    Definition task_request_bound_function :=
      task_cost tsk * max_arrivals tsk delta.

  End SingleTask.

  (** ** Total RBF of Multiple Tasks *)

  (** In this section, we define a bound for the workload of multiple tasks. *)
  Section AllTasks.

    (** Consider a task set ts... *)
    Variable ts : list Task.

    (** ...and let [tsk] be any task in task set. *)
    Variable tsk : Task.

    (** Let delta be the length of the interval of interest. *)
    Variable delta : duration.

    (** Recall the definition of higher-or-equal-priority task and the per-task
        workload bound for FP scheduling. *)
    Let is_hep_task tsk_other := hep_task tsk_other tsk.
    Let is_other_hep_task tsk_other := hep_task tsk_other tsk && (tsk_other != tsk).

    (** Using the sum of individual workload bounds, we define the following
        bound for the total workload of tasks in any interval of length
        delta. *)
    Definition total_request_bound_function :=
      \sum_(tsk <- ts) task_request_bound_function tsk delta.

    (** Similarly, we define the following bound for the total workload of
        tasks of higher-or-equal priority (with respect to [tsk]) in any interval
        of length delta. *)
    Definition total_hep_request_bound_function_FP :=
      \sum_(tsk_other <- ts | is_hep_task tsk_other)
       task_request_bound_function tsk_other delta.

    (** We also define a bound for the total workload of higher-or-equal
        priority tasks other than [tsk] in any interval of length delta. *)
    Definition total_ohep_request_bound_function_FP :=
      \sum_(tsk_other <- ts | is_other_hep_task tsk_other)
       task_request_bound_function tsk_other delta.

  End AllTasks.

End TaskWorkloadBoundedByArrivalCurves.
