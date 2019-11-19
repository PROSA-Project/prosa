Require Export rt.util.all.
Require Import rt.restructuring.behavior.all.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.preemption.task.parameters.

(** * Task's Run to Completion Threshold *)
(** In this section, we instantiate function [task run to completion
    threshold] for the model with floating non-preemptive regions. *)
Section TaskRTCThresholdFloatingNonPreemptiveRegions.

  (** Consider any type of tasks.*)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  
  (** In the model with floating non-preemptive regions, task has to
      static information about the placement of preemption
      points. Thus, the only safe task's run to completion threshold
      is [task cost]. *)
  Global Program Instance fully_preemptive : TaskRunToCompletionThreshold Task :=
    { 
      task_run_to_completion_threshold (tsk : Task) := task_cost tsk
    }.

End TaskRTCThresholdFloatingNonPreemptiveRegions.
