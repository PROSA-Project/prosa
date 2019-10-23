From rt.util Require Import all.
From rt.restructuring.behavior Require Import job schedule.
From rt.restructuring Require Import model.job model.task.
From rt.restructuring.model.preemption Require Import task.parameters.

(** * Task's Run to Completion Threshold *)
(** In this section, we instantiate function [task run to completion
    threshold] for the limited preemptions model. *)
Section TaskRTCThresholdLimitedPreemptions.
  
  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskPreemptionPoints Task}.
    
  (** In the model with limited preemptions, no job can be preempted after
      a job reaches its last non-preemptive segment. Thus, we can
      set task's run to completion threshold to [task_cost tsk -
      (task_last_nonpr_seg tsk - ε)] which is always greater than
      [job_cost j - (job_last_nonpr_seg j - ε)]. *)
  Global Program Instance limited_preemptions : TaskRunToCompletionThreshold Task :=
    { 
      task_run_to_completion_threshold (tsk : Task) :=
        task_cost tsk - (task_last_nonpr_segment tsk - ε)
    }.
  
End TaskRTCThresholdLimitedPreemptions.
