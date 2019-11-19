Require Import rt.util.all.
Require Import rt.restructuring.behavior.job.
Require Import rt.restructuring.behavior.schedule.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.preemption.task.parameters.

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
