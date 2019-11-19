Require Import rt.util.all.
Require Import rt.restructuring.behavior.all.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.preemption.task.parameters.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Task's Run to Completion Threshold *)
(** In this section, we instantiate function [task run to completion
    threshold] for the fully non-preemptive model. *)
Section TaskRTCThresholdFullyNonPreemptive.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}. 
  Context `{TaskCost Task}.
    
  (** In fully non-preemptive model no job can be preempted until its
      completion. Thus, we can set task's run to completion threshold
      to ε. *)
  Global Program Instance fully_nonpreemptive : TaskRunToCompletionThreshold Task :=
    { 
      task_run_to_completion_threshold (tsk : Task) := ε
    }.

End TaskRTCThresholdFullyNonPreemptive.
