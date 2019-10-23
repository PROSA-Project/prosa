From rt.util Require Import all.
From rt.restructuring.behavior Require Import all.
From rt.restructuring Require Import model.job model.task.
From rt.restructuring.model.preemption Require Import task.parameters.

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
