Require Export rt.restructuring.model.task.preemption.parameters.

(** * Platform for Fully Preemptive Model *)
(** In this section, we instantiate function
   [task_max_nonpreemptive_segment] for the fully preemptive model. *)
Section FullyPreemptiveModel.

  (** Consider any type of jobs. *)
  Context {Task : JobType}.

  (** In the fully preemptive model any job can be preempted at any time. Thus, 
      the maximal non-preemptive segment has length at most ε. *) 
  Global Program Instance fully_preemptive_model : TaskMaxNonpreemptiveSegment Task :=
    { 
      task_max_nonpreemptive_segment (tsk : Task) := ε
    }.
  
End FullyPreemptiveModel.

Require Export rt.restructuring.model.task.preemption.parameters.

(** * Task's Run to Completion Threshold *)
(** In this section, we instantiate function [task run to completion
   threshold] for the fully preemptive model. *)
Section TaskRTCThresholdFullyPreemptiveModel.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In the fully preemptive model any job can be preempted at any time. Thus, 
       the only safe task's run to completion threshold is [task cost]. *)
  Global Program Instance fully_preemptive : TaskRunToCompletionThreshold Task :=
    { 
      task_run_to_completion_threshold (tsk : Task) := task_cost tsk
    }.
    
End TaskRTCThresholdFullyPreemptiveModel.
