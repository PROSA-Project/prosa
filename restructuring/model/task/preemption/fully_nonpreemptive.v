Require Export rt.restructuring.model.task.preemption.parameters.

(** * Platform for Fully Non-Preemptive Model *)
(** In this section, we instantiate function
   [task_max_nonpreemptive_segment] for the fully non-preemptive
   model. *)
Section FullyNonPreemptiveModel.

  (** Consider any type of jobs. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  
  (** In fully non-preemptive model no job can be preempted until its
      completion. The maximal non-preemptive segment of a job
      [j] has length [job_cost j] which is bounded by [task_cost tsk].*)
  Global Program Instance fully_nonpreemptive_model : TaskMaxNonpreemptiveSegment Task :=
    {
      task_max_nonpreemptive_segment (tsk : Task) := task_cost tsk
    }.
                                                     
End FullyNonPreemptiveModel.

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
