From rt.util Require Export all.
From rt.restructuring.behavior Require Import all. 
From rt.restructuring Require Import model.job model.task.
From rt.restructuring.model.preemption Require Import
     valid_model job.parameters task.parameters.

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
