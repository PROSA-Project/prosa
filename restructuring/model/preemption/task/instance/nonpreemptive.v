Require Export rt.util.all.
Require Import rt.restructuring.behavior.all.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Export rt.restructuring.model.preemption.valid_model.
Require Export rt.restructuring.model.preemption.job.parameters.
Require Export rt.restructuring.model.preemption.task.parameters.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

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
