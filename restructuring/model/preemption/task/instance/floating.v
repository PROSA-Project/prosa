Require Import rt.util.all.
Require Import rt.restructuring.behavior.all.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.preemption.job.parameters.
Require Import rt.restructuring.model.preemption.task.parameters.
Require Import rt.restructuring.model.preemption.job.instance.limited.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Platform for Models with Floating Non-Preemptive Regions *)
(** In this section, we introduce a set of requirements for function
    [task_max_nonpr_segment], so it is coherent with model with
    floating non-preemptive regions. *)
Section ModelWithFloatingNonpreemptiveRegions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptionPoints Job}.
  
  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** We require [task_max_nonpreemptive_segment (job_task j)] to be
     an upper bound of the lenght of the max nonpreemptive segment of
     job [j]. *)
  Definition job_max_np_segment_le_task_max_np_segment :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_max_nonpreemptive_segment j <= task_max_nonpreemptive_segment (job_task j).

  (** We define a valid model with floating nonpreemptive regions as the
      model with floating nonpreemptive regions at the task-level and
      valid model with limited preemptions at the job-level.  *)
  Definition valid_model_with_floating_nonpreemptive_regions :=
    valid_limited_preemptions_job_model arr_seq /\
    job_max_np_segment_le_task_max_np_segment.

End ModelWithFloatingNonpreemptiveRegions.
