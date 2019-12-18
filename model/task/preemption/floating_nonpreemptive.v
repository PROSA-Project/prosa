Require Import prosa.model.preemption.limited_preemptive.
Require Export prosa.model.task.preemption.parameters.

(** * Task Model with Floating Non-Preemptive Regions *)

(** In this file, we instantiate the specific task model of (usually)
    preemptive tasks with "floating" non-preemptive regions, i.e., with jobs
    that exhibit non-preemptive segments of bounded length at unpredictable
    points during their execution.  *)

(** ** Model Validity *)

(** To begin with, we introduce requirements that the function
    [task_max_nonpr_segment] must satisfy to be coherent with the floating
    non-preemptive regions model. *)
Section ValidModelWithFloatingNonpreemptiveRegions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  (** ... with a bound on the maximum non-preemptive segment length ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of limited-preemptive jobs associated with these tasks ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  (** ... with execution costs and specific preemption points. *)
  Context `{JobCost Job}.
  Context `{JobPreemptionPoints Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We require [task_max_nonpreemptive_segment (job_task j)] to be an upper
      bound of the length of the maximum nonpreemptive segment of job [j]. *)
  Definition job_respects_task_max_np_segment :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_max_nonpreemptive_segment j <= task_max_nonpreemptive_segment (job_task j).

  (** A model with floating nonpreemptive regions is valid if it is both valid
      a the job level and jobs respect the upper bound of their task. *)
  Definition valid_model_with_floating_nonpreemptive_regions :=
    valid_limited_preemptions_job_model arr_seq /\
    job_respects_task_max_np_segment.

End ValidModelWithFloatingNonpreemptiveRegions.

(** ** Run-to-Completion Threshold *)

(** In this section, we instantiate the task-level run-to-completion threshold
    for the model with floating non-preemptive regions. *)
Section TaskRTCThresholdFloatingNonPreemptiveRegions.

  (** Consider any type of tasks with a WCET bound.*)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In the model with floating non-preemptive regions, there is no static
      information about the placement of preemption points in all jobs, i.e.,
      it is impossible to predict when exactly a job will be preemptable. Thus,
      the only safe run-to-completion threshold is [task cost]. *)
  Global Program Instance fully_preemptive : TaskRunToCompletionThreshold Task :=
    {
      task_run_to_completion_threshold (tsk : Task) := task_cost tsk
    }.

End TaskRTCThresholdFloatingNonPreemptiveRegions.
