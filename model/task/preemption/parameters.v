Require Export prosa.model.preemption.parameter.
Require Export prosa.model.task.concept.

(** * Task Preemption Model *)

(** In this module, we define the abstract interface for task-level preemption
    models. Specific preemption models are instantiated in the sibling files in
    this directory. *)

(** ** Preemption-Related Task Parameters *)

(** We define three parameters to express the preemption behavior of a given
    task. *)

(** First, we define [task_max_nonpreemptive_segment] to denote a bound on the
    maximum length of a task's non-preemptive segment. *)
Class TaskMaxNonpreemptiveSegment (Task : TaskType) :=
  task_max_nonpreemptive_segment : Task -> work.

(** Second, [task_run_to_completion_threshold] indicates a progress bound with
    the interpretation that, once a job of a task [tsk] has received at least
    [task_run_to_completion_threshold tsk] time units of service, it will
    remain nonpreemptive until the end and run to completion. *)
Class TaskRunToCompletionThreshold (Task : TaskType) :=
  task_run_to_completion_threshold : Task -> work.

(** Third, the parameter [task_preemption_points] indicates the non-preemptive
    segments of a task. Obviously, not all preemption models use this parameter. *)
Class TaskPreemptionPoints (Task : TaskType) :=
  task_preemption_points : Task -> seq work.

(** ** Derived Properties *)
(** In this section, we define the notions of the maximal and the last
    non-preemptive segments of a task. *)
Section MaxAndLastNonpreemptiveSegment.

  (** Consider any type of tasks with fixed preemption points. *)
  Context {Task : TaskType}.
  Context `{TaskPreemptionPoints Task}.

  (** We define a function [task_max_nonpr_segment] that computes the length of
      the longest non-preemptive segment of a given task. *)
  Definition task_max_nonpr_segment (tsk : Task) :=
    max0 (distances (task_preemption_points tsk)).

  (** Similarly, [task_last_nonpr_segment] is a function that computes the
      length of the last non-preemptive segment. *)
  Definition task_last_nonpr_segment (tsk : Task) :=
    last0 (distances (task_preemption_points tsk)).

End MaxAndLastNonpreemptiveSegment.

(** To avoid having to specify redundant information, we allow Coq to
    automatically infer a task's maximum non-preemptive segment length if its
    preemption points are known. *)
Instance TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
         (Task : TaskType) `{TaskPreemptionPoints Task} : TaskMaxNonpreemptiveSegment Task := task_max_nonpr_segment.


(** ** Preemption Model Validity *)

(** For analysis purposes, it is important that the distance between any two
    neighboring preemption points of a job is bounded. We define the validity
    criterion for the maximum non-preemptive segment length accordingly. *)
Section ValidPreemptionModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Suppose we are given the maximum non-preemptive segment length for each task ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and a job-level preemption model. *)
  Context `{JobPreemptable Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.

  (** First we require that [task_max_nonpreemptive_segment] gives an upper
      bound on values of the function [job_max_nonpreemptive_segment]. *)
  Definition job_respects_max_nonpreemptive_segment (j: Job) :=
    job_max_nonpreemptive_segment j <= task_max_nonpreemptive_segment (job_task j).

  (** Next, we require that all segments of a job [j] have bounded length. That
      is, for any progress [ρ] of job [j], there exists a preemption point [pp]
      such that [ρ <= pp <= ρ + (job_max_nps j - ε)]. That is, in any time
      interval of length [job_max_nps j] during which a job is continuously
      scheduled, there exists a preemption point that lies in this interval. *)
  Definition nonpreemptive_regions_have_bounded_length (j : Job) :=
    forall (ρ : duration),
      0 <= ρ <= job_cost j ->
      exists (pp : duration),
        ρ <= pp <= ρ + (job_max_nonpreemptive_segment j - ε) /\
        job_preemptable j pp.

  (** We say that the schedule exhibits bounded nonpreemptive segments iff the
      predicate [job_preemptable] satisfies the two preceding conditions. *)
  Definition model_with_bounded_nonpreemptive_segments :=
    forall j,
      arrives_in arr_seq j ->
      job_respects_max_nonpreemptive_segment j
      /\ nonpreemptive_regions_have_bounded_length j.

  (** Finally, we say that the schedule exhibits _valid_ bounded nonpreemptive
      segments iff the predicate [job_preemptable] defines a valid preemption
      model and if this model has non-preemptive segments of bounded length. *)
  Definition valid_model_with_bounded_nonpreemptive_segments :=
    valid_preemption_model arr_seq sched /\
    model_with_bounded_nonpreemptive_segments.

End ValidPreemptionModel.

(** ** Run-to-Completion Threshold Validity *)

(** Since a task model may not provide exact information about the preemption
    points of a task, a task's run-to-completion threshold generally cannot be
    defined in terms of the preemption points of a task (unlike a job's
    run-to-completion threshold, which can always be computed from a job's
    preemption points). Instead, we require each task-level preemption model to
    specify a task's run-to-completion threshold explicitly. We define its
    required properties in the following. *)
Section ValidTaskRunToCompletionThreshold.

  (** Consider any type of tasks with bounded WCETs ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** ... where each job has an execution cost. *)
  Context `{JobCost Job}.

  (** Suppose we are given a job-level preemption model ... *)
  Context `{JobPreemptable Job}.

  (** ...and the run-to-completion threshold for each task. *)
  Context `{TaskRunToCompletionThreshold Task}.

  (** Further, consider any kind of processor model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched: schedule PState.

  (** A task's run-to-completion threshold must not exceed the WCET of the
      task. *)
  Definition task_rtc_bounded_by_cost tsk :=
    task_run_to_completion_threshold tsk <= task_cost tsk.

  (** We say that the run-to-completion threshold of a task [tsk] bounds the
      job-level run-to-completion threshold iff, for any job [j] of task [tsk],
      the job's run-to-completion threshold is at most the task's
      run-to-completion threshold. *)
  Definition job_respects_task_rtc tsk :=
    forall j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_run_to_completion_threshold j <= task_run_to_completion_threshold tsk.

  (** Finally, we require that a valid run-to-completion threshold parameter
      will satisfy the two above definitions. *)
  Definition valid_task_run_to_completion_threshold tsk :=
    task_rtc_bounded_by_cost tsk /\
    job_respects_task_rtc tsk.

End ValidTaskRunToCompletionThreshold.
