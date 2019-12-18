Require Export prosa.model.task.preemption.parameters.
Require Import prosa.model.preemption.limited_preemptive.

(** * Limited-Preemptive Task Model *)

(** In this module, we instantiate the task model in which jobs can be
    preempted only at certain preemption points. *)

(** ** Model Validity *)

(** To begin with, we introduce requirements that the function
    [task_max_nonpr_segment] must satisfy to be coherent with the
    limited-preemptive task model. *)
Section ValidModelWithFixedPreemptionPoints.

  (** Consider any type of tasks with WCET bounds and given preemption points ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskPreemptionPoints Task}.

  (**  ... and any type of jobs associated with these tasks, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  (** ... where each job has an arrival time, an execution cost, and some
      preemption points. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptionPoints Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : TaskSet Task.

  (** First, we describe structural properties that a sequence of preemption
      points of a task should satisfy. *)

  (** (1) We require the sequence of preemption points to contain the beginning ... *)
  Definition task_beginning_of_execution_in_preemption_points :=
    forall tsk, tsk \in ts -> first0 (task_preemption_points tsk) = 0.

  (** ... and (2) the end of execution. *)
  Definition task_end_of_execution_in_preemption_points :=
    forall tsk, tsk \in ts -> last0 (task_preemption_points tsk) = task_cost tsk.

  (** (3) Furthermore, we require the sequence of preemption points to be a
          non-decreasing sequence. *)
  Definition nondecreasing_task_preemption_points :=
    forall tsk, tsk \in ts -> nondecreasing_sequence (task_preemption_points tsk).

  (** (4) We also require the number of nonpreemptive segments of a job to be
          equal to the number of nonpreemptive segments of its task. Note that
          some of nonpreemptive segments of a job can have zero length;
          nonetheless the number of segments should match. *)
  Definition consistent_job_segment_count :=
    forall j,
      arrives_in arr_seq j ->
      size (job_preemption_points j) = size (task_preemption_points (job_task j)).

  (** (5) We require the lengths of the nonpreemptive segments of a job to be
          bounded by the lengths of the corresponding segments of its task.  *)
  Definition job_respects_segment_lengths :=
    forall j n,
      arrives_in arr_seq j ->
      nth 0 (distances (job_preemption_points j)) n
      <= nth 0 (distances (task_preemption_points (job_task j))) n.

  (** (6) Lastly, we ban empty nonpreemptive segments at the task level. *)
  Definition task_segments_are_nonempty :=
    forall tsk n,
      (tsk \in ts) ->
      n < size (distances (task_preemption_points tsk)) ->
      ε <= nth 0 (distances (task_preemption_points tsk)) n.

  (** We define a valid task-level model with fixed preemption points as the
      conjunction of the hypotheses above. *)
  Definition valid_fixed_preemption_points_task_model :=
    task_beginning_of_execution_in_preemption_points /\
    task_end_of_execution_in_preemption_points /\
    nondecreasing_task_preemption_points /\
    consistent_job_segment_count /\
    job_respects_segment_lengths /\
    task_segments_are_nonempty.

  (** Finally, a model with fixed preemption points is valid if it is both valid
      a the job and task levels. *)
  Definition valid_fixed_preemption_points_model :=
    valid_limited_preemptions_job_model arr_seq /\
    valid_fixed_preemption_points_task_model.

End ValidModelWithFixedPreemptionPoints.

(** ** Run-to-Completion Threshold *)

(** In this section, we instantiate the task-level run-to-completion threshold
    for the task model with fixed preemption points. *)
Section TaskRTCThresholdLimitedPreemptions.

  (** Consider any type of tasks with WCET bounds and fixed preemption points. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskPreemptionPoints Task}.

  (** Given fixed preemption points, no job can be preempted after a job
      reaches its last non-preemptive segment. Thus, we can set the task-level
      run-to-completion threshold to [task_cost tsk - (task_last_nonpr_seg tsk - ε)],
      which safely bounds [job_cost j - (job_last_nonpr_seg j - ε)]. *)
  Global Program Instance limited_preemptions : TaskRunToCompletionThreshold Task :=
    {
      task_run_to_completion_threshold (tsk : Task) :=
        task_cost tsk - (task_last_nonpr_segment tsk - ε)
    }.

End TaskRTCThresholdLimitedPreemptions.
