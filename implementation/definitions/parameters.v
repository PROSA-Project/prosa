Require Export prosa.model.task.concept.

(** * Implementation-Specific Task and Job Parameters *)

(** We define some additional task- and job-level workload model parameters that
    are useful in concrete implementations. *)

(** Numeric task identifiers let implementations distinguish tasks through a
    common interface. *)
Class TaskId (Task : TaskType) := { task_id : Task -> nat }.

(** Likewise, numeric job identifiers let implementations distinguish jobs with
    otherwise equal parameters, which is useful for tie-breaking purposes. *)
Class JobId (Job : JobType) := { job_id : Job -> nat }.

(** ** Identifier Uniqueness *)

(** Unique task identifiers allow implementations to use IDs to determine task
    identity. *)
Section ValidTaskIds.

  (** Consider tasks with numeric identifiers. *)
  Context {Task : TaskType} `{TaskId Task}.

  (** Within a given task set, each identifier unambiguously identifies a task. *)
  Definition valid_task_ids (ts : TaskSet Task) :=
    forall tsk1 tsk2,
      tsk1 \in ts ->
      tsk2 \in ts ->
      task_id tsk1 = task_id tsk2 ->
      tsk1 = tsk2.

End ValidTaskIds.

(** Task and job identifiers together allow implementations to refer
    unambiguously to jobs throughout an arrival sequence. *)
Section ValidJobIds.

  (** Consider tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{TaskId Task}.

  (** ... and their jobs, also with numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobId Job}.

  (** Task IDs provide the scope in which job IDs determine job identity. *)
  Definition valid_job_ids (arr_seq : arrival_sequence Job) :=
    forall j1 j2,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      task_id (job_task j1) = task_id (job_task j2) ->
      job_id j1 = job_id j2 ->
      j1 = j2.

  (** We next relate job IDs to arrival times. *)
  Context `{JobArrival Job}.

  (** We say that job identifiers are monotonic if they are consistent with the
      arrival order. *)
  Definition monotonic_job_ids (arr_seq : arrival_sequence Job) :=
    forall j1 j2,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      task_id (job_task j1) = task_id (job_task j2) ->
      job_arrival j1 < job_arrival j2 ->
      job_id j1 < job_id j2.

End ValidJobIds.
