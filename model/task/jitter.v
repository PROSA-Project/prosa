Require Export prosa.model.task.concept.
Require Export prosa.model.readiness.jitter.

(** * Task Release Jitter Bound *)

(** We define a task-level parameter that expresses that the release jitter
    experienced by any of the task's jobs is bounded by a known constant. *)
Class TaskJitter (Task : TaskType) := task_jitter : Task -> duration.

(** In the following, we connect the task-level bound to the job-level release
    jitter in the obvious way. *)
Section ValidTaskJitter.

  (** Consider any type of tasks with associated jitter bounds... *)
  Context {Task : TaskType} `{TaskJitter Task}.

  (** ...and the corresponding jobs. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobJitter Job}.

  (** A jitter bound is valid iff it bounds the release jitter experienced by
      any of job of the task. *)
  Definition valid_jitter (tsk : Task) :=
    forall j,
      job_task j = tsk ->
      job_jitter j <= task_jitter tsk.

  (** In the context of a set of tasks [ts], ... *)
  Variable ts : TaskSet Task.

  (** ... all tasks in the set must have valid jitter bounds. *)
  Definition valid_jitter_bounds := forall tsk, tsk \in ts -> valid_jitter tsk.

End ValidTaskJitter.

