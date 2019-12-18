Require Export prosa.model.readiness.suspension.
Require Export prosa.model.task.concept.

(** * Task Parameter for the Dynamic Self-Suspension Model *)

(** Under the dynamic self-suspension model, for each task, there is a bound on
    the maximum total self-suspension duration exhibited by any job of the
    task. *)
Class TaskTotalSuspension (Task : TaskType) := task_total_suspension : Task -> duration.

(** * Validity *)

(** In the following section, we specify the semantics of the dynamic
    self-suspension model: each job self-suspends in total no longer than
    specified by the cumulative self-suspension bound of its associated
    task. *)

Section ValidDynamicSuspensions.

  (** Consider any kind of jobs,... *)
  Context {Job : JobType}.

  (** ...where each job has a cost and may exhibit self-suspensions,... *)
  Context `{JobCost Job} `{JobSuspension Job}.

  (** ...and the tasks from which these jobs stem. *)
  Context {Task : TaskType}.
  Context `{JobTask Job Task} `{TaskTotalSuspension Task}.

  (** Under the dynamic self-suspension model, the total self-suspension time
      of any job cannot exceed the self-suspension bound of its associated
      task. *)
  Definition valid_dynamic_suspensions :=
    forall j, total_suspension j <= task_total_suspension (job_task j).

End ValidDynamicSuspensions.
