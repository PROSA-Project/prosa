Require Export prosa.model.task.concept.

(** In this module, we give a precise definition of the common notion of
    "sequential tasks", which is commonly understood to mean that the jobs of a
    sequential task execute in sequence and in a non-overlapping fashion. *)

Section PropertyOfSequentiality.

  (** Consider any type of jobs stemming from any type of tasks ... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor model. *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Given a schedule of such jobs ... *)
  Variable sched: schedule PState.

  (** ... we say that the tasks execute sequentially if each task's jobs are
     executed in arrival order and in a non-overlapping fashion. *)
  Definition sequential_tasks :=
    forall (j1 j2: Job) (t: instant),
      same_task j1 j2 ->
      job_arrival j1 < job_arrival j2 ->
      scheduled_at sched j2 t ->
      completed_by sched j1 t.

End PropertyOfSequentiality.
