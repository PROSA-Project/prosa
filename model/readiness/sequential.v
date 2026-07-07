Require Export prosa.behavior.all.
Require Export prosa.model.task.sequentiality.

(** * Sequential Readiness Model *)

(** In this module, we specify the notion of sequential task readiness.
    This notion is similar to the classic Liu & Layland model without
    jitter or self-suspensions. However, an important difference is
    that in the sequential task readiness model only the earliest
    pending job of a task is ready. *)

Section SequentialTasksReadiness.

  (** Consider any type of job associated with any type of tasks ... *)
  Context {Job : JobType} {Task : TaskType} `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** A given readiness model [RM] ... *)
  Variable RM : JobReady Job PState.

  (** ... follows the basic sequential readiness model iff a job
      [j] is ready at a time instant [t] exactly when it is pending and all jobs
      from task [job_task j] that arrived earlier than job [j] are already
      completed by time [t]. *)
  Definition basic_sequential_readiness (arr_seq : arrival_sequence Job) :=
    forall sched j t,
      job_ready sched j t = pending sched j t
                            && prior_jobs_complete arr_seq sched j t.

End SequentialTasksReadiness.
