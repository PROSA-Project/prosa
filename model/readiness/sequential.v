Require Export prosa.behavior.all.
Require Export prosa.model.task.sequentiality.

(** * Sequential Readiness Model *)

(** In this module, we define the notion of sequential task readiness.
    This notion is similar to the classic Liu & Layland model without
    jitter or self-suspensions. However, an important difference is
    that in the sequential task readiness model only the earliest
    pending job of a task is ready. *)

Section SequentialTasksReadiness.

  (** Consider any type of job associated with any type of tasks... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Consider any job arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** A job [j] is ready at a time instant [t] iff all jobs from task
     [job_task j] that arrived earlier than job [j] are already
     completed by time [t]. *)
  #[local,program] Instance sequential_ready_instance : JobReady Job PState :=
  {
    job_ready sched j t := pending sched j t &&
                             prior_jobs_complete arr_seq sched j t
  }.
  Next Obligation. by move: H2 => /andP[]. Qed.

End SequentialTasksReadiness.
