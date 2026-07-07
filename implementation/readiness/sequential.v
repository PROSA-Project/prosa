Require Export prosa.model.readiness.sequential.

(** * Basic Sequential Readiness Model *)

(** In this module, we define the concrete readiness instance for the basic
    sequential task readiness model, in which only the earliest pending job of a
    task is ready. *)

Section SequentialTasksReadiness.

  (** Consider any type of job associated with any type of tasks... *)
  Context {Job : JobType} {Task : TaskType} `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Consider a given job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** A job [j] is ready at a time instant [t] iff it is pending and all jobs
      from task [job_task j] that arrived earlier than job [j] are already
      completed by time [t]. *)
  #[local,program] Instance sequential_ready_instance : JobReady Job PState :=
  {
    job_ready sched j t := pending sched j t
                           && prior_jobs_complete arr_seq sched j t;
  }.
  Next Obligation. by move=> sched j t /andP[]. Qed.

  (** The concrete sequential readiness instance satisfies the axiomatic
      specification of basic sequential readiness. *)
  Fact sequential_readiness_spec :
    basic_sequential_readiness sequential_ready_instance arr_seq.
  Proof. by []. Qed.

End SequentialTasksReadiness.

(** We add the concrete model's specification to the basic facts database so
    implementation modules can use it automatically. *)
Global Hint Resolve sequential_readiness_spec : basic_rt_facts.
