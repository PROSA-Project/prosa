Require Export prosa.model.task.sequentiality.

Section ExecutionOrder.
  
  (** Consider any type of job associated with any type of tasks... *)
  Context {Job: JobType}.
  Context {Task: TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state model. *)
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Assume a schedule ... *)
  Variable sched: schedule PState.

  (** in which the sequential tasks hypothesis holds. *)
  Hypothesis H_sequential_tasks: sequential_tasks sched.


  (** A simple corollary of this hypothesis is that the scheduler
      executes a job with the earliest arrival time. *)
  Corollary scheduler_executes_job_with_earliest_arrival:
    forall j1 j2 t,
      same_task j1 j2 ->
      ~~ completed_by sched j2 t ->
      scheduled_at sched j1 t ->
      job_arrival j1 <= job_arrival j2.
  Proof.
    intros ? ? t TSK NCOMPL SCHED.
    rewrite /same_task eq_sym in TSK.
    have SEQ := H_sequential_tasks j2 j1 t TSK.
    rewrite leqNgt; apply/negP; intros ARR.
    move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
      by apply SEQ.
  Qed.

End ExecutionOrder.
