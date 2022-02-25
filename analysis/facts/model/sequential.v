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
  Context {PState: ProcessorState Job}.


  (** Consider any arrival sequence ... *) 
  Variable arr_seq : arrival_sequence Job.
  
  (** ... and any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.  
  
  (** ... in which the sequential tasks hypothesis holds. *)
  Hypothesis H_sequential_tasks: sequential_tasks arr_seq sched.

  (** A simple corollary of this hypothesis is that the scheduler
      executes a job with the earliest arrival time. *)
  Corollary scheduler_executes_job_with_earliest_arrival:
    forall j1 j2 t,
      arrives_in arr_seq j1 -> 
      arrives_in arr_seq j2 ->
      same_task j1 j2 ->
      ~~ completed_by sched j2 t ->
      scheduled_at sched j1 t ->
      job_arrival j1 <= job_arrival j2.
  Proof.
    intros ? ? t ARR1 ARR2 TSK NCOMPL SCHED.
    rewrite /same_task eq_sym in TSK.
    have SEQ := H_sequential_tasks j2 j1 t ARR2 ARR1 TSK.
    rewrite leqNgt; apply/negP; intros ARR.
    move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
    by apply SEQ.
  Qed.

End ExecutionOrder.
