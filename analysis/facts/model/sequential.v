Require Export prosa.analysis.facts.behavior.all.
Require Export prosa.model.task.sequentiality.
Require Export prosa.analysis.definitions.readiness.
Require Export prosa.analysis.facts.model.task_arrivals.

Section ExecutionOrder.

  (** Consider any type of job associated with any type of tasks... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.

  (** ... in which the sequential tasks hypothesis holds. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.

  (** A simple corollary of this hypothesis is that the scheduler
      executes a job with the earliest arrival time. *)
  Corollary scheduler_executes_job_with_earliest_arrival :
    forall j1 j2 t,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      same_task j1 j2 ->
      ~~ completed_by sched j2 t ->
      scheduled_at sched j1 t ->
      job_arrival j1 <= job_arrival j2.
  Proof.
    move=> j1 j2 t ARR1 ARR2 TSK NCOMPL SCHED.
    have {}TSK := eqbLR (same_task_sym _ _) TSK.
    have SEQ := H_sequential_tasks j2 j1 t ARR2 ARR1 TSK.
    rewrite leqNgt; apply/negP => ARR.
    exact/(negP NCOMPL)/SEQ.
  Qed.

  (** Likewise, if we see an earlier-arrived incomplete job [j1] while another
      job [j2] is scheduled, then [j1] and [j2] must stem from different
      tasks. *)
  Corollary sequential_tasks_different_tasks :
    forall j1 j2 t,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      job_arrival j1 < job_arrival j2 ->
      ~~ completed_by sched j1 t ->
      scheduled_at sched j2 t ->
      ~~ same_task j1 j2.
  Proof.
    move=> j1 j2 t IN1 IN2 LT_ARR INCOMP SCHED.
    apply: contraL INCOMP => SAME.
    by apply/negPn/H_sequential_tasks; eauto.
  Qed.

End ExecutionOrder.


(** In the following section, we connect [sequential_readiness] with
    [sequential_tasks], showing that the latter follows from the former. *)
Section FromSequentialReadiness.

  (** Consider any type of job associated with any type of tasks ... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any kind of processor state, ... *)
  Context {PState : ProcessorState Job}.

  (** ... and any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** If we have a sequential readiness model, ... *)
  Context {JR : JobReady Job PState}.
  Hypothesis H_sequential : sequential_readiness JR arr_seq.

  (** ... then in any valid schedule of the arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** ... all tasks execute sequentially. *)
  Lemma sequential_tasks_from_readiness :
    sequential_tasks arr_seq sched.
  Proof.
    move=> j j' t IN IN' SAME LT_ARR SCHED'.
    have /allP COMP: prior_jobs_complete arr_seq sched j' t by apply: H_sequential.
    apply/COMP/job_in_task_arrivals_between => //.
    by move: SAME => /eqP.
  Qed.

End FromSequentialReadiness.
