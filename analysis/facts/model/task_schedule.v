Require Export prosa.model.task.concept.
Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.model.scheduled.

(** In this file we provide basic properties related to schedule of a task. *)
Section TaskSchedule.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence of such jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and let [sched] be any corresponding uni-processor schedule. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.
  Variable sched : schedule PState.

  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** We show that if the processor is idle at time [t], then no task
      is scheduled. *)
  Lemma idle_implies_no_task_scheduled :
    forall t,
      is_idle arr_seq sched t ->
      ~~ task_scheduled_at arr_seq sched tsk t.
  Proof.
    move=> t IDLE; rewrite /task_scheduled_at.
    case EQ: (scheduled_job_at arr_seq sched t) => [j | //].
    exfalso.
    apply scheduled_job_at_iff in EQ => //.
    move: IDLE => /negPn /negP => IDLE; apply: IDLE.
    by apply is_nonidle_iff => //.
  Qed.

  (** We show that if a job is scheduled at time [t], then
      [task_scheduled_at tsk t] is equal to [job_of_task tsk j]. In
      other words, any occurrence of [task_scheduled_at] can be
      replaced with [job_of_task]. *)
  Lemma job_scheduled_implies_task_scheduled_eq_job_task :
    forall j t,
      scheduled_at sched j t ->
      task_scheduled_at arr_seq sched tsk t = job_of_task tsk j.
  Proof.
    by move=> j t; rewrite -(scheduled_job_at_iff arr_seq) // /task_scheduled_at => ->.
  Qed.

  (** As a corollary, we show that if a job of task [tsk] is scheduled
      at time [t], then task [tsk] is scheduled at time [t]. *)
  Corollary job_of_task_scheduled_implies_task_scheduled :
    forall j t,
      job_of_task tsk j ->
      scheduled_at sched j t ->
      task_scheduled_at arr_seq sched tsk t.
  Proof.
    by move=> j t TSK SCHED; rewrite (job_scheduled_implies_task_scheduled_eq_job_task j) => //.
  Qed.

  (** And vice versa, if no job of task [tsk] is scheduled at time
      [t], then task [tsk] is not scheduled at time [t]. *)
  Corollary job_of_task_scheduled_implies_task_scheduled':
    forall j t,
      ~~ job_of_task tsk j ->
      scheduled_at sched j t ->
      ~~ task_scheduled_at arr_seq sched tsk t.
  Proof.
    by move=> j t TSK SCHED; rewrite (job_scheduled_implies_task_scheduled_eq_job_task j) => //.
  Qed.

End TaskSchedule.
