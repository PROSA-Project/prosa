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

  (** We show that if a job of task [tsk] is scheduled at time [t],
      then task [tsk] is scheduled at time [t]. *)
  Lemma job_of_task_scheduled_implies_task_scheduled :
    forall j t,
      job_of_task tsk j ->
      scheduled_at sched j t ->
      task_scheduled_at arr_seq sched tsk t.
  Proof.
    move=> j t TSK.
    rewrite -(scheduled_job_at_iff arr_seq) // /task_scheduled_at => ->.
    by move: TSK; rewrite /job_of_task.
  Qed.

  (** And vice versa, if no job of task [tsk] is scheduled at time
      [t], then task [tsk] is not scheduled at time [t]. *)
  Lemma job_of_task_scheduled_implies_task_scheduled':
    forall j t,
      ~~ job_of_task tsk j ->
      scheduled_at sched j t ->
      ~~ task_scheduled_at arr_seq sched tsk t.
  Proof.
    move => j t TSK SCHED; apply: contra; last exact: TSK.
    move: SCHED; rewrite -(scheduled_job_at_iff arr_seq) // /task_scheduled_at => ->.
    by rewrite /job_of_task.
  Qed.

End TaskSchedule.
