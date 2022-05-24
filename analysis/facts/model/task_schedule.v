Require Export prosa.model.task.concept.
Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.model.ideal.schedule.
        
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

  (** Let [sched] be any ideal uni-processor schedule. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** Let [tsk] be any task. *) 
  Variable tsk : Task.
  
  (** We show that if a job of task [tsk] is scheduled at time [t],
      then task [tsk] is scheduled at time [t]. *)
  Lemma job_of_task_scheduled_implies_task_scheduled :
    forall j t,
      job_of_task tsk j -> 
      scheduled_at sched j t ->
      task_scheduled_at sched tsk t.
  Proof.
    intros ? ? TSK SCHED.
    unfold task_scheduled_at.
    by move: SCHED; rewrite scheduled_at_def => /eqP ->.
  Qed.

  (** And vice versa, if no job of task [tsk] is scheduled at time
      [t], then task [tsk] is not scheduled at time [t]. *)
  Lemma job_of_task_scheduled_implies_task_scheduled':
    forall j t,
      ~~ job_of_task tsk j -> 
      scheduled_at sched j t ->
      ~~ task_scheduled_at sched tsk t.
  Proof.
    move => j t /negP TSK SCHED; apply /negP => TSCHED; apply: TSK.
    move: SCHED; rewrite scheduled_at_def => /eqP SCHED.
    by move: TSCHED; rewrite /task_scheduled_at SCHED.
  Qed.

End TaskSchedule.
