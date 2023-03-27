Require Export prosa.model.task.concept.
Require Export prosa.model.schedule.scheduled.

(** Due to historical reasons this file defines the notion of a schedule of a
    task for (arbitrary) uni-processor models. This is not a fundamental
    limitation and the notion can be further generalized to multiprocessor
    models. *)

(** * Schedule of task *)
(** In this section we define properties of the schedule of a task. *)
Section ScheduleOfTask.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

    (** Consider any arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** Let [sched] be any kind of uniprocessor schedule *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** Next we define whether a task is scheduled at time [t], ... *)
  Definition task_scheduled_at (t : instant) :=
    if (scheduled_job_at arr_seq sched t) is Some j then
      job_task j == tsk
    else false.

  (** ...which also corresponds to the instantaneous service it receives. *)
  Definition task_service_at (t : instant) := task_scheduled_at t.

  (** Based on the notion of instantaneous service, we define the cumulative
       service received by [tsk] during any interval <<[t1, t2)>>... *)
  Definition task_service_during (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) task_service_at t.

  (** ...and the cumulative service received by [tsk] up to time [t2], i.e., in
       the interval <<[0, t2)>>. *)
  Definition task_service (t2 : instant) := task_service_during 0 t2.

End ScheduleOfTask.
