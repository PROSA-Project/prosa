Require Export prosa.model.task.concept.
Require Export prosa.analysis.definitions.service.
Require Export prosa.model.schedule.scheduled.

(** * Schedule and Service of task *)
(** In this section we define properties of the schedule and service
    of a task. *)
Section ScheduleAndServiceOfTask.

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

  (** Let [sched] be any kind of schedule *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** We define a set of jobs of task [tsk] that are scheduled at time
      [t]. *)
  Definition scheduled_jobs_of_task_at (t : instant) :=
    [seq j <- scheduled_jobs_at arr_seq sched t | job_of_task tsk j].

  (** Next we define whether task [tsk] is scheduled at time [t]. *)
  Definition task_scheduled_at (t : instant) :=
    scheduled_jobs_of_task_at t != [::].

  (** We define the instantaneous service of [tsk] as the total
      instantaneous service of all jobs of this task scheduled at time
      [t]. *)
  Definition task_service_at (t : instant) :=
    \sum_(j <- scheduled_jobs_of_task_at t) service_at sched j t.

  (** Based on the notion of instantaneous service, we define the
      cumulative service received by [tsk] during any interval <<[t1, t2)>> ... *)
  Definition task_service_during (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) task_service_at t.

  (** ...and the cumulative service received by [tsk] up to time [t2],
      i.e., in the interval <<[0, t2)>>. *)
  Definition task_service (t2 : instant) := task_service_during 0 t2.

  (** Similarly, we define a set of jobs of task [tsk] receiving
      service at time [t]. *)
  Definition served_jobs_of_task_at (t : instant) :=
    [seq j <- scheduled_jobs_of_task_at t | receives_service_at sched j t].

  (** Next, we define whether [tsk] is served at time [t]. *)
  Definition task_served_at (t : instant) :=
    served_jobs_of_task_at t != [::].

End ScheduleAndServiceOfTask.
