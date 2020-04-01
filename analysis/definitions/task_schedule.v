Require Export prosa.model.task.concept.

(** Due to historical reasons this file defines the notion of a
    schedule of a task for the ideal uni-processor model. This is not
    a fundamental limitation and the notion can be further generalized
    to an arbitrary model. *)
Require Export prosa.model.processor.ideal.

(** * Schedule of task *)
(** In this section we define properties of schedule of a task *)
Section ScheduleOfTask.
 
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
  
  (** Next we define whether a task is scheduled at time [t], ... *)
  Definition task_scheduled_at (t : instant) :=
    if sched t is Some j then
      job_task j == tsk
    else false.

  (** ...which also corresponds to the instantaneous service it receives. *)
  Definition task_service_at (t : instant) := task_scheduled_at t.

  (** Based on the notion of instantaneous service, we define the
       cumulative service received by [tsk] during any interval <<[t1, t2)>>... *)
  Definition task_service_during (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) task_service_at t.

  (** ...and the cumulative service received by [tsk] up to time t2,
       i.e., in the interval <<[0, t2)>>. *)
  Definition task_service (t2 : instant) := task_service_during 0 t2.

End ScheduleOfTask. 
