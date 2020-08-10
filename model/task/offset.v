Require Export prosa.model.task.concept.
Require Export prosa.behavior.all.
Require Export prosa.model.task.arrivals.
Require Export prosa.util.all.
Require Export prosa.analysis.facts.behavior.all.

(** * Task Offset *)

(** We define a task-model parameter [task_offset] that maps each task
    to its corresponding offset, that is the instant when its first job arrives. *)
Class TaskOffset (Task : TaskType) := task_offset : Task -> instant.

(** In the following section, we define two important properties 
    that an offset of any task should satisfy. *)
Section ValidTaskOffset.
  
  (** Consider any type of tasks with offsets, ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  
  (** ... any type of jobs associated with these tasks, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** ... and any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** No jobs of a task [tsk] arrive before [task_offset tsk]. *)
  Definition no_jobs_before_offset (tsk : Task) := 
    forall j,
      job_task j = tsk ->
      job_arrival j >= task_offset tsk.
  
  (** Furthermore for a task [tsk], there exists a job that 
      arrives exactly at the offset. *)
  Definition job_released_at_offset (tsk : Task) := 
    exists j',
      arrives_in arr_seq j' /\
      job_task j' = tsk /\
      job_arrival j' = task_offset tsk.
  
  (** An offset is valid iff it satisfies both of the above conditions. *) 
  Definition valid_offset (tsk : Task) := no_jobs_before_offset tsk /\ job_released_at_offset tsk.

  (** In the context of a set of tasks [ts], ... *)
  Variable ts : TaskSet Task.

  (** ... all tasks in the set must have valid offsets. *)
  Definition valid_offsets := forall tsk, tsk \in ts -> valid_offset tsk.
  
End ValidTaskOffset.



