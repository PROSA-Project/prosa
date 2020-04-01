Require Export prosa.model.task.concept.

(** In this module, we provide basic definitions concerning the job
    arrivals of a given task. *)

Section TaskArrivals.

  (** Consider any type of job associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** Consider any job arrival sequence ...  *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any task. *)
  Variable tsk : Task.

  (** First, we construct the list of jobs of task [tsk] that arrive
      in a given half-open interval <<[t1, t2)>>. *)
  Definition task_arrivals_between (t1 t2 : instant) :=
    [seq j <- arrivals_between arr_seq t1 t2 | job_task j == tsk].

  (** Based on that, we define the list of jobs of task [tsk] that
      arrive up to and including time [t], ...*)
  Definition task_arrivals_up_to (t : instant) := task_arrivals_between 0 t.+1.

  (** ...and the list of jobs of task [tsk] that arrive strictly
      before time [t], ... *)
  Definition task_arrivals_before (t : instant) := task_arrivals_between 0 t.

  (** ... and also count the number of job arrivals. *)
  Definition number_of_task_arrivals (t1 t2 : instant) :=
    size (task_arrivals_between t1 t2).
    
End TaskArrivals.
