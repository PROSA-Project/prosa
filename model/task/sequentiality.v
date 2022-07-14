Require Export prosa.model.task.concept.
Require Export prosa.model.task.arrivals.

(** In this module, we give a precise definition of the common notion of
    "sequential tasks", which is commonly understood to mean that the jobs of a
    sequential task execute in sequence and in a non-overlapping fashion. *)

Section PropertyOfSequentiality.

  (** Consider any type of jobs stemming from any type of tasks ... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any kind of processor model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *) 
  Variable arr_seq : arrival_sequence Job.
  
  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.
  
  (** We say that the tasks execute sequentially if each task's jobs are
      executed in arrival order and in a non-overlapping fashion. *)
  Definition sequential_tasks :=
    forall (j1 j2 : Job) (t : instant),
      arrives_in arr_seq j1 -> 
      arrives_in arr_seq j2 -> 
      same_task j1 j2 ->
      job_arrival j1 < job_arrival j2 ->
      scheduled_at sched j2 t ->
      completed_by sched j1 t.

  (** Given a job [j] and a time instant [t], we say that all prior
     jobs are completed if any job [j_tsk] of task [job_task j] that
     arrives before time [job_arrival j] is completed by time [t]. *)
  Definition prior_jobs_complete (j : Job) (t : instant) :=
    all 
      (fun j_tsk => completed_by sched j_tsk t) 
      (task_arrivals_before arr_seq (job_task j) (job_arrival j)).

End PropertyOfSequentiality.
