Require Export prosa.model.task.concept.

(** Given relative task deadlines and a mapping from jobs to tasks, we provide
    the canonical definition of each job's absolute deadline, i.e.,
    [job_deadline], as the job's arrival time plus its task's relative
    deadline. *)

Instance job_deadline_from_task_deadline (Job : JobType) (Task : TaskType)
         `{TaskDeadline Task} `{JobArrival Job} `{JobTask Job Task} : JobDeadline Job :=
  fun (j : Job) => job_arrival j + task_deadline (job_task j).
