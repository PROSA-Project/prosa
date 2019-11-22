Require Export rt.restructuring.model.task.concept.
(** Given task deadlines and a mapping from jobs to tasks 
   we provide a generic definition of job_deadline. *)
Instance job_deadline_from_task_deadline (Job : JobType) (Task : TaskType)
         `{TaskDeadline Task} `{JobArrival Job} `{JobTask Job Task} : JobDeadline Job :=
  fun (j : Job) => job_arrival j + task_deadline (job_task j).
