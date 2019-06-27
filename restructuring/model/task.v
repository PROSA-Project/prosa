From mathcomp Require Export ssrbool.
From rt.restructuring.behavior Require Export job.

(* Throughout the library we assume that tasks have decidable equality *)

Definition TaskType := eqType.

(* Definition of a generic type of parameter relating jobs to tasks *)

Class JobTask (J : JobType) (T : TaskType) := job_task : J -> T.

Section SameTask.
  (* For any type of job associated with any type of tasks... *)
  Context {Job: JobType}.
  Context {Task: TaskType}.
  Context `{JobTask Job Task}.

  (* ... we say that two jobs j1 and j2 are from the same task iff job_task j1
     is equal to job_task j2. *)
  Definition same_task j1 j2 := job_task j1 == job_task j2.

End SameTask.

(* Definition of a generic type of parameter for task deadlines *)
Class TaskDeadline (Task : TaskType) := task_deadline : Task -> duration.

(* Given task deadlines and a mapping from jobs to tasks we provide a generic definition of job_deadline *)

Instance job_deadline_from_task_deadline
        (Job : JobType) (Task : TaskType)
        `{TaskDeadline Task} `{JobArrival Job} `{JobTask Job Task} :
  JobDeadline Job := fun j => job_arrival j + task_deadline (job_task j).
