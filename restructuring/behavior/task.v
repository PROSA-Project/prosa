From mathcomp Require Export ssrbool.
From rt.restructuring.behavior Require Export job.

(* Throughout the library we assume that jobs have decidable equality *)

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
