From rt.behavior Require Export job.

(* Throughout the library we assume that jobs have decidable equality *)

Definition TaskType := eqType.

(* Definition of a generic type of parameter relating jobs to tasks *)

Class JobTask (T : TaskType) (J : JobType) := job_task : J -> T.