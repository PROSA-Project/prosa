From rt.restructuring.behavior Require Export time.
From mathcomp Require Export eqtype.

(* Throughout the library we assume that jobs have decidable equality *)

Definition JobType := eqType.

(* Definition of a generic type of parameter relating jobs to a discrete cost *)

Class JobCost (J : JobType) := job_cost : J -> duration.

(* Definition of a generic type of parameter for job_arrival *)

Class JobArrival (J : JobType) := job_arrival : J -> instant.

(* Definition of a generic type of parameter relating jobs to an absolute deadline *)
Class JobDeadline (J : JobType) := job_deadline : J -> instant.