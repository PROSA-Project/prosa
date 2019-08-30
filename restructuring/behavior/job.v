From rt.restructuring.behavior Require Export time.
From mathcomp Require Export eqtype ssrnat.

(* Throughout the library we assume that jobs have decidable equality. *)
Definition JobType := eqType.

(* Definition of a generic type of parameter relating jobs to a discrete cost. *)
Class JobCost (Job : JobType) := job_cost : Job -> duration.

(* Definition of a generic type of parameter for job_arrival. *)
Class JobArrival (Job : JobType) := job_arrival : Job -> instant.

(* Definition of a generic type of parameter relating jobs to an absolute deadline. *)
Class JobDeadline (Job : JobType) := job_deadline : Job -> instant.

(* Definition of a generic type of release jitter parameter. *)
Class JobJitter (Job : JobType) := job_jitter : Job -> duration.

(* Definition of a generic type of parameter relating jobs to their preemption points. *)
Class JobPreemptable (Job : JobType) := job_preemptable : Job -> duration -> bool.