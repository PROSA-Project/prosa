Require Export prosa.behavior.time.
From mathcomp Require Export eqtype ssrnat.

(** * Notion of a Job Type *)

(** Throughout the library we assume that jobs have decidable equality. *)
Definition JobType := eqType.

(** * Unit of Work *)

(** We define 'work' to denote the unit of service received or needed. In a
   real system, this corresponds to the number of processor cycles. *)
Definition work  := nat.

(** * Basic Job Parameters — Cost, Arrival Time, and Absolute Deadline *)

(** Definition of a generic type of parameter relating jobs to a discrete cost. *)
Class JobCost (Job : JobType) := job_cost : Job -> work.

(** Definition of a generic type of parameter for job_arrival. *)
Class JobArrival (Job : JobType) := job_arrival : Job -> instant.

(** Definition of a generic type of parameter relating jobs to an absolute deadline. *)
Class JobDeadline (Job : JobType) := job_deadline : Job -> instant.
