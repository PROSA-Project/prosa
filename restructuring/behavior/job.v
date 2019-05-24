From mathcomp Require Export eqtype.

(* Throughout the library we assume that jobs have decidable equality *)

Definition JobType := eqType.

(* Definition of a generic type of parameter relating jobs to a discrete cost *)

Class JobCost (J : JobType) := job_cost : J -> nat.
