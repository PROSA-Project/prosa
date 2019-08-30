From rt.restructuring.behavior Require Export time job.
From mathcomp Require Export eqtype ssrnat.

(* In this section, we introduce properties of a job. *)
Section PropertesOfJob.

  (* Assume that job costs are known. *)
  Context {Job : JobType}.
  Context `{JobCost Job}.

  (* Consider an arbitrary job. *)
  Variable j: Job.

  (* The job cost must be positive. *)
  Definition job_cost_positive := job_cost j > 0.

End PropertesOfJob.