Require Export prosa.behavior.all.

(** In this section, we introduce properties of a job. *)
Section PropertiesOfJob.

  (** Assume that job costs are known. *)
  Context {Job : JobType}.
  Context `{JobCost Job}.

  (** Consider an arbitrary job. *)
  Variable j : Job.

  (** The job cost must be positive. *)
  Definition job_cost_positive := job_cost j > 0.

End PropertiesOfJob. 