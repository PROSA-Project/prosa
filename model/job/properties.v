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

(** In the next section, we lift the above property to the level 
    of arrival sequences. *)
Section PropertiesOfAllJobs.

  (** Consider any type of jobs... *)
  Context {Job : JobType}.

  (** ... and the cost associated with each job. *)
  Context `{JobCost Job}.

  (** Next, consider any arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that the arrival sequence has positive job costs if every
      job in the sequence has positive cost. *)
  Definition arrivals_have_positive_job_costs :=
    forall j,
      arrives_in arr_seq j ->
      job_cost_positive j.

End PropertiesOfAllJobs.
