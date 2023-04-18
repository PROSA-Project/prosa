Require Import prosa.behavior.all.
Require Import prosa.model.task.concept.
Require Import prosa.analysis.definitions.job_properties.

(** In this module, we state some general results about
    the [task_cost] parameter. *)
Section TaskCost.

  (** Consider tasks and jobs with the following associated parameters. *)
  Context `{Task : TaskType} `{Job : JobType} `{JobTask Job Task} `{JobCost Job} `{TaskCost Task}.

  (** Consider a task [tsk] and a job of the task [j]. *)
  Variable tsk : Task.
  Variable j : Job.
  Hypothesis H_job_of_task : job_of_task tsk j.

  (** Assume [j] has a positive and valid cost. *)
  Hypothesis H_job_cost_positive : job_cost_positive j.
  Hypothesis H_valid_job_cost : valid_job_cost j.

  (** Then, the task cost of [tsk] is also positive. *)
  Lemma job_cost_positive_implies_task_cost_positive : 0 < task_cost tsk.
  Proof.
    apply leq_trans with (job_cost j) => [//|].
    by move : H_job_of_task => /eqP TSK; rewrite -TSK.
  Qed.

End TaskCost.

(** We add the above lemma to the global hints database. *)
Global Hint Resolve
  job_cost_positive_implies_task_cost_positive:
  basic_rt_facts.
