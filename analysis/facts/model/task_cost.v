Require Import prosa.behavior.all.
Require Export prosa.model.job.properties.
Require Import prosa.model.task.concept.

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
  Lemma job_cost_positive_implies_task_cost_positive :
    0 < task_cost tsk.
  Proof.
    apply leq_trans with (job_cost j) => [//|].
    by move : H_job_of_task => /eqP TSK; rewrite -TSK.
  Qed.

End TaskCost.

(** Next, we prove a simple lemma that extends the notion of [valid_job_cost]
    from a single job to multiple jobs. *)
Section JointWCETCompliance.

  (** Consider any type of tasks and their jobs described by a WCET bound. *)
  Context {Task : TaskType} `{TaskCost Task}.
  Context {Job : JobType} `{JobCost Job} `{JobTask Job Task}.

  (** Consider a given task [tsk] ... *)
  Variable tsk : Task.

  (** ... and any sequence of jobs of task [tsk] (in any order) with job costs
      compliant with the task's WCET bound. *)
  Variable js : seq Job.
  Hypothesis H_valid_jobs : {in js, forall j, job_of_task tsk j && valid_job_cost j}.

  (** Then it is the case that the sum of the costs of the jobs in the sequence
      is upper-bounded by their joint WCET. *)
  Lemma sum_job_costs_bounded :
    \sum_(j <- js) job_cost j <= task_cost tsk * size js.
  Proof.
      rewrite -sum1_size big_distrr /=.
      rewrite [leqLHS]big_seq_cond [leqRHS]big_seq_cond.
      apply: leq_sum => j /andP[IN _] /[! muln1].
      move: (H_valid_jobs _ IN) => /andP[/eqP <- COST].
      by apply: COST.
    Qed.

End JointWCETCompliance.

(** We add the above lemma to the global hints database. *)
Global Hint Resolve
  job_cost_positive_implies_task_cost_positive :
  basic_rt_facts.
