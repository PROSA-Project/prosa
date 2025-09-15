Require Export prosa.behavior.all.
Require Export prosa.util.all.

(** * Task Type *)

(** As in case of the job model, we make no assumptions about the structure or
    type of tasks, i.e., like jobs, we consider tasks to be mathematically
    opaque objects. We only assume that any type that represents tasks has a
    decidable equality. *)
Definition TaskType := eqType.

(** * Task Model Core Parameters *)

(** In the following, we define three central parameters of the task model: how
    jobs map to tasks, deadlines of tasks, and each task's WCET parameter. *)

(** First, we define a job-model parameter [job_task] that maps each job to its
    corresponding task. *)
Class JobTask (Job : JobType) (Task : TaskType) := job_task : Job -> Task.

(** Second, we define a task-model parameter to express each task's relative
    deadline. *)
Class TaskDeadline (Task : TaskType) := task_deadline : Task -> duration.

(** Third, we define a task-model parameter to express each task's worst-case
    execution cost (WCET). *)
Class TaskCost (Task : TaskType) := task_cost : Task -> duration.

(** And finally, we define a task-model parameter to express each task's best-case
    execution cost (BCET). *)
Class TaskMinCost (Task : TaskType) := task_min_cost : Task -> duration.


(** * Task Model Validity *)

(** In the following section, we introduce properties that a reasonable task
    model must satisfy. *)
Section ModelValidity.

  (** Consider any type of tasks with WCETs/BCETs and relative deadlines. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMinCost Task}.
  Context `{TaskDeadline Task}.

  (** First, we constrain the possible WCET values of a valid task. *)
  Section ValidCost.

    (** Consider an arbitrary task. *)
    Variable tsk : Task.

    (** The WCET of the task should be positive. *)
    Definition task_cost_positive := task_cost tsk > 0.

    (** The WCET should not be larger than the deadline, as otherwise the task
        is trivially infeasible. *)
    Definition task_cost_at_most_deadline := task_cost tsk <= task_deadline tsk.

  End ValidCost.

  (** Second, we relate the cost of a task's jobs to its WCET. *)
  Section ValidJobCost.

    (** Consider any type of jobs associated with the tasks ... *)
    Context {Job : JobType}.
    Context `{JobTask Job Task}.
    (** ... and consider the cost of each job. *)
    Context `{JobCost Job}.

    (** The cost of any job [j] cannot exceed the WCET of its respective
        task. *)
    Definition valid_job_cost j :=
      job_cost j <= task_cost (job_task j).

    (** Every job has a valid job cost. *)
    Definition jobs_have_valid_job_costs :=
      forall j, valid_job_cost j.

    (** Next, consider any arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.

    (** The cost of a job from the arrival sequence cannot
       be larger than the task cost. *)
    Definition arrivals_have_valid_job_costs :=
      forall j,
        arrives_in arr_seq j ->
        valid_job_cost j.

  End ValidJobCost.

  (** Third, we relate the cost of a task's jobs to its BCET. *)
  Section ValidMinJobCost.

    (** Consider any type of jobs associated with the tasks ... *)
    Context {Job : JobType}.
    Context `{JobTask Job Task}.
    (** ... and consider the cost of each job. *)
    Context `{JobCost Job}.

    (** The cost of any job [j] cannot be less than the BCET of its respective
        task. *)
    Definition valid_min_job_cost j :=
      task_min_cost (job_task j) <= job_cost j.

    (** Every job have a valid job cost *)
    Definition jobs_have_valid_min_job_costs :=
      forall j, valid_min_job_cost j.

    (** Next, consider any arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.

    (** The cost of a job from the arrival sequence cannot
       be less than the task cost. *)
    Definition arrivals_have_valid_min_job_costs :=
      forall j,
        arrives_in arr_seq j ->
        valid_min_job_cost j.

  End ValidMinJobCost.

End ModelValidity.

(** * Task Sets *)

(** Next, we introduce the notion of a task set and define properties of valid
    task sets. *)

(** For simplicity, we represent sets of such tasks simply as (finite) sequences of
    tasks. *)
Definition TaskSet := seq.

Section ValidTaskSet.

  (** Consider any type of tasks with WCETs ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  (** ... as well as their individual execution costs. *)
  Context `{JobCost Job}.

  (** Further, consider an arrival sequence of these jobs... *)
  Variable arr_seq : arrival_sequence Job.

  (** ...and the set of tasks that generate them.  *)
  Variable ts : TaskSet Task.

  (** All jobs in the arrival sequence should come from the task set. *)
  Definition all_jobs_from_taskset :=
    forall j,
      arrives_in arr_seq j ->
      job_task j \in ts.

End ValidTaskSet.

(** Finally, for readability, we define two ways in which jobs and tasks
    relate. *)
Section SameTask.

  (** For any type of job associated with any type of tasks... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... we say that two jobs [j1] and [j2] are from the same task iff
      [job_task j1] is equal to [job_task j2]. *)
  Definition same_task (j1 j2 : Job) := job_task j1 == job_task j2.

  (** Trivially, [same_task] is symmetric. *)
  Remark same_task_sym :
    forall j1 j2,
      same_task j1 j2 = same_task j2 j1.
  Proof. by move=> j1 j2; rewrite /same_task eq_sym. Qed.

  (** We further say that a job [j] is a job of task [tsk] iff [job_task j] is
      equal to [tsk]. *)
  Definition job_of_task (tsk : Task) (j : Job) := job_task j == tsk.

  (** Trivially, if one job is a job of a given task, and another is not, then
      the two jobs do not come from the same task. *)
  Remark diff_task :
    forall tsk j1 j2,
      job_of_task tsk j1 ->
      ~~ job_of_task tsk j2 ->
      ~~ same_task j1 j2.
  Proof.
    move=> tsk j1 j2 /eqP OF /eqP NOF.
    apply/eqP => SAME.
    by apply: NOF; rewrite -SAME.
  Qed.

End SameTask.
