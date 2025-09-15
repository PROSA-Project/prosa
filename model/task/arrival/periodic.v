Require Export prosa.model.task.arrival.sporadic.
Require Export prosa.model.task.arrival.task_max_inter_arrival.
Require Export prosa.model.task.offset.
Require Export prosa.analysis.facts.job_index.

(** * The Periodic Task Model *)

(** In the following, we define the classic Liu & Layland arrival process,
    i.e., the arrival process commonly known as the _periodic task model_,
    wherein the arrival times of consecutive jobs of a periodic task are
    separated by the task's _period_. *)

(** ** Task Model Parameter for Periods *)

(** Under the periodic task model, each task is characterized by its period,
    which we denote as [task_period]. *)

Class PeriodicModel (Task : TaskType) := task_period : Task -> duration.

(** ** Model Validity *)

(** Next, we define the semantics of the periodic task model. *)
Section ValidPeriodicTaskModel.

  (** Consider any type of periodic tasks. *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** A valid periodic task has a non-zero period. *)
  Definition valid_period (tsk : Task) := task_period tsk > 0.

  (** Next, consider any type of jobs stemming from these tasks ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... and an arbitrary arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that a task respects the periodic task model if every job [j]
      (except the first one) has a predecessor [j'] that arrives exactly one
      task period before it. *)
  Definition respects_periodic_task_model (tsk : Task) :=
    forall j,
      arrives_in arr_seq j ->
      job_index arr_seq j > 0 ->
      job_task j = tsk ->
      exists j',
        arrives_in arr_seq j' /\
        job_index arr_seq j' = job_index arr_seq j - 1 /\
        job_task j' = tsk /\
        job_arrival j = job_arrival j' + task_period tsk.

  (** Further, in the context of a set of periodic tasks, ... *)
  Variable ts : TaskSet Task.

  (** ... every task in the set must have a valid period ... *)
  Definition valid_periods := forall tsk : Task, tsk \in ts -> valid_period tsk.

  (** ... and all jobs of every task in a set of periodic tasks must
      respect the period constraint on arrival times. *)
  Definition taskset_respects_periodic_task_model :=
    forall tsk, tsk \in ts -> respects_periodic_task_model tsk.

End ValidPeriodicTaskModel.
