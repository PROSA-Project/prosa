Require Export prosa.model.task.arrival.sporadic.

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
  Definition valid_period tsk := task_period tsk > 0.

  (** Further, in the context of a set of periodic tasks, ... *)
  Variable ts : TaskSet Task.

  (** ... every task in the set must have a  valid period. *)
  Definition valid_periods := forall tsk : Task, tsk \in ts -> valid_period tsk.

  (** Next, consider any type of jobs stemming from these tasks ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... and an arbitrary arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that a task respects the periodic task model if the arrivals of
      its jobs in the arrival sequence are separated by integer multiples of
      the period. *)
  Definition respects_periodic_task_model (tsk : Task) :=
    forall (j j': Job),
      (** Given two different jobs j and j' ... *)
      j <> j' ->
      (** ...that belong to the arrival sequence... *)
      arrives_in arr_seq j ->
      arrives_in arr_seq j' ->
      (** ... and that stem from the given task, ... *)
      job_task j = tsk ->
      job_task j' = tsk ->
      (** ... if [j] arrives no later than [j'] ...,  *)
      job_arrival j <= job_arrival j' ->
      (** ... then the arrivals of [j] and [j'] are separated by an integer
          multiple of [task_period tsk]. *)
      exists n, n > 0 /\ job_arrival j' =  (n * task_period tsk) + job_arrival j.

  (** Every task in a set of periodic tasks must satisfy the above
      criterion. *)
  Definition taskset_respects_periodic_task_model :=
    forall tsk, tsk \in ts -> respects_periodic_task_model tsk.

End ValidPeriodicTaskModel.

(** ** Treating Periodic Tasks as Sporadic Tasks *)

(** Since the periodic-arrivals assumption is stricter than the
    sporadic-arrivals assumption (i.e., any periodic arrival sequence is also a
    valid sporadic arrivals sequence), it is sometimes convenient to apply
    analyses for sporadic tasks to periodic tasks. We therefore provide an
    automatic "conversion" of periodic tasks to sporadic tasks, i.e., we tell
    Coq that it may use a periodic task's [task_period] parameter also as the
    task's minimum inter-arrival time [task_min_inter_arrival_time]
    parameter. *)

Section PeriodicTasksAsSporadicTasks.
  (** Any type of periodic tasks ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... and their corresponding jobs ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... may be interpreted as a type of sporadic tasks by using each task's
      period as its minimum inter-arrival time ... *)
  Global Instance periodic_as_sporadic : SporadicModel Task :=
    {
      task_min_inter_arrival_time := task_period
    }.

  (** ... such that the model interpretation is valid, both w.r.t. the minimum
      inter-arrival time parameter ... *)
  Remark valid_period_is_valid_inter_arrival_time:
    forall tsk, valid_period tsk -> valid_task_min_inter_arrival_time tsk.
  Proof. trivial. Qed.

  (** ... and the separation of job arrivals. *)
  Remark periodic_task_respects_sporadic_task_model:
    forall arr_seq tsk,
      respects_periodic_task_model arr_seq tsk -> respects_sporadic_task_model arr_seq tsk.
  Proof.
    move=> arr_seq tsk PERIODIC j j' NOT_EQ ARR_j ARR_j' TSK_j TSK_j' ORDER.
    rewrite /task_min_inter_arrival_time /periodic_as_sporadic.
    have PERIOD_MULTIPLE:  exists n, n > 0 /\ job_arrival j' =  (n * task_period tsk) + job_arrival j
        by apply PERIODIC => //.
    move: PERIOD_MULTIPLE => [n [GT0 ->]].
    rewrite addnC leq_add2r.
    by apply leq_pmull.
  Qed.

  (** For convenience, we state these obvious correspondences also at the level
      of entire task sets. *)
  Remark valid_periods_are_valid_inter_arrival_times:
    forall ts, valid_periods ts -> valid_taskset_inter_arrival_times ts.
  Proof. trivial. Qed.

  Remark periodic_task_sets_respect_sporadic_task_model:
    forall ts arr_seq,
      taskset_respects_periodic_task_model ts arr_seq ->
      taskset_respects_sporadic_task_model ts arr_seq.
  Proof.
    move=> ? ? PERIODIC ? ?.
    apply periodic_task_respects_sporadic_task_model.
    by apply PERIODIC.
  Qed.

End PeriodicTasksAsSporadicTasks.
