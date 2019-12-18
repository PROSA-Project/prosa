Require Export prosa.model.task.concept.

(** * The Sporadic Task Model *)

(** In the following, we define the arrival process commonly known as the
    sporadic task model, where jobs may arrive at any time provided any two
    jobs of a task are separated by at least the minimum inter-arrival time (or
    period) of the task. *)


(** ** Task Parameter for the Sporadic Task Model *)

(** Under the sporadic task model, each task is characterized by its minimum
    inter-arrival time, which we denote as [task_min_inter_arrival_time]. *)

Class SporadicModel (Task : TaskType) :=
  task_min_inter_arrival_time : Task -> duration.

(** ** Model Validity *)

(** Next, we define the semantics of the sporadic task model. *)
Section ValidSporadicTaskModel.
  (** Consider any type of sporadic tasks. *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** A valid sporadic task should have a non-zero minimum inter-arrival
      time. *)
  Definition valid_task_min_inter_arrival_time tsk :=
    task_min_inter_arrival_time tsk > 0.

  (** Further, in the context of a set of such tasks, ... *)
  Variable ts : TaskSet Task.

  (** ... every task in the set should have a valid inter-arrival time. *)
  Definition valid_taskset_inter_arrival_times :=
    forall tsk : Task,
      tsk \in ts -> valid_task_min_inter_arrival_time tsk.

  (** Next, consider any type of jobs stemming from these tasks ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... and an arbitrary arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that a task respects the sporadic task model if the arrivals of
      its jobs in the arrival sequence are appropriately spaced in time. *)
  Definition respects_sporadic_task_model (tsk : Task) :=
    forall (j j': Job),
      (** Given two different jobs j and j' ... *)
      j <> j' ->
      (** ...that belong to the arrival sequence... *)
      arrives_in arr_seq j ->
      arrives_in arr_seq j' ->
      (** ... and that stem from the given task, ... *)
      job_task j = tsk ->
      job_task j' = tsk ->
      (** ... if the arrival of j precedes the arrival of j' ...,  *)
      job_arrival j <= job_arrival j' ->
      (** then the arrival of j and the arrival of j' are separated by at least
          one period. *)
      job_arrival j' >= job_arrival j + task_min_inter_arrival_time tsk.

  (** Based on the above definition, we define the sporadic task model as
      follows. *)
  Definition taskset_respects_sporadic_task_model :=
    forall tsk, tsk \in ts -> respects_sporadic_task_model tsk.

End ValidSporadicTaskModel.
