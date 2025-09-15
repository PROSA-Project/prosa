Require Export prosa.analysis.definitions.schedulability.

(** * Tardiness *)

(** In the following section we define the notion of bounded tardiness,
    i.e., an upper-bound on the difference between the response time of
    any job of a task and its relative deadline. *)
Section Tardiness.

  (** Consider any type of tasks and its deadline, ... *)
  Context {Task : TaskType}.
  Context `{TaskDeadline Task}.

  (** ... any type of jobs associated with these tasks, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobTask Job Task}.

  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.

  (** Further, consider any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.

  (** ...and any schedule of these jobs. *)
  Variable sched : schedule PState.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk : Task.

  (** Then, we say that B is a tardiness bound of [tsk] in this schedule ... *)
  Variable B : duration.

  (** ... iff any job [j] of [tsk] in the arrival sequence has
         completed no more that [B] time units after its deadline. *)
  Definition task_tardiness_is_bounded arr_seq sched tsk B :=
    task_response_time_bound arr_seq sched tsk (task_deadline tsk + B).

End Tardiness.
