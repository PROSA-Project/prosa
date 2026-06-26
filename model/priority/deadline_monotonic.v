Require Export prosa.model.priority.classes.

(** * Deadline-Monotonic Fixed-Priority Policy *)

(** We define what it means for an abstract fixed-priority policy to behave as
    deadline-monotonic. *)
Section DMPolicy.

  (** Consider tasks with relative deadlines. *)
  Context {Task : TaskType} `{TaskDeadline Task}.

  (** A fixed-priority policy is deadline-monotonic if it assigns higher
      priority to tasks with shorter relative deadlines. *)
  Definition policy_is_DM (FP : FP_policy Task) :=
    forall tsk1 tsk2,
      hep_task tsk1 tsk2 = (task_deadline tsk1 <= task_deadline tsk2).

End DMPolicy.
