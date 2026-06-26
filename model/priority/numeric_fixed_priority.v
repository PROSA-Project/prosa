Require Export prosa.model.priority.classes.

(** * Numeric Fixed Task Priorities *)

(** We define the notion of arbitrary numeric fixed task priorities, i.e., tasks
    are prioritized in order of user-provided numeric priority values. *)

(** First, we define a new task parameter [task_priority] that maps each task
    to a numeric priority value. *)
Class TaskPriority (Task : TaskType) := { task_priority : Task -> nat }.

(** Based on this parameter, we consider two possible interpretations. In the
    first interpretation, a lower numeric value indicates lower priority, while
    in the other interpretation, a lower numeric value indicates higher
    priority. Both interpretations can be found in practice and in the
    literature. For example, Linux uses "higher numeric value <-> higher
    priority", whereas many papers in the academic literature assume "lower
    numeric value <-> higher priority". *)

Section NumericFPInterpretations.

  (** Consider tasks with numeric priorities. *)
  Context {Task : TaskType} `{TaskPriority Task}.

  (** A fixed-priority policy is ascending numeric FP if it assigns higher
      priority to tasks with higher numeric [task_priority] values. *)
  Definition policy_is_numeric_FP_ascending (FP : FP_policy Task) :=
    forall tsk1 tsk2,
      hep_task tsk1 tsk2 = (task_priority tsk1 >= task_priority tsk2).

  (** A fixed-priority policy is descending numeric FP if it assigns higher
      priority to tasks with lower numeric [task_priority] values. *)
  Definition policy_is_numeric_FP_descending (FP : FP_policy Task) :=
    forall tsk1 tsk2,
      hep_task tsk1 tsk2 = (task_priority tsk1 <= task_priority tsk2).

End NumericFPInterpretations.
