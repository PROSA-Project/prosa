Require Export prosa.model.priority.classes.
Require Export prosa.model.task.arrival.sporadic.

(** * Rate-Monotonic Fixed-Priority Policy *)

(** We define what it means for an abstract fixed-priority policy to behave as
    rate-monotonic. *)
Section RMPolicy.

  (** Consider sporadic tasks. *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** A fixed-priority policy is rate-monotonic if it assigns higher priority
      to tasks with shorter minimum inter-arrival times, or periods. *)
  Definition policy_is_RM (FP : FP_policy Task) :=
    forall tsk1 tsk2,
      hep_task tsk1 tsk2
      = (task_min_inter_arrival_time tsk1 <= task_min_inter_arrival_time tsk2).

End RMPolicy.
