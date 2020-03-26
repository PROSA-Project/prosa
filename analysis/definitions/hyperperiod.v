Require Export prosa.model.task.arrival.periodic.
Require Export prosa.util.lcmseq.
From mathcomp Require Import div.

(** In this file we define the notion of a hyperperiod for periodic tasks. *)
Section Hyperperiod.

  (** Consider periodic tasks. *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** Consider any task set [ts]... *)
  Variable ts : TaskSet Task.

  (** ... and any task [tsk] that belongs to this task set. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** The hyperperiod of a task set is defined as the least common multiple
   (LCM) of the periods of all tasks in the task set. **)
  Definition hyperperiod : duration := lcml (map task_period ts).        

  (** Consequently, a task set's hyperperiod is an integral multiple
   of each task's period in the task set. **)
  Lemma hyperperiod_int_mult_of_any_task : 
    exists k, hyperperiod = k * task_period tsk.
  Proof.
    apply lcm_seq_is_mult_of_all_ints.
    apply map_f.
    by apply H_tsk_in_ts.
  Qed.

End Hyperperiod.

