Require Export prosa.model.task.arrivals.

(** In this file we provide basic properties related to tasks on arrival sequences. *)
Section TaskArrivals.

  (** Consider any type of job associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** We show that the number of arrivals of task can be split into disjoint intervals. *) 
  Lemma num_arrivals_of_task_cat:
    forall t t1 t2,
      t1 <= t <= t2 ->
      number_of_task_arrivals arr_seq tsk t1 t2 =
      number_of_task_arrivals arr_seq tsk t1 t + number_of_task_arrivals arr_seq tsk t t2.
  Proof.
    move => t t1 t2 /andP [GE LE].
    rewrite /number_of_task_arrivals /task_arrivals_between /arrivals_between. 
    rewrite (@big_cat_nat _ _ _ t) //=.
      by rewrite filter_cat size_cat.
  Qed.

End TaskArrivals.