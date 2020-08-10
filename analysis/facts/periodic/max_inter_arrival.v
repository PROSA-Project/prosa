Require Export prosa.analysis.facts.periodic.arrival_separation.

(** ** Periodic Task Model respects the Task Max Inter-Arrival model. *)

(** In this section, we show that the periodic task model 
    respects the task max inter-arrival model (i.e. consecutive jobs 
    of a task are separated at most by a certain duration specified by
    the [task_max_inter_arrival_time] parameter). *)
Section PeriodicTasksRespectMaxInterArrivalModel.
  
  (** Consider any type of periodic tasks, ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.
  
  (** ... any type of jobs associated with the tasks, ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.
  
  (** ... and any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** By using each task's period as its maximum inter-arrival time, ... *)
  Global Instance max_inter_eq_period : TaskMaxInterArrival Task :=
    {
      task_max_inter_arrival_time := task_period
    }.
  
  (** ... we observe that for any task [tsk], 
      [task_max_inter_arrival_time tsk] is positive, ... *)
  Remark valid_period_is_valid_max_inter_arrival_time:
    forall tsk, valid_period tsk -> positive_task_max_inter_arrival_time tsk.
  Proof. trivial. Qed.

  (** ... and show that the periodic model respects the task max inter-arrival model. *)
  Remark periodic_model_respects_max_inter_arrival_model:
    forall tsk,
      valid_period tsk -> 
      respects_periodic_task_model arr_seq tsk ->
      valid_task_max_inter_arrival_time arr_seq tsk.
    Proof.
      intros tsk VALID_PERIOD PERIODIC.
      split; first by apply VALID_PERIOD => //.
      intros j ARR TSK IND.
      specialize (PERIODIC j); feed_n 3 PERIODIC => //. 
      move : PERIODIC => [j' [ARR' [IND' [TSK' ARRJ']]]].
      exists j'; repeat split => //.
      { case: (boolP (j == j')) => [/eqP EQ|NEQ].
        - have EQ_IND : (job_index arr_seq j' = job_index arr_seq j) by apply f_equal => //.
          now exfalso; ssrlia.
        - now apply /eqP. }
      { have NZ_PERIOD : (task_period tsk > 0) by apply VALID_PERIOD.
        rewrite /max_inter_eq_period /task_max_inter_arrival_time ARRJ'. 
        now ssrlia. }
    Qed.
    
End PeriodicTasksRespectMaxInterArrivalModel.
