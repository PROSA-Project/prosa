Require Export prosa.model.task.arrival.periodic.

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

  (** ... and their corresponding jobs from a consistent arrival sequence with
      non-duplicate arrivals ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

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
    forall tsk, valid_period tsk ->
           respects_periodic_task_model arr_seq tsk ->
           respects_sporadic_task_model arr_seq tsk.
  Proof.
    intros tsk VALID_PERIOD H_PERIODIC j1 j2 NEQ ARR ARR' TSK TSK' ARR_LT.
    rewrite /task_min_inter_arrival_time /periodic_as_sporadic.
    have IND_LT : job_index arr_seq j1 < job_index arr_seq j2.
    { rewrite -> diff_jobs_iff_diff_indices in NEQ => //; eauto; last by rewrite TSK.
      move_neq_up IND_LTE; move_neq_down ARR_LT.
      specialize (H_PERIODIC j1); feed_n 3 H_PERIODIC => //; try by lia.
      move : H_PERIODIC => [pj [ARR_PJ [IND_PJ [TSK_PJ PJ_ARR]]]].
      have JB_IND_LTE : job_index arr_seq j2 <= job_index arr_seq pj by lia.
      apply index_lte_implies_arrival_lte in JB_IND_LTE => //; try by rewrite TSK_PJ.
      rewrite PJ_ARR.
      have POS_PERIOD : task_period tsk > 0 by auto.
      by lia. }
    specialize (H_PERIODIC j2); feed_n 3 H_PERIODIC => //; try by lia.
    move: H_PERIODIC => [pj [ARR_PJ [IND_PJ [TSK_PJ PJ_ARR]]]].
    have JB_IND_LTE : job_index arr_seq j1 <= job_index arr_seq pj by lia.
    apply index_lte_implies_arrival_lte in JB_IND_LTE => //; try by rewrite TSK_PJ.
    by rewrite PJ_ARR; lia.
  Qed.

  (** For convenience, we state these obvious correspondences also at the level
      of entire task sets. *)

  (** First, we show that all tasks in a task set with valid periods
      also have valid min inter-arrival times. *)
  Remark valid_periods_are_valid_inter_arrival_times :
    forall ts, valid_periods ts -> valid_taskset_inter_arrival_times ts.
  Proof. trivial. Qed.

  (** Second, we show that each task in a periodic task set respects
      the sporadic task model. *)
  Remark periodic_task_sets_respect_sporadic_task_model :
    forall ts,
      valid_periods ts ->
      taskset_respects_periodic_task_model arr_seq ts ->
      taskset_respects_sporadic_task_model ts arr_seq.
  Proof.
    intros ts VALID_PERIODS H_PERIODIC tsk TSK_IN.
    specialize (H_PERIODIC tsk TSK_IN).
    exact: periodic_task_respects_sporadic_task_model.
  Qed.

End PeriodicTasksAsSporadicTasks.

(** We add the lemmas into the "Hint Database" basic_rt_facts so that
    they become available for proof automation. *)
Global Hint Resolve
  periodic_task_respects_sporadic_task_model
  valid_period_is_valid_inter_arrival_time
  valid_periods_are_valid_inter_arrival_times
  periodic_task_sets_respect_sporadic_task_model
  : basic_rt_facts.
