Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.definitions.demand_bound_function.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.workload.

(** * Facts about the Demand Bound Function (DBF) *)
(** In this file we establish some properties of DBFs. *)
Section ProofDemandBoundDefinition.
  (** Consider any type of task with relative deadlines and any type of jobs associated with such tasks. *)
  Context {Task : TaskType} `{TaskDeadline Task}
          {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Consider a valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** First, we establish a relation between a task's arrivals in a given interval and
      those arrivals that also have a deadline contained within the given interval. *)
  Lemma task_arrivals_with_deadline_within_eq :
    forall (tsk : Task) (t : instant) (delta : duration),
      task_arrivals_with_deadline_within arr_seq tsk t (t + delta)
      = task_arrivals_between arr_seq tsk t (t + (delta - (task_deadline tsk -1))).
  Proof.
    move=> tsk t delta.
    rewrite /task_arrivals_with_deadline_within/job_deadline
      /job_deadline_from_task_deadline/task_arrivals_between.
    rewrite (@arrivals_between_cat _ _ _ (t + (delta - (task_deadline tsk - 1)))); try lia.
    rewrite filter_cat.
    rewrite (@eq_in_filter _ _ (fun j => job_of_task tsk j)).
    { set nilS := [seq j <- arrivals_between arr_seq t (t + (delta - (task_deadline tsk - 1))) | job_of_task tsk j].
      rewrite -[in RHS](@cats0 _ nilS).
      apply /eqP; rewrite eqseq_cat => //=.
      apply /andP; split => //=.
      rewrite (@eq_in_filter _ _ pred0);
        first by rewrite filter_pred0.
      move=> j IN.
      have [/eqP ->|] := boolP (job_of_task tsk j) => //=.
      have GEQ: job_arrival j >= t + (delta - (task_deadline tsk - 1))
        by apply: job_arrival_between_ge.
      have LT := (arrivals_between_nonempty _ _ _ _ IN).
      by lia. }
    { move=> j IN.
      have [/eqP ->|] := boolP (job_of_task tsk j) => //=.
      have -> : (job_arrival j + task_deadline tsk  <= t + delta) => //.
      have LT := (arrivals_between_nonempty _ _ _ _ IN).
      have LTj: job_arrival j < t + (delta - (task_deadline tsk - 1))
        by apply: job_arrival_between_lt.
      by lia. }
  Qed.

  (** As a corollary, we also show a much more useful result that arises when we count these jobs. *)
  Corollary num_task_arrivals_with_deadline_within_eq :
    forall (tsk : Task) (t : instant) (delta : duration),
      number_of_task_arrivals_with_deadline_within arr_seq tsk t (t + delta)
      = number_of_task_arrivals arr_seq tsk t (t + (delta - (task_deadline tsk - 1))).
  Proof.
    move=> tsk t delta.
    rewrite /number_of_task_arrivals_with_deadline_within
      /number_of_task_arrivals.
    by rewrite task_arrivals_with_deadline_within_eq.
  Qed.

  (** In the following, assume we are given a valid WCET bound for each task. *)
  Context `{TaskCost Task} `{JobCost Job}.
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** A task's _demand_ in a given interval is the sum of the execution costs (i.e., the workload) of the task's jobs
      that both arrive in the interval and have a deadline within it. *)
  Definition task_demand_within (tsk :  Task) (t1 t2 : instant)  :=
    let
      causing_demand (j : Job) := (job_deadline j <= t2) && (job_of_task tsk j)
    in
      workload_of_jobs causing_demand (arrivals_between arr_seq t1 t2).

  (** Consider a task set [ts]. *)
  Variable ts : seq Task.

  (** Let [max_arrivals] be any arrival curve. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_is_arrival_bound : taskset_respects_max_arrivals arr_seq ts.

  (** The task's processor demand  [task_demand_within] is upper-bounded by the task's DBF [task_demand_bound_function]. *)
  Lemma task_demand_within_le_task_dbf :
    forall (tsk : Task) t delta,
      tsk \in ts ->
      task_demand_within tsk t (t + delta) <= task_demand_bound_function tsk delta.
  Proof.
    move=> tsk t delta IN0.
    have ->: task_demand_within tsk t (t + delta)
             = task_workload tsk (arrivals_between arr_seq t (t + (delta - (task_deadline tsk - 1)))).
    { rewrite /task_demand_within/task_workload/workload_of_jobs.
      under eq_bigl do rewrite andbC.
      rewrite -big_filter.
      move: (task_arrivals_with_deadline_within_eq tsk t delta).
      rewrite /task_arrivals_with_deadline_within/task_arrivals_between => ->.
      by rewrite big_filter. }
    rewrite /task_demand_bound_function/task_workload.
    by apply: rbf_spec.
  Qed.

  (** We also prove that [task_demand_within] is less than shifted RBF. *)
  Corollary task_demand_within_le_task_rbf_shifted :
    forall (tsk : Task) t delta,
      tsk \in ts ->
      task_demand_within tsk t (t + delta) <= task_request_bound_function tsk (delta - (task_deadline tsk - 1)).
  Proof.
    move=> tsk t delta IN0.
    by apply task_demand_within_le_task_dbf.
  Qed.

  (** Next, we define the total workload of all jobs that arrives in a given interval that also have a
      deadline within the interval. *)
  Definition total_demand_within (t1 t2 : instant) :=
    let
      causing_demand (j : Job) := job_deadline j <= t2
    in
      workload_of_jobs causing_demand (arrivals_between arr_seq t1 t2).

  (** Assume that all jobs come from the task set [ts]. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Finally we establish that [total_demand_within] is bounded by [total_demand_bound_function]. *)
  Lemma total_demand_within_le_total_dbf :
    forall (t : instant) (delta : duration),
      total_demand_within t (t + delta) <= total_demand_bound_function ts delta.
  Proof.
    move=> t delta.
    apply (@leq_trans (\sum_(tsk <- ts) task_demand_within tsk t (t + delta))).
    { apply workload_of_jobs_le_sum_over_partitions => //.
      move=> j IN; by apply in_arrivals_implies_arrived in IN. }
    rewrite /total_demand_bound_function.
    apply leq_sum_seq => tsk' tsk_IN P_tsk.
    by apply task_demand_within_le_task_dbf.
  Qed.

  (** As a corollary, we also note that [total_demand_within] is less than
      the sum of each task's shifted RBF. *)
  Corollary total_demand_within_le_sum_task_rbf_shifted :
    forall (t : instant ) (delta : instant),
      total_demand_within t (t + delta)
      <= \sum_(tsk <- ts) task_request_bound_function tsk (delta - (task_deadline tsk - 1)).
  Proof.
    move=> t delta.
    by apply total_demand_within_le_total_dbf.
  Qed.

End ProofDemandBoundDefinition.
