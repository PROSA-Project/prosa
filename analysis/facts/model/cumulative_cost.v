Require Export prosa.model.task.cumulative_cost.
Require Export prosa.analysis.facts.model.task_arrivals.

(** * Facts About Cumulative Task Costs *)

(** In this file, we establish basic consequences of cumulative task-cost
    validity. In particular, a cumulative bound for singleton blocks implies
    the ordinary scalar job-cost validity assumption. *)

(** We first establish some basic facts about consecutive arrivals of a task. *)
Section ConsecutiveArrivals.

  (** Consider any type of tasks and their jobs. *)
  Context {Task : TaskType}.
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Consider any job arrival sequence with consistent arrival times. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.

  (** Any arriving job [j] is trivially a "consecutive" block in the arrival
      sequence of [job_task j]. *)
  Lemma arriving_job_is_consecutive_task_arrival :
    forall j,
      arrives_in arr_seq j ->
      consecutive_task_arrivals arr_seq (job_task j) [:: j].
  Proof.
    move=> j ARR.
    set arrivals := task_arrivals_up_to_job_arrival arr_seq j.
    have IN : j \in arrivals
      by apply: arrives_in_task_arrivals_up_to.
    exists (job_arrival j), (take (index j arrivals) arrivals),
      (drop (index j arrivals).+1 arrivals).
    change (arrivals = take (index j arrivals) arrivals
                       ++ [:: j] ++ drop (index j arrivals).+1 arrivals).
    have TAIL : drop (index j arrivals) arrivals
                = [:: j] ++ drop (index j arrivals).+1 arrivals.
    { rewrite /= (@drop_nth _ j); last by rewrite index_mem.
      by rewrite (nth_index j IN). }
    by rewrite -TAIL cat_take_drop.
  Qed.

  (** The arrivals of a given task in any half-open interval are consecutive. *)
  Lemma task_arrivals_between_is_consecutive_task_arrival :
    forall tsk t1 t2,
      t1 <= t2 ->
      consecutive_task_arrivals arr_seq tsk
        (task_arrivals_between arr_seq tsk t1 t2).
  Proof.
    move=> tsk t1 t2 LEQ.
    exists t2, (task_arrivals_before arr_seq tsk t1),
      (task_arrivals_between arr_seq tsk t2 t2.+1).
    rewrite /task_arrivals_up_to /task_arrivals_before
            /task_arrivals_between.
    rewrite (arrivals_between_cat _ 0 t2 t2.+1) //=
            (arrivals_between_cat _ 0 t1 t2) //=.
    by rewrite !filter_cat catA.
  Qed.

End ConsecutiveArrivals.

(** Next, we derive ordinary scalar job-cost validity from cumulative cost
    validity. *)
Section ValidJobCosts.

  (** Consider any type of tasks with cumulative cost bounds ... *)
  Context {Task : TaskType} `{TaskCumulativeCost Task}.

  (** ... and their associated jobs with execution costs and arrival times. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{JobArrival Job}.

  (** Consider any job arrival sequence with consistent arrival times. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.

  (** Let [task_cost] be defined by WCET(1). *)
  #[local] Existing Instance task_cost_from_cumulative_cost.

  (** Given a task that with a valid cumulative cost bound [tsk], every arriving
      job [j] of the task has a valid scalar job cost. *)
  Lemma valid_job_cost_from_cumulative_cost_bound :
    forall tsk,
      respects_task_cumulative_cost arr_seq tsk ->
      forall j,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        valid_job_cost j.
  Proof.
    move=> tsk RESP j ARR TSK.
    rewrite /valid_job_cost /task_cost /=.
    have COST : \sum_(j0 <- [:: j]) job_cost j0
                <= task_cumulative_cost (job_task j) (size [:: j]).
    { move: TSK; rewrite /job_of_task => /eqP TSK; rewrite TSK.
      apply: RESP; rewrite -TSK.
      by apply: arriving_job_is_consecutive_task_arrival. }
    by rewrite big_seq1 in COST.
  Qed.

  (** We next lift the above property to task sets. Consider any given task set
      with valid cumulative execution-time bounds. *)
  Variable ts : seq Task.
  Hypothesis H_bounds_respected : taskset_respects_cumulative_cost_bounds arr_seq ts.

  (** All jobs in an arrival sequence of the task set have valid scalar job
      costs. *)
  Corollary valid_job_costs_from_cumulative_cost_bounds :
    all_jobs_from_taskset arr_seq ts ->
    arrivals_have_valid_job_costs arr_seq.
  Proof.
    move=> FROM j ARR.
    apply: valid_job_cost_from_cumulative_cost_bound => //=.
    by rewrite /job_of_task.
  Qed.

End ValidJobCosts.

(** The trivial cumulative cost [WCET(n) = n * WCET] is valid for every task. *)
Section TrivialCumulativeCostValidity.

  (** Consider any type of tasks with a scalar WCET ... *)
  Context {Task : TaskType} `{ScalarCost : TaskCost Task}.

  (** ... and the induced trivial WCET(n) bound for such tasks. *)
  Let TrivialCumulativeCost := (@task_cost_as_cumulative_cost Task ScalarCost).

  (** The trivial cumulative bound induced by the scalar bound is well
      formed. *)
  Lemma trivial_cumulative_cost_valid :
    forall tsk,
      @valid_task_cumulative_cost Task TrivialCumulativeCost tsk.
  Proof.
    move=> tsk.
    split; first by rewrite /task_cumulative_cost /= mul0n.
    move=> x y LEQ.
    rewrite /task_cumulative_cost /=.
    case: (task_cost tsk) => [|c]; first by rewrite !muln0.
    by rewrite leq_pmul2r.
  Qed.
  (** Next, consider an arrival sequence of the jobs associated with these
      tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.

  (** Ordinary scalar job-cost validity implies that the induced trivial WCET(n)
      bound is respected. *)
  Lemma trivial_cumulative_cost_respected :
    arrivals_have_valid_job_costs arr_seq ->
    forall tsk,
      @respects_task_cumulative_cost Task TrivialCumulativeCost
        Job _ _ arr_seq tsk.
  Proof.
    move=> VALID tsk js [t [prefix [suffix ARR]]].
    rewrite /task_cumulative_cost /= mulnC -sum1_size big_distrr //= muln1.
    apply: leq_sum_seq => j IN _.
    have: j \in task_arrivals_up_to arr_seq tsk t by rewrite ARR !mem_cat IN !orbT.
    rewrite /task_arrivals_up_to => IN'.
    have /eqP <- : job_of_task tsk j by (move: IN'; rewrite mem_filter => /andP [TSK _]).
    by apply/VALID/arrives_in_task_arrivals_implies_arrived.
  Qed.

  (** For automation, we lift the two previous lemmas to task sets. *)
  Variable ts : seq Task.

  (** The induced trivial WCET(n) bound is valid for every task. *)
  Fact taskset_trivial_cumulative_cost_valid :
    taskset_has_valid_cumulative_cost_bounds ts.
  Proof. by move=> tsk IN; apply: trivial_cumulative_cost_valid. Qed.

  (** The induced trivial WCET(n) bound is respected by every task if each
      task's WCET is valid. *)
  Fact taskset_trivial_cumulative_cost_bound_respected :
    arrivals_have_valid_job_costs arr_seq ->
    taskset_respects_cumulative_cost_bounds arr_seq ts.
  Proof. by move=> VALID tsk IN; apply: trivial_cumulative_cost_respected. Qed.

End TrivialCumulativeCostValidity.

(** We add the above lemmas about the induced trivial cost bound into the "Hint
    Database" basic_rt_facts so that they become available for proof
    automation. *)
Global Hint Resolve
  valid_job_cost_from_cumulative_cost_bound
  valid_job_costs_from_cumulative_cost_bounds
  trivial_cumulative_cost_valid
  trivial_cumulative_cost_respected
  taskset_trivial_cumulative_cost_valid
  taskset_trivial_cumulative_cost_bound_respected
  : basic_rt_facts.
