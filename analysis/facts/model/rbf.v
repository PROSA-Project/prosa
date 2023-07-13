Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.facts.model.arrival_curves.
Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.definitions.request_bound_function.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.util.tactics.

(** * Facts about Request Bound Functions (RBFs) *)

(** In this file, we prove some lemmas about request bound functions. *)

(** ** RBF is a Bound on Workload *)

(** First, we show that a task's RBF is indeed an upper bound on its
    workload. *)
Section ProofWorkloadBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... any schedule corresponding to this arrival sequence, ... *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... and an FP policy that indicates a higher-or-equal priority relation. *)
  Context `{FP_policy Task}.

  (** Further, consider a task set [ts]... *)
  Variable ts : seq Task.

  (** ... and let [tsk] be any task in [ts]. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Assume that the job costs are no larger than the task costs ... *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** ... and that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let [max_arrivals] be any arrival bound for task-set [ts]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_is_arrival_bound : taskset_respects_max_arrivals arr_seq ts.

  (** Next, recall the notions of total workload of jobs... *)
  Let total_workload t1 t2 := workload_of_jobs predT (arrivals_between arr_seq t1 t2).

  (** ... and the workload of jobs of the same task as job j. *)
  Let task_workload t1 t2 :=
    workload_of_jobs (job_of_task tsk) (arrivals_between arr_seq t1 t2).

  (** Finally, let us define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let total_rbf := total_request_bound_function ts.
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.


  (** In this section, we prove that the workload of all jobs is
      no larger than the request bound function. *)
  Section WorkloadIsBoundedByRBF.

    (** Consider any time [t] and any interval of length [Δ]. *)
    Variable t : instant.
    Variable Δ : instant.

    (** First, we show that workload of task [tsk] is bounded by the number of
        arrivals of the task times the cost of the task. *)
    Lemma task_workload_le_num_of_arrivals_times_cost:
      task_workload t (t + Δ)
      <= task_cost tsk * number_of_task_arrivals arr_seq tsk t (t + Δ).
    Proof.
      rewrite /task_workload /workload_of_jobs/ number_of_task_arrivals
              /task_arrivals_between -big_filter -sum1_size big_distrr big_filter.
      destruct (task_arrivals_between arr_seq tsk t (t + Δ)) eqn:TASK.
      { unfold task_arrivals_between in TASK.
        by rewrite -big_filter !TASK !big_nil. }
      { rewrite //= big_filter big_seq_cond [in X in _ <= X]big_seq_cond.
        apply leq_sum.
        move => j' /andP [IN TSKj'].
        rewrite muln1.
        move: TSKj' => /eqP TSKj'; rewrite -TSKj'.
        apply H_valid_job_cost.
        by apply in_arrivals_implies_arrived in IN. }
    Qed.

    (** As a corollary, we prove that workload of task is no larger the than
        task request bound function. *)
    Corollary task_workload_le_task_rbf:
      task_workload t (t + Δ) <= task_rbf Δ.
    Proof.
      eapply leq_trans; first by apply task_workload_le_num_of_arrivals_times_cost.
      rewrite leq_mul2l; apply/orP; right.
      rewrite -{2}[Δ](addKn t).
      by apply H_is_arrival_bound; last rewrite leq_addr.
    Qed.

    (** Next, we prove that total workload of tasks is no larger than the total
        request bound function. *)
    Lemma total_workload_le_total_rbf:
      total_workload t (t + Δ) <= total_rbf Δ.
    Proof.
      set l := arrivals_between arr_seq t (t + Δ).
      apply (@leq_trans (\sum_(tsk' <- ts) (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0))).
      { rewrite /total_workload.
        have EXCHANGE := exchange_big_dep predT.
        rewrite EXCHANGE //=; clear EXCHANGE.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)) /=.
        - by rewrite eq_refl; apply leq_addr.
        - by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset. }
      apply leq_sum_seq; intros tsk0 INtsk0 HP0.
      apply (@leq_trans (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + Δ)))).
      { rewrite -sum1_size big_distrr /= big_filter -/l /workload_of_jobs muln1.
        apply leq_sum_seq => j0 IN0 /eqP <-.
        apply H_valid_job_cost.
        by apply in_arrivals_implies_arrived in IN0. }
      { rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[Δ](addKn t).
        by apply H_is_arrival_bound; last rewrite leq_addr. }
    Qed.

    (** Next, we consider any job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_job_of_tsk : job_of_task tsk j.

    (** We prove that the sum of job cost of jobs whose corresponding
        task satisfies a predicate [pred] is bounded by the RBF of
        these tasks. *)
    Lemma sum_of_jobs_le_sum_rbf :
      forall (pred : pred Task),
        \sum_(j' <- arrivals_between arr_seq t (t + Δ) | pred (job_task j'))
         job_cost j' <=
          \sum_(tsk' <- ts| pred tsk')
           task_request_bound_function tsk' Δ.
    Proof.
      move => pred.
      apply (@leq_trans (\sum_(tsk' <- filter pred ts)
                           (\sum_(j' <-  arrivals_between arr_seq t (t + Δ)
                                 | job_task j' == tsk') job_cost j'))).
      - move: (H_job_of_tsk) => /eqP TSK.
        rewrite [X in _ <= X]big_filter.
        set P := fun x => pred (job_task x).
        rewrite (exchange_big_dep P) //=; last by rewrite /P; move => ???/eqP->.
        rewrite  /P /workload_of_jobs big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)).
        + by rewrite HP0 andTb eq_refl; apply leq_addr.
        + by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset.
      - rewrite big_filter.
        apply leq_sum_seq => tsk0 INtsk0 HP0.
        apply (@leq_trans (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + Δ)))).
        + rewrite -sum1_size big_distrr /= big_filter /workload_of_jobs.
          rewrite  muln1  /arrivals_between /arrival_sequence.arrivals_between.
          apply leq_sum_seq; move => j0 IN0 /eqP EQ.
          by rewrite -EQ; apply H_valid_job_cost; apply in_arrivals_implies_arrived in IN0.
        + rewrite leq_mul2l; apply/orP; right.
          rewrite -{2}[Δ](addKn t).
          by apply H_is_arrival_bound; last by rewrite leq_addr.
    Qed.

    (** Using lemma [sum_of_jobs_le_sum_rbf], we prove that the
        workload of higher-or-equal priority jobs (w.r.t. task [tsk])
        is no larger than the total request-bound function of
        higher-or-equal priority tasks. *)
    Lemma hep_workload_le_total_hep_rbf :
      workload_of_hep_jobs arr_seq j t (t + Δ) <= total_hep_rbf Δ.
    Proof.
      rewrite /workload_of_hep_jobs /workload_of_jobs /total_hep_rbf /total_hep_request_bound_function_FP.
      rewrite /another_task_hep_job /hep_job /FP_to_JLFP.
      set (pred_task tsk_other := hep_task tsk_other tsk).
      rewrite (eq_big (fun j=> pred_task (job_task j)) job_cost) //;
              last by move=> j'; rewrite /pred_task; move: H_job_of_tsk => /eqP ->.
      erewrite (eq_big pred_task); [|by done|by move=> tsk'; eauto].
      by apply: sum_of_jobs_le_sum_rbf.
    Qed.

  End WorkloadIsBoundedByRBF.

End ProofWorkloadBound.

(** ** RBF Properties *)
(** In this section, we prove simple properties and identities of RBFs. *)
Section RequestBoundFunctions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent:
    consistent_arrival_times arr_seq.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts] [max_arrival tsk] is (1) an arrival
      bound of [tsk], and (2) it is a monotonic function that equals 0
      for the empty interval [Δ = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_arrival_curve (max_arrivals tsk).
  Hypothesis H_is_arrival_curve : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.

  (** We prove that [task_rbf 0] is equal to [0]. *)
  Lemma task_rbf_0_zero:
    task_rbf 0 = 0.
  Proof.
    rewrite /task_rbf /task_request_bound_function.
    apply/eqP; rewrite muln_eq0; apply/orP; right; apply/eqP.
    by move: H_valid_arrival_curve => [T1 T2].
  Qed.

  (** We prove that [task_rbf] is monotone. *)
  Lemma task_rbf_monotone:
    monotone leq task_rbf.
  Proof.
    rewrite /monotone; intros ? ? LE.
    rewrite /task_rbf /task_request_bound_function leq_mul2l.
    apply/orP; right.
    by move: H_valid_arrival_curve => [_ T]; apply T.
  Qed.


  (** In the following, we assume that [tsk] has a positive cost ... *)
  Hypothesis H_positive_cost : 0 < task_cost tsk.

  (** ... and [max_arrivals tsk ε] is positive. *)
  Hypothesis H_arrival_curve_positive : max_arrivals tsk ε > 0.

  (** Then we prove that [task_rbf] at [ε] is greater than or equal to the task's WCET. *)
  Lemma task_rbf_1_ge_task_cost:
    task_rbf ε >= task_cost tsk.
  Proof.
    have ALT: forall n, n = 0 \/ n > 0 by clear; intros n; destruct n; [left | right].
    specialize (ALT (task_cost tsk)); destruct ALT as [Z | POS]; first by rewrite Z.
    rewrite -[task_cost tsk]muln1 /task_rbf /task_request_bound_function.
    by rewrite leq_pmul2l //=.
  Qed.

  (** As a corollary, we prove that the [task_rbf] at any point [A] greater than
      [0] is no less than the task's WCET. *)
  Lemma task_rbf_ge_task_cost:
    forall A,
      A > 0 ->
      task_rbf A >= task_cost tsk.
  Proof.
    case => // A GEQ.
    apply: (leq_trans task_rbf_1_ge_task_cost).
    exact: task_rbf_monotone.
  Qed.

  (** Then, we prove that [task_rbf] at [ε] is greater than [0]. *)
  Lemma task_rbf_epsilon_gt_0 : 0 < task_rbf ε.
  Proof.
    apply leq_trans with (task_cost tsk) => [//|].
    exact: task_rbf_1_ge_task_cost.
  Qed.

  (** Consider a set of tasks [ts] containing the task [tsk]. *)
  Variable ts : seq Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Next, we prove that cost of [tsk] is less than or equal to the
      [total_request_bound_function]. *)
  Lemma task_cost_le_sum_rbf :
    forall t,
      t > 0 ->
      task_cost tsk <= total_request_bound_function ts t.
  Proof.
    case=> [//|t] GE.
    eapply leq_trans; first exact: task_rbf_1_ge_task_cost.
    rewrite /total_request_bound_function.
    erewrite big_rem; last by exact H_tsk_in_ts.
    apply leq_trans with (task_request_bound_function tsk t.+1); last by apply leq_addr.
    by apply task_rbf_monotone.
  Qed.

End RequestBoundFunctions.


(** ** Monotonicity of the Total RBF *)

(** In the following section, we note some trivial facts about the monotonicity
    of various total RBF variants. *)
Section TotalRBFMonotonic.

  (** Consider a set of tasks characterized by WCETs and arrival curves. *)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}.
  Variable ts : seq Task.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** We observe that the total RBF is monotonically increasing. *)
  Lemma total_rbf_monotone :
    monotone leq (total_request_bound_function ts).
  Proof. by apply: sum_leq_mono => tsk IN; apply: task_rbf_monotone. Qed.

  (** Furthermore, for any fixed-priority policy, ... *)
  Context `{FP_policy Task}.

  (** ... the total RBF of higher- or equal-priority tasks is also monotonic, ... *)
  Lemma total_hep_rbf_monotone :
    forall tsk,
      monotone leq (total_hep_request_bound_function_FP ts tsk).
  Proof.
    move=> tsk.
    apply: sum_leq_mono => tsk' IN.
    exact: task_rbf_monotone.
  Qed.

  (** ... as is the variant that excludes the reference task. *)
  Lemma total_ohep_rbf_monotone :
    forall tsk,
      monotone leq (total_ohep_request_bound_function_FP ts tsk).
  Proof.
    move=> tsk.
    apply: sum_leq_mono => tsk' IN.
    exact: task_rbf_monotone.
  Qed.

End TotalRBFMonotonic.

(** ** RBFs Equal to Zero for Duration ε *)

(** In the following section, we derive simple properties that follow in
    the pathological case of an RBF that yields zero for duration ε. *)
Section DegenerateTotalRBFs.

  (** Consider a set of tasks characterized by WCETs and arrival curves ... *)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}.
  Variable ts : seq Task.

  (** ... and any consistent arrival sequence of valid jobs of these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent: consistent_arrival_times arr_seq.
  Hypothesis H_valid_job_cost: arrivals_have_valid_job_costs arr_seq.

  (** Suppose the arrival curves are correct. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve :  taskset_respects_max_arrivals arr_seq ts.

  (** Consider any valid schedule corresponding to this arrival sequence. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Hypothesis H_jobs_from_arr_seq : jobs_come_from_arrival_sequence sched arr_seq.

  (** First, we observe that, if a task's RBF is zero for a duration [ε], then it
      trivially has a response-time bound of zero. *)
  Lemma pathological_rbf_response_time_bound :
    forall tsk,
      tsk \in ts ->
      task_request_bound_function tsk ε = 0 ->
      task_response_time_bound arr_seq sched tsk 0.
  Proof.
    move=> tsk IN ZERO j ARR TASK.
    rewrite /job_response_time_bound/completed_by.
    move: ZERO. rewrite /task_request_bound_function => /eqP.
    rewrite muln_eq0 => /orP [/eqP COST|/eqP NEVER].
    { apply: leq_trans.
      - by apply: H_valid_job_cost.
      - move: TASK. rewrite /job_of_task => /eqP ->.
        by rewrite COST. }
    { exfalso.
      have: 0 < max_arrivals tsk ε
        by apply: (non_pathological_max_arrivals tsk arr_seq _ j).
      by rewrite NEVER. }
  Qed.

  (** Second, given a fixed-priority policy with reflexive priorities, ... *)
  Context {FP : FP_policy Task}.
  Hypothesis H_reflexive : reflexive_task_priorities FP.

  (** ... if the total RBF of all equal- and higher-priority tasks is zero, then
      the reference task's response-time bound is also trivially zero. *)
  Lemma pathological_total_hep_rbf_response_time_bound :
    forall tsk,
      tsk \in ts ->
      total_hep_request_bound_function_FP ts tsk ε = 0 ->
      task_response_time_bound arr_seq sched tsk 0.
  Proof.
    move=> tsk IN ZERO j ARR TASK.
    apply: pathological_rbf_response_time_bound; eauto.
    apply /eqP.
    move: ZERO => /eqP; rewrite sum_nat_eq0_nat => /allP; apply.
    rewrite mem_filter; apply /andP; split => //.
  Qed.

  (** Thus we we can prove any response-time bound from such a pathological
      case, which is useful to eliminate this case in higher-level analyses. *)
  Corollary pathological_total_hep_rbf_any_bound :
    forall tsk,
      tsk \in ts ->
      total_hep_request_bound_function_FP ts tsk ε = 0 ->
      forall R,
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> tsk IN ZERO R.
    move: (pathological_total_hep_rbf_response_time_bound tsk IN ZERO).
    rewrite /task_response_time_bound/job_response_time_bound => COMP j INj TASK.
    apply: completion_monotonic; last by apply: COMP.
    by lia.
  Qed.

End DegenerateTotalRBFs.

(** In this section, we establish results about the task-wise partitioning of
    total RBFs of multiple tasks. *)
Section FP_RBF_partitioning.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType} `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks, where each task has
      a cost and an associated arrival curve. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{MaxArrivals Task}.

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation. *)
  Context `{FP_policy Task}.

  (** Consider a task set ts... *)
  Variable ts : seq Task.

  (** ...and let [tsk] be any task that serves as the reference point for
     "higher or equal priority" (usually, but not necessarily, from [ts]). *)
  Variable tsk : Task.

  (** We establish that the bound on the total workload due to
      higher-or-equal-priority tasks can be partitioned task-wise.
      In other words, it is equal to the sum of the bound on the
      total workload due to higher-priority tasks and the bound on
      the total workload due to equal- priority tasks. *)
  Lemma hep_rbf_taskwise_partitioning :
    forall L,
      total_hep_request_bound_function_FP ts tsk L
      = total_hp_request_bound_function_FP ts tsk L
        + total_ep_request_bound_function_FP ts tsk L.
  Proof.
    move=> L; apply sum_split_exhaustive_mutually_exclusive_preds => t.
    - by rewrite -andb_orr orNb Bool.andb_true_r.
    - rewrite !negb_and; case: (hep_task _ _) =>//=.
      by case: (hep_task _ _)=>//.
  Qed.

End FP_RBF_partitioning.

