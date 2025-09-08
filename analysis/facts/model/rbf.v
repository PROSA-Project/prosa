Require Export prosa.model.job.properties.
Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.facts.model.arrival_curves.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.analysis.definitions.request_bound_function.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.util.tactics.
Require Export prosa.analysis.definitions.workload.bounded.

(** * Facts about Request-Bound Functions (RBFs) *)

(** In this file, we prove some lemmas about RBFs. *)

(** ** RBF is a Bound on Workload *)

Section ProofRequestBoundFunction.

  (** Consider any type of tasks characterized by WCETs and arrival curves ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task} `{MaxArrivals Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any schedule corresponding to this arrival sequence. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** In this section, we establish that a task's RBF is indeed an upper bound
      on the task's workload. *)
  Section RBF.

    (** Consider a given task [tsk]. *)
    Variable tsk : Task.

    (** First, as a stepping stone, we observe that any sequence of jobs of the
        task jointly satisfy the task's WCET. *)
    Lemma task_workload_between_bounded :
      forall t1 t2,
        task_workload_between arr_seq tsk t1 t2
        <= task_cost tsk * number_of_task_arrivals arr_seq tsk t1 t2.
    Proof.
      move=> t Δ.
      rewrite /number_of_task_arrivals/task_arrivals_between.
      rewrite /task_workload_between/task_workload/workload_of_jobs -big_filter.
      apply: sum_job_costs_bounded.
      move=> j /[! mem_filter ] /andP [TSK IN]; apply /andP; split => //.
      by apply/H_valid_job_cost/in_arrivals_implies_arrived.
    Qed.

    (** Next, suppose that task [tsk] respects its arrival curve [max_arrivals]. *)
    Hypothesis H_tsk_arrivals_bounded : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

    (** From this assumption, we establish the RBF spec: In any interval of any
        length, the RBF upper-bounds the task's actual workload. *)
    Lemma rbf_spec :
      forall t Δ,
        task_workload_between arr_seq tsk t (t + Δ)
        <= task_request_bound_function tsk Δ.
    Proof.
      move=> t Δ.
      apply: leq_trans; first by apply: task_workload_between_bounded.
      rewrite /task_request_bound_function.
      rewrite leq_mul2l; apply/orP; right.
      rewrite -{2}[Δ](addKn t).
      by apply/H_tsk_arrivals_bounded/leq_addr.
    Qed.

  End RBF.

  (** In this section, we prove a trivial corollary stating that the RBF still
      upper-bounds the workload when considering only a subset of a task's jobs
      (namely those satisfying a filter predicate). *)
  Section SubsetOfJobs.

    (** Consider any predicate [P] on jobs. *)
    Variable P : pred Job.

    (** Consider any task [tsk] that respects its arrival curve [max_arrivals] *)
    Variable tsk : Task.
    Hypothesis H_tsk_arrivals_bounded : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

    (** Assume that all jobs that satisfy [P] come from task [tsk]. *)
    Hypothesis H_jobs_of_tsk : forall j, P j -> job_of_task tsk j.

    (** Trivially, the workload of jobs from task [tsk] that satisfy the
        predicate [P] is bounded by the task's RBF. *)
    Corollary rbf_spec' :
      forall t Δ,
        workload_of_jobs P
          (arrivals_between arr_seq t (t + Δ))
        <= task_request_bound_function tsk Δ.
    Proof.
      move=> t Δ.
      apply: leq_trans; last by apply: rbf_spec.
      rewrite /task_workload_between/task_workload/workload_of_jobs.
      by apply leq_sum_seq_pred.
    Qed.

  End SubsetOfJobs.

  (** Now, consider a task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Assume that all tasks in the task set respect [max_arrivals]. *)
  Hypothesis H_is_arrival_bound : taskset_respects_max_arrivals arr_seq ts.

  (** Next, we prove that total workload is upper-bounded by the total RBF. *)
  Lemma total_workload_le_total_rbf :
    forall t Δ,
      total_workload_between arr_seq t (t + Δ) <= total_request_bound_function ts Δ.
  Proof.
    move=> t Δ.
    apply leq_trans with (n := \sum_(tsk <- ts) task_workload_between arr_seq tsk t (t + Δ)).
    { apply: workload_of_jobs_le_sum_over_partitions => //.
      move=> j IN; by apply in_arrivals_implies_arrived in IN. }
    rewrite /total_request_bound_function.
    apply leq_sum_seq => tsk' tsk_IN ?.
    by apply rbf_spec.
  Qed.

  (** In this section, we prove a more general result about the workload of
      arbitrary sets of jobs. *)
  Section SumRBF.

    (** Consider two predicates, one on jobs and one on tasks. *)
    Variable pred1 : pred Job.
    Variable pred2 : pred Task.

    (** Assume that for all jobs satisfying [pred1], the task it belongs to
        satisfies [pred2]. *)
    Hypothesis H_also_satisfied : forall j, pred1 j -> pred2 (job_task j).

    (** We prove that the workload of all jobs satisfying predicate [pred1] is
        bounded by the sum of task RBFs over tasks that satisfy the predicate
        [pred2]. *)
    Lemma workload_of_jobs_bounded :
      forall t Δ,
        workload_of_jobs (pred1) (arrivals_between arr_seq t (t + Δ))
        <= \sum_(tsk' <- ts | pred2 tsk') task_request_bound_function tsk' Δ.
    Proof.
      move=> t Δ.
      rewrite /workload_of_jobs.
      apply (@leq_trans (\sum_(tsk <- ts | pred2 tsk)
                (\sum_(j <- arrivals_between arr_seq t (t + Δ) | (job_task j == tsk) && (pred1 j))
                    job_cost j))).
      { rewrite (exchange_big_dep pred1) //=;
          last by move=> ? ? ? /andP[].
        rewrite big_seq_cond [X in _ <= X]big_seq_cond.
        rewrite leq_sum //= => j' /andP [IN' Pj'].
        rewrite Pj'.
        under eq_bigl do [rewrite andbA; rewrite andbT].
        rewrite (big_rem (job_task j')) //=;
          last by apply/H_all_jobs_from_taskset/in_arrivals_implies_arrived.
        rewrite (H_also_satisfied _  Pj') eq_refl //=.
        by apply leq_addr. }
      { rewrite leq_sum_seq //=.
        move=> tsk' tsk_in_ts' P_tsk'.
        apply (@leq_trans (\sum_(j <- arrivals_between arr_seq t (t + Δ)
                | job_task j == tsk') job_cost j)).
        - rewrite leq_sum_seq_pred //=.
          by move=> ? ? /andP[].
        - exact: rbf_spec. }
    Qed.

  End SumRBF.


  (** Next, we establish bounds specific to fixed-priority scheduling. *)
  Section FP.

    (** Consider an arbitrary fixed-priority policy ... *)
    Context {FP : FP_policy Task}.

    (** ... and any given task. *)
    Variable tsk : Task.

    (** The [athep_workload_is_bounded] predicate used below allows the workload
        bound to depend on two arguments: the relative offset [A] (w.r.t. the
        beginning of the corresponding busy interval) of a job to be analyzed
        and the length of an interval [Δ]. In the case of FP scheduling, the
        relative offset ([A]) does not play a role and is therefore ignored.

        Let's abbreviate [total_ohep_request_bound_function_FP] such that the
        [A] argument is ignored. *)
    Let total_ohep_rbf (_A Δ : duration) :=
          total_ohep_request_bound_function_FP ts tsk Δ.

    (** We next prove that the higher-or-equal-priority workload of tasks
        different from [tsk] is bounded by [total_ohep_rbf]. *)
    Lemma athep_workload_le_total_ohep_rbf :
      athep_workload_is_bounded arr_seq sched tsk total_ohep_rbf.
    Proof.
      move => j t1 Δ POS TSK _.
      rewrite /workload_of_jobs /total_ohep_request_bound_function_FP.
      rewrite /another_task_hep_job /hep_job /FP_to_JLFP.
      apply: workload_of_jobs_bounded.
      by move: TSK => /eqP ->.
    Qed.

    (** Consider any job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_job_of_tsk : job_of_task tsk j.

    (** Using lemma [workload_of_jobs_bounded], we prove that the
        workload of higher-or-equal priority jobs (w.r.t. task [tsk])
        is no larger than the total request-bound function of
        higher-or-equal priority tasks. *)
    Lemma hep_workload_le_total_hep_rbf :
      forall t Δ,
        workload_of_hep_jobs arr_seq j t (t + Δ)
        <= total_hep_request_bound_function_FP ts tsk Δ.
    Proof.
      move=> t Δ.
      apply workload_of_jobs_bounded.
      rewrite /hep_job /FP_to_JLFP.
      by move: H_job_of_tsk => /eqP <-.
    Qed.

  End FP.

  (** In this section, we show that the total RBF is a bound on higher-or-equal
      priority workload under any JLFP policy. *)
  Section JLFP.

    (** Consider a JLFP policy that indicates a higher-or-equal priority
        relation ... *)
    Context `{JLFP_policy Job}.

    (** ... and any job [j]. *)
    Variable j : Job.

    (** A simple consequence of lemma [hep_workload_le_total_hep_rbf] is that
        the workload of higher-or-equal priority jobs is bounded by the total
        request-bound function. *)
    Corollary hep_workload_le_total_rbf :
      forall t Δ,
        workload_of_hep_jobs arr_seq j t (t + Δ)
        <= total_request_bound_function ts Δ.
    Proof.
      move=> t Δ.
      rewrite /workload_of_hep_jobs (leqRW (workload_of_jobs_weaken _ predT _ _ )); last by done.
      by apply total_workload_le_total_rbf.
    Qed.

  End JLFP.

End ProofRequestBoundFunction.

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

  (** We prove that [task_request_bound_function 0] is equal to [0]. *)
  Lemma task_rbf_0_zero:
    task_request_bound_function tsk 0 = 0.
  Proof.
    rewrite /task_request_bound_function.
    apply/eqP; rewrite muln_eq0; apply/orP; right; apply/eqP.
    by move: H_valid_arrival_curve => [T1 T2].
  Qed.

  (** We prove that [task_request_bound_function] is monotone. *)
  Lemma task_rbf_monotone:
    monotone leq (task_request_bound_function tsk).
  Proof.
    rewrite /monotone => ? ? LE.
    rewrite /task_request_bound_function leq_mul2l.
    apply/orP; right.
    by move: H_valid_arrival_curve => [_ T]; apply T.
  Qed.


  (** In the following, we assume that [tsk] has a positive cost ... *)
  Hypothesis H_positive_cost : 0 < task_cost tsk.

  (** ... and [max_arrivals tsk ε] is positive. *)
  Hypothesis H_arrival_curve_positive : max_arrivals tsk ε > 0.

  (** Then we prove that [task_request_bound_function] at [ε] is greater than or equal to the task's WCET. *)
  Lemma task_rbf_1_ge_task_cost:
    task_request_bound_function tsk ε >= task_cost tsk.
  Proof.
    have ALT: forall n, n = 0 \/ n > 0 by clear; intros n; destruct n; [left | right].
    specialize (ALT (task_cost tsk)); destruct ALT as [Z | POS]; first by rewrite Z.
    rewrite -[task_cost tsk]muln1 /task_request_bound_function.
    by rewrite leq_pmul2l //=.
  Qed.

  (** As a corollary, we prove that the [task_request_bound_function] at any point [A] greater than
      [0] is no less than the task's WCET. *)
  Lemma task_rbf_ge_task_cost:
    forall A,
      A > 0 ->
      task_request_bound_function tsk A >= task_cost tsk.
  Proof.
    case => // A GEQ.
    apply: (leq_trans task_rbf_1_ge_task_cost).
    exact: task_rbf_monotone.
  Qed.

  (** Then, we prove that [task_request_bound_function] at [ε] is greater than [0]. *)
  Lemma task_rbf_epsilon_gt_0 : 0 < task_request_bound_function tsk ε.
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

  (** Thus we can prove any response-time bound from such a pathological
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
  Context `{FP : FP_policy Task}.

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

  (** Now, assume that the priorities are reflexive. *)
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.

  (** If the task set does not contain duplicates, then the total
      higher-or-equal-priority RBF for any task can be split as the sum of
      the total _other_ higher-or-equal-priority workload and the RBF of the
      task itself. *)
  Lemma split_hep_rbf :
    forall Δ,
      tsk \in ts ->
      uniq ts ->
      total_hep_request_bound_function_FP ts tsk Δ
      = total_ohep_request_bound_function_FP ts tsk Δ
        + task_request_bound_function tsk Δ.
  Proof.
    move => Δ IN UNIQ.
    rewrite /total_hep_request_bound_function_FP /total_ohep_request_bound_function_FP.
    rewrite (bigID_idem _ _ (fun tsko => tsko != tsk)) //=.
    apply /eqP; rewrite eqn_add2l.
    rewrite (eq_bigl (fun i => i == tsk)); last first.
    - move => tsko.
      case (tsko == tsk) eqn: EQ; last by lia.
      move : EQ => /eqP ->.
      by rewrite H_priority_is_reflexive //=.
    - rewrite  (big_rem tsk) //= eq_refl.
      rewrite big_seq_cond big_pred0; first by rewrite addn0 //=.
      move => tsko.
      case (tsko == tsk) eqn: EQ; last by lia.
      move : EQ => /eqP ->.
      rewrite andbT.
      by apply mem_rem_uniqF => //=.
  Qed.

  (** If the task set may contain duplicates, then the we can only say that
      the sum of other higher-or-equal-priority [RBF] and task [tsk]'s [RBF]
      is at most the total higher-or-equal-priority workload. *)
  Lemma split_hep_rbf_weaken:
    forall Δ,
      tsk \in ts ->
      total_ohep_request_bound_function_FP ts tsk Δ + task_request_bound_function tsk Δ
      <= total_hep_request_bound_function_FP ts tsk Δ.
  Proof.
    move => Δ IN.
    rewrite /total_hep_request_bound_function_FP /total_ohep_request_bound_function_FP.
    rewrite [leqRHS](bigID_idem _ _ (fun tsko => tsko != tsk)) //=.
    apply leq_add; first by done.
    rewrite (eq_bigl (fun tsko => tsko == tsk)); last first.
    - move => tsko.
      case (tsko ==tsk) eqn: TSKEQ; last by lia.
      move : TSKEQ => /eqP ->.
      by rewrite (H_priority_is_reflexive tsk) //=.
    - rewrite  (big_rem tsk) //= eq_refl.
      by apply leq_addr.
  Qed.

End FP_RBF_partitioning.

(** In this section, we state a few facts for RBFs in the context of a
    fixed-priority policy. *)
Section RBFFOrFP.

  (** Consider a set of tasks characterized by WCETs and arrival curves. *)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}.
  Variable ts : seq Task.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** For any fixed-priority policy, ... *)
  Context `{FP_policy Task}.

  (** ... [total_ohep_request_bound_function_FP] at [0] is always [0]. *)
  Lemma total_ohep_rbf0 :
    forall (tsk : Task),
      total_ohep_request_bound_function_FP ts tsk 0 = 0.
  Proof.
    rewrite /total_ohep_request_bound_function_FP => tsk.
    apply /eqP.
    rewrite sum_nat_eq0_nat.
    apply /allP => tsk' IN.
    apply /eqP.
    apply task_rbf_0_zero => //=.
    apply H_valid_arrival_curve.
    rewrite mem_filter in IN.
    by move : IN => /andP[_ ->].
  Qed.

  (** Next we show how [total_ohep_request_bound_function_FP] can bound the
      workload of jobs in a given interval. *)

  (** Consider any types of jobs. *)
  Context `{Job : JobType} `{JobTask Job Task} `{JobCost Job}.

  (** Consider any arrival sequence that only has jobs from the task set and
      where all arrivals have a valid job cost. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Assume there exists an arrival curve and that the arrival sequence
      respects this curve. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_respects_max_arrivals : taskset_respects_max_arrivals arr_seq ts.

  (** Consider any task [tsk] and any job [j] of the task [tsk]. *)
  Variable j : Job.
  Variable tsk : Task.
  Hypothesis H_job_of_task : job_of_task tsk j.

  (** For any interval <<[t1, t1 + Δ)>>, the workload of jobs that have higher
      task priority than the task priority of [j] is bounded by
      [total_ohep_request_bound_function_FP] for the duration [Δ]. *)
  Lemma ohep_workload_le_rbf :
    forall Δ t1,
      workload_of_jobs (another_task_hep_job^~ j) (arrivals_between arr_seq t1 (t1 + Δ))
      <= total_ohep_request_bound_function_FP ts tsk Δ.
  Proof.
    move => Δ t1.
    rewrite /workload_of_jobs /total_ohep_request_bound_function_FP.
    rewrite /another_task_hep_job /hep_job /FP_to_JLFP.
    set (pred_task tsk_other := hep_task tsk_other tsk && (tsk_other != tsk)).
    rewrite (eq_big (fun j=> pred_task (job_task j)) job_cost) //;
      last by move=> j'; rewrite /pred_task; move: H_job_of_task => /eqP ->.
    erewrite (eq_big pred_task); [|by done|by move=> tsk'; eauto].
    by apply: workload_of_jobs_bounded.
  Qed.

End RBFFOrFP.

(** We know that the workload of a task in any interval must be
    bounded by the task's RBF in that interval. However, in the proofs
    of several lemmas, we are required to reason about the workload of
    a task in an interval excluding the cost of a particular job
    (usually the job under analysis). Such a workload can be tightly
    bounded by the task's RBF for the interval excluding the cost of
    one task.

    Notice, however, that this is not a trivial result since a naive
    approach to proving it would fail.  Suppose we want to prove that
    some quantity [A - B] is upper bounded by some quantity [C -
    D]. This usually requires us to prove that [A] is upper bounded by
    [C] _and_ [D] is upper bounded by [B]. In our case, this would be
    equivalent to proving that the task cost is upper-bounded by the
    job cost, which of course is not true.

    So, a different approach is needed, which we show in this
    section. *)
Section TaskWorkload.

   (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent:
    consistent_arrival_times arr_seq.

  (** ... and assume that WCETs are respected. *)
  Hypothesis H_arrivals_have_valid_job_costs :
    arrivals_have_valid_job_costs arr_seq.

  (** Let [tsk] be any task ... *)
  Variable tsk : Task.

  (** ... characterized by a valid arrival curve. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_arrival_curve (max_arrivals tsk).
  Hypothesis H_is_arrival_curve : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  (** Consider any job [j] of [tsk] ... *)
  Variable j : Job.
  Hypothesis H_job_of_task : job_of_task tsk j.

  (** ... that arrives in the given arrival sequence. *)
  Hypothesis H_j_arrives_in : arrives_in arr_seq j.

  (** Consider any time instant [t1] and duration [Δ] such that [j]
      arrives before [t1 + Δ]. *)
  Variables (t1 : instant) (Δ : duration).
  Hypothesis H_job_arrival_lt : job_arrival j < t1 + Δ.

  (** As a preparatory step, we restrict our attention to the sub-interval
      containing the job's arrival. We know that the job's arrival necessarily
      happens in the interval (<<[job_arrival j], t1 + Δ>>). This allows us to
      show that the task workload excluding the task cost can be bounded by the
      cost of the arrivals in the interval as follows. *)
  Lemma task_rbf_without_job_under_analysis_from_arrival :
    task_workload_between arr_seq tsk (job_arrival j) (t1 + Δ) - job_cost j
    <= task_cost tsk * number_of_task_arrivals arr_seq tsk (job_arrival j) (t1 + Δ)
       - task_cost tsk.
  Proof.
    rewrite /task_workload_between /task_workload /workload_of_jobs /number_of_task_arrivals.
    rewrite (big_rem j) //= addnC //= H_job_of_task addnK (filter_size_rem j)//.
    rewrite mulnDr mulnC muln1 addnK mulnC.
    apply sum_majorant_constant => j' ARR' /eqP TSK2.
    rewrite -TSK2; apply H_arrivals_have_valid_job_costs.
    apply rem_in in ARR'.
    by eapply in_arrivals_implies_arrived => //=.
  Qed.

  (** To use the above lemma in our final theorem, we require that the arrival
      of the job under analysis necessarily happens in the interval we are
      considering. *)
  Hypothesis H_j_arrives_after_t : t1 <= job_arrival j.

  (** Under the above assumption, we can finally establish the desired bound. *)
  Lemma task_rbf_without_job_under_analysis :
    task_workload_between arr_seq tsk t1 (t1 + Δ) - job_cost j
    <= task_request_bound_function tsk Δ - task_cost tsk.
  Proof.
    apply leq_trans with
      (task_cost tsk * number_of_task_arrivals arr_seq tsk t1 (t1 + Δ) - task_cost tsk); last first.
    - rewrite leq_sub2r // leq_mul2l; apply/orP => //=; right.
      have POSE: Δ = (t1 + Δ - t1) by lia.
      rewrite [in leqRHS]POSE.
      eapply (H_is_arrival_curve t1 (t1 + Δ)).
      by lia.
    - rewrite (@num_arrivals_of_task_cat _ _ _ _ _ (job_arrival j)); last by apply /andP; split.
      rewrite mulnDr.
      rewrite /task_workload_between /task_workload (workload_of_jobs_cat _ (job_arrival j) );
        last by apply/andP; split; lia.
      rewrite -!addnBA; first last.
      + by rewrite /task_workload
          /workload_of_jobs (big_rem j) //= H_job_of_task leq_addr.
      + rewrite -{1}[task_cost tsk]muln1 leq_mul2l; apply/orP; right.
        rewrite /number_of_task_arrivals /task_arrivals_between.
        rewrite size_filter -has_count; apply/hasP; exists j; last by rewrite H_job_of_task.
        apply (mem_bigcat _ Job _ (job_arrival j) _); last by apply job_in_arrivals_at => //=.
        rewrite mem_index_iota.
        by apply /andP;split.
      + rewrite leq_add //; last by apply: task_rbf_without_job_under_analysis_from_arrival.
        rewrite -/(task_workload _ _) -/(task_workload_between _ _ _ _).
        by apply: task_workload_between_bounded.
  Qed.

End TaskWorkload.
