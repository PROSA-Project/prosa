Require Export prosa.model.aggregate.workload.
Require Export prosa.analysis.facts.behavior.arrivals.
Require Export prosa.analysis.facts.model.task_arrivals.

(** * Lemmas about Workload of Sets of Jobs *)
(** In this file, we establish basic facts about the workload of sets of jobs. *)
Section WorkloadFacts.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** To begin with, we establish an auxiliary rewriting lemma that allows us to
      introduce a [filter] on the considered set of jobs, provided the filter
      predicate [P2] is implied by the job-selection predicate [P1]. *)
  Lemma workload_of_jobs_filter :
    forall (P1 P2 : pred Job) (jobs : seq Job),
      (forall j, j \in jobs -> P1 j -> P2 j) ->
      workload_of_jobs P1 jobs = workload_of_jobs P1 [seq j <- jobs | P2 j ].
  Proof.
    move=> P1 P2 jobs IMPL.
    rewrite /workload_of_jobs big_filter_cond big_seq_cond [RHS]big_seq_cond.
    apply: eq_bigl => j.
    case: (boolP (j \in jobs)) => // IN.
    rewrite !andTb.
    case: (boolP (P1 j)) => //= P1j; first by rewrite (IMPL j IN P1j).
    by rewrite andbF.
  Qed.

  (** We establish that if the predicate [P1] implies the predicate [P2],
      then the cumulative workload of jobs that respect [P1] is bounded
      by the cumulative workload of jobs that respect [P2]. *)
  Lemma workload_of_jobs_weaken :
    forall (P1 P2 : pred Job) (jobs : seq Job),
      (forall j, P1 j -> P2 j) ->
      workload_of_jobs P1 jobs <= workload_of_jobs P2 jobs.
  Proof.
    move => P1 P2 jobs IMPLIES; rewrite /workload_of_jobs.
    apply: leq_sum_seq_pred => j' _.
    by apply: IMPLIES.
  Qed.

  (** The cumulative workload of jobs from an empty sequence is always zero. *)
  Lemma workload_of_jobs0 :
    forall (P : pred Job), workload_of_jobs P [::] = 0.
  Proof. by move => ?; rewrite /workload_of_jobs big_nil. Qed.

  (** Now we relate the workload of jobs satisfying a predicate [P] to the sum over tasks. *)
  Lemma workload_of_jobs_le_sum_over_partitions :
    forall {P : pred Job} (Q : pred Task) {js : seq Job} (ts : seq Task),
      {in js, forall j, (job_task j) \in ts} ->
      {in js, forall j, P j -> Q (job_task j)} ->
      let P_and_job_of tsk_o j := P j && (job_task j == tsk_o) in
      workload_of_jobs P js
      <= \sum_(tsk_o <- ts | Q tsk_o ) workload_of_jobs (P_and_job_of tsk_o) js.
  Proof.
    move=> P Q js ts IN_ts PQ //=.
    rewrite -big_filter.
    apply: sum_over_partitions_le => j IN Px.
    rewrite mem_filter.
    by apply/andP.
  Qed.

  (** The workload of a set of jobs can be equivalently rewritten as sum over
      their tasks. *)
  Lemma workload_of_jobs_partitioned_by_tasks :
    forall {P : pred Job} (Q : pred Task) {js : seq Job} (ts : seq Task),
      {in js, forall j, (job_task j) \in ts} ->
      {in js, forall j, P j -> Q (job_task j)} ->
      uniq js ->
      uniq ts ->
      let P_and_job_of tsk_o j := P j && (job_task j == tsk_o) in
      workload_of_jobs P js
      = \sum_(tsk_o <- ts | Q tsk_o ) workload_of_jobs (P_and_job_of tsk_o) js.
  Proof.
    move=> P Q js ts IN_ts PQ UJ UT //=.
    rewrite -big_filter {1}/workload_of_jobs //.
    apply: sum_over_partitions_eq => // [j IN Px|]; last exact: filter_uniq.
    rewrite mem_filter; apply/andP; split; last by apply: IN_ts.
    by apply: PQ.
  Qed.

  (** In this section we state a lemma about splitting the workload among tasks
      of different priority relative to a job [j]. *)
  Section WorkloadPartitioningByPriority.

    (** Consider any JLFP policy. *)
    Context `{JLFP_policy Job}.

    (** Consider the workload of all the jobs that have priority
        higher-than-or-equal-to the priority of [j]. This workload can be split
        by task into the workload of higher-or-equal priority jobs from the task of [j]
        and higher-or-equal priority jobs from all tasks except for the task of [j]. *)
    Lemma workload_of_other_jobs_split :
      forall jobs j,
        workload_of_jobs (another_hep_job^~j) jobs =
          workload_of_jobs (another_task_hep_job^~j) jobs
          + workload_of_jobs (another_hep_job_of_same_task^~j) jobs.
    Proof.
      move => jobs j.
      rewrite /workload_of_jobs.
      apply sum_split_exhaustive_mutually_exclusive_preds  => jo.
      - rewrite /another_hep_job /another_task_hep_job /another_hep_job_of_same_task
          /same_task /another_hep_job.
        case (hep_job jo j) eqn: EQ1;
          case (jo != j) eqn: EQ2;
          case (job_task jo != job_task j) eqn: EQ3; try lia.
        move : EQ2 => /eqP EQ2.
        rewrite EQ2 in EQ3.
        contradict EQ3.
        by apply /negP /negPn /eqP.
      - rewrite /another_hep_job /another_task_hep_job /another_hep_job_of_same_task
          /same_task /another_hep_job.
        by case (hep_job jo j) eqn: EQ1; case (jo != j) eqn: EQ2;
          case (job_task jo != job_task j) eqn: EQ3; try lia.
    Qed.

  End WorkloadPartitioningByPriority.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent : consistent_arrival_times arr_seq.

  (** In this section, we prove a few useful properties regarding the
      predicate of [workload_of_jobs]. *)
  Section PredicateProperties.

    (** Consider a sequence of jobs [jobs]. *)
    Variable jobs : seq Job.

    (** First, we show that workload of [jobs] for an unsatisfiable
        predicate is equal to [0]. *)
    Lemma workload_of_jobs_pred0 :
      workload_of_jobs pred0 jobs = 0.
    Proof. by rewrite /workload_of_jobs; apply big_pred0. Qed.

    (** Next, consider two arbitrary predicates [P] and [P']. *)
    Variable P P' : pred Job.

    (** We show that [workload_of_jobs] conditioned on [P] can be split into two summands:
        (1) [workload_of_jobs] conditioned on [P /\ P'] and
        (2) [workload_of_jobs] conditioned on [P /\ ~~ P']. *)
    Lemma workload_of_jobs_case_on_pred :
      workload_of_jobs P jobs =
        workload_of_jobs (fun j => P j && P' j) jobs + workload_of_jobs (fun j => P j && ~~ P' j) jobs.
    Proof.
      rewrite /workload_of_jobs !big_mkcond [in X in _ = X]big_mkcond
              [in X in _ = _ + X]big_mkcond //= -big_split //=.
      apply: eq_big_seq => j' IN.
      by destruct (P _), (P' _); simpl; lia.
    Qed.

    (** We show that if [P] is indistinguishable from [P'] on set
        [jobs], then [workload_of_jobs] conditioned on [P] is equal to
        [workload_of_jobs] conditioned on [P']. *)
    Lemma workload_of_jobs_equiv_pred :
      {in jobs, P =1 P'} ->
      workload_of_jobs P jobs = workload_of_jobs P' jobs.
    Proof.
      intros * EQUIV.
      rewrite /workload_of_jobs !big_mkcond [in X in _ = X]big_mkcond //=.
      by apply: eq_big_seq => j' IN; rewrite EQUIV.
    Qed.

  End PredicateProperties.

  (** In this section, we prove one equality about the workload of a job. *)
  Section WorkloadOfJob.

    (** Assume there are no duplicates in the arrival sequence. *)
    Hypothesis H_arrival_sequence_is_a_set : arrival_sequence_uniq arr_seq.

    (** We prove that the workload of a job in an interval <<[t1,
        t2)>> is equal to the cost of the job if the job's arrival is
        in the interval and [0] otherwise. *)
    Lemma workload_of_job_eq_job_arrival :
      forall (j : Job) (t1 t2 : instant),
        arrives_in arr_seq j ->
        workload_of_job arr_seq j t1 t2
        = if t1 <= job_arrival j < t2 then job_cost j else 0.
    Proof.
      move=> j t1 t2 ARR; case NEQ: (_ <= _ < _).
      { rewrite /workload_of_job /workload_of_jobs.
        erewrite big_pred1_seq; first reflexivity.
        - by apply arrived_between_implies_in_arrivals => //=.
        - by done.
        - by move => j'; rewrite /pred1 //=.
      }
      { apply big1_seq => j' /andP [/eqP EQ IN]; subst j'; exfalso.
        by apply job_arrival_between in IN => //.
      }
    Qed.

  End WorkloadOfJob.

  (** In the following section, we relate three types of workload:
      workload of a job [j], workload of higher-or-equal priority jobs
      distinct from [j], and workload of higher-or-equal priority
      jobs. *)
  Section HEPWorkload.

    (** Consider a JLFP policy that indicates a higher-or-equal
        priority relation and assume that the relation is
        reflexive. *)
    Context {JLFP : JLFP_policy Job}.
    Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

    (** We prove that the sum of the workload of a job [j] and the
        workload of higher-or-equal priority jobs distinct from [j] is
        equal to the workload of higher-or-equal priority jobs. *)
    Lemma workload_job_and_ahep_eq_workload_hep :
      forall (j : Job) (t1 t2 : instant),
        workload_of_job arr_seq j t1 t2 + workload_of_other_hep_jobs arr_seq j t1 t2
        = workload_of_hep_jobs arr_seq j t1 t2.
    Proof.
      move=> j t1 t2.
      rewrite /workload_of_job /workload_of_other_hep_jobs /workload_of_hep_jobs.
      rewrite [RHS](workload_of_jobs_case_on_pred _ _  (fun jhp => jhp != j)).
      have EQ: forall a b c d, a = b -> c = d -> a + c = b + d by lia.
      rewrite addnC; apply EQ; first by reflexivity.
      clear EQ; apply workload_of_jobs_equiv_pred => jo IN.
      have [EQ|NEQ] := eqVneq j jo.
      { by subst; rewrite andbT; symmetry; apply H_priority_is_reflexive. }
      by rewrite andbF.
    Qed.

  End HEPWorkload.

  (** If at some point in time [t] the predicate [P] by which we select jobs
      from the set of arrivals in an interval <<[t1, t2)>> becomes certainly
      false, then we may disregard all jobs arriving at time [t] or later. *)
  Lemma workload_of_jobs_nil_tail :
    forall {P t1 t2 t},
      t <= t2 ->
      (forall j, j \in (arrivals_between arr_seq t1 t2) -> job_arrival j >= t -> ~~ P j) ->
      workload_of_jobs P (arrivals_between arr_seq t1 t2)
      = workload_of_jobs P (arrivals_between arr_seq t1 t).
  Proof.
    move=> P t1 t2 t LE IMPL.
    have -> : arrivals_between arr_seq t1 t = [seq j <- (arrivals_between arr_seq t1 t2) | job_arrival j < t]
      by apply: arrivals_between_filter.
    rewrite (workload_of_jobs_filter _ (fun j => job_arrival j < t)) // => j IN Pj.
    case: (leqP t (job_arrival j)) => // TAIL.
    by move: (IMPL j IN TAIL) => /negP.
  Qed.

  (** We observe that the cumulative workload of all jobs arriving in a time
      interval <<[t1, t2)>> and respecting a predicate [P] can be split into two parts. *)
   Lemma workload_of_jobs_cat:
    forall t t1 t2 P,
      t1 <= t <= t2 ->
      workload_of_jobs P (arrivals_between arr_seq t1 t2) =
      workload_of_jobs P (arrivals_between arr_seq t1 t) + workload_of_jobs P (arrivals_between arr_seq t t2).
  Proof.
    move => t t1 t2 P /andP [GE LE].
    rewrite /workload_of_jobs.
    by rewrite (arrivals_between_cat _ _ t) // big_cat.
  Qed.

  (** As a corollary, we prove that the workload in any range <<[t1,t3)>>
      always bounds the workload in any sub-range <<[t1,t2)>>. *)
    Corollary workload_of_jobs_reduce_range :
      forall t1 t2 t3 P,
        t1 <= t2 ->
        t2 <= t3 ->
        workload_of_jobs P (arrivals_between arr_seq t1 t2)
        <= workload_of_jobs P (arrivals_between arr_seq t1 t3).
    Proof.
      move => t1 t2 t3 P ??.
      rewrite (workload_of_jobs_cat t2 t1 t3 P _  ) //=; [| apply /andP; split; done].
      by apply leq_addr.
    Qed.

  (** Consider a job [j] ... *)
  Variable j : Job.

  (** ... and a duplicate-free sequence of jobs [jobs]. *)
  Variable jobs : seq Job.
  Hypothesis H_jobs_uniq : uniq jobs.

  (** Further, assume that [j] is contained in [jobs]. *)
  Hypothesis H_j_in_jobs : j \in jobs.

  (** To help with rewriting, we prove that the workload of [jobs]
      minus the job cost of [j] is equal to the workload of all jobs
      except [j]. *)
  Lemma workload_minus_job_cost' :
    forall P,
      workload_of_jobs (fun jhp : Job => P jhp && (jhp != j)) jobs
      = workload_of_jobs P jobs - (if P j then job_cost j else 0).
  Proof.
    move => P.
    rewrite /workload_of_jobs.
    rewrite [in X in _ = X - _](bigID_idem _ _ (fun jo => (jo != j))) //=.
    have -> :  \sum_(j0 <- jobs | P j0 && ~~ (j0 != j)) job_cost j0 =(if P j then job_cost j else 0);
      last by lia.
    rewrite (big_rem j) //=.
    rewrite negbK eq_refl andbT.
    have -> :  \sum_(y <- rem (T:=Job) j jobs | P y && ~~ (y != j)) job_cost y= 0;
      last by rewrite addn0.
    rewrite big_seq_cond.
    apply big_pred0 => jo.
    rewrite negbK andbA andbC andbA.
    case (P jo); [rewrite andbT | lia].
    case (jo == j) eqn: JJ; [rewrite andTb| lia].
    move : JJ => /eqP ->.
    by apply mem_rem_uniqF => //=.
  Qed.

  (** Next, we specialize the above lemma to the trivial predicate [predT]. *)
  Corollary workload_minus_job_cost :
    workload_of_jobs (fun jhp : Job => jhp != j) jobs =
    workload_of_jobs predT jobs - job_cost j.
  Proof.
    by rewrite (workload_minus_job_cost' predT) //=.
  Qed.

  (** In this section, we prove the relation between two different ways of constraining
      [workload_of_jobs] to only those jobs that arrive prior to a given time. *)
  Section Subset.

    (** Assume that arrival times are consistent and that arrivals are unique. *)
    Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

    (** Consider a time interval <<[t1, t2)>> and a time instant [t]. *)
    Variable t1 t2 t : instant.
    Hypothesis H_t1_le_t2 : t1 <= t2.

    (** Let [P] be an arbitrary predicate on jobs. *)
    Variable P : pred Job.

    (** Consider the window <<[t1,t2)>>. We prove that the total workload of the jobs
        arriving in this window before some [t] is the same as the workload of the jobs
        arriving in <<[t1,t)>>. Note that we only require [t1] to be less-or-equal
        than [t2]. Consequently, the interval <<[t1,t)>> may be empty. *)
    Lemma workload_equal_subset :
      workload_of_jobs (fun j => (job_arrival j <= t) && P j) (arrivals_between arr_seq t1 t2)
      <= workload_of_jobs (fun j => P j) (arrivals_between arr_seq t1 (t + ε)).
    Proof.
      clear H_jobs_uniq H_j_in_jobs H_t1_le_t2.
      rewrite /workload_of_jobs big_seq_cond.
      rewrite -[in X in X <= _]big_filter -[in X in _ <= X]big_filter.
      apply leq_sum_sub_uniq; first by apply filter_uniq, arrivals_uniq.
      move => j'; rewrite mem_filter => [/andP [/andP [A  /andP [C D]] _]].
      rewrite job_arrival_in_bounds in A => //=.
      move : A => [A /andP[A1 A2]].
      rewrite mem_filter; apply/andP; split=> [//|].
      apply job_in_arrivals_between => //=.
      by lia.
    Qed.

  End Subset.

End WorkloadFacts.
