Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.definitions.request_bound_function.

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
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** ... any schedule corresponding to this arrival sequence, ... *)
  Context {PState : Type} `{ProcessorState Job PState}.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... and an FP policy that indicates a higher-or-equal priority relation. *)
  Context `{FP_policy Task}.
  Let jlfp_higher_eq_priority := FP_to_JLFP Job Task.

  (** Further, consider a task set [ts]... *)
  Variable ts : list Task.

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
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.
  
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
        rewrite EXCHANGE /=; clear EXCHANGE; last by done.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)) /=.
        rewrite eq_refl; apply leq_addr.
        by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset. }
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
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_task j = tsk.
    
    (** We say that two jobs [j1] and [j2] are in relation
      [other_higher_eq_priority], iff [j1] has higher or equal priority than [j2] and
      is produced by a different task. *)
    Let other_higher_eq_priority j1 j2 :=
      jlfp_higher_eq_priority j1 j2 && (~~ same_task j1 j2).

    (** Recall the notion of workload of higher or equal priority jobs... *)
    Let total_hep_workload t1 t2 :=
      workload_of_jobs (fun j_other => jlfp_higher_eq_priority j_other j)
                       (arrivals_between arr_seq t1 t2).

    (** ... and workload of other higher or equal priority jobs. *)
    Let total_ohep_workload t1 t2 :=
      workload_of_jobs (fun j_other => other_higher_eq_priority j_other j)
                       (arrivals_between arr_seq t1 t2).

    (** We prove that total workload of other tasks with higher-or-equal
        priority is no larger than the total request bound function. *)
    Lemma total_workload_le_total_ohep_rbf:
      total_ohep_workload t (t + Δ) <= total_ohep_rbf Δ.
    Proof.
      set l := arrivals_between arr_seq t (t + Δ).
      apply (@leq_trans (\sum_(tsk' <- ts | hep_task tsk' tsk && (tsk' != tsk))
                          (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0))).
      { rewrite /total_ohep_workload /workload_of_jobs /other_higher_eq_priority.
        rewrite /jlfp_higher_eq_priority /FP_to_JLFP /same_task H_job_of_tsk.
        set P := fun x => hep_task (job_task x) tsk && (job_task x != tsk).
        rewrite (exchange_big_dep P) //=; last by rewrite /P; move => ???/eqP->.
        rewrite /P /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)).
        - by rewrite HP0 andTb eq_refl; apply leq_addr.
        - by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset. }
      apply leq_sum_seq; intros tsk0 INtsk0 HP0.
      apply (@leq_trans (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + Δ)))).
      { rewrite -sum1_size big_distrr /= big_filter /workload_of_jobs.
        rewrite  muln1 /l /arrivals_between /arrival_sequence.arrivals_between.
        apply leq_sum_seq; move => j0 IN0 /eqP EQ.
        by rewrite -EQ; apply H_valid_job_cost; apply in_arrivals_implies_arrived in IN0. }
      { rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[Δ](addKn t).
        by apply H_is_arrival_bound; last rewrite leq_addr. }
    Qed.

    (** Next, we prove that total workload of all tasks with higher-or-equal
        priority is no larger than the total request bound function. *)
    Lemma total_workload_le_total_hep_rbf:
      total_hep_workload t (t + Δ) <= total_hep_rbf Δ.
    Proof.
      set l := arrivals_between arr_seq t (t + Δ).
      apply(@leq_trans (\sum_(tsk' <- ts | hep_task tsk' tsk)
                         (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0))).
      { rewrite /total_hep_workload /jlfp_higher_eq_priority /FP_to_JLFP H_job_of_tsk.
        have EXCHANGE := exchange_big_dep (fun x => hep_task (job_task x) tsk).
        rewrite EXCHANGE /=; clear EXCHANGE; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)).
        - by rewrite HP0 andTb eq_refl; apply leq_addr.
        - by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset. }
      apply leq_sum_seq; intros tsk0 INtsk0 HP0.
      apply (@leq_trans (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + Δ)))).
      { rewrite -sum1_size big_distrr /= big_filter.
        rewrite -/l /workload_of_jobs muln1.
        apply leq_sum_seq; move => j0 IN0 /eqP <-.
        apply H_valid_job_cost.
        by apply in_arrivals_implies_arrived in IN0. }
      { rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[Δ](addKn t).
        by apply H_is_arrival_bound; last rewrite leq_addr. }
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

  (** Let [max_arrivals] be a family of valid arrival curves, i.e., for any task [tsk] in [ts]
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) it is a monotonic function
     that equals 0 for the empty interval Δ = 0. *)
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

  (** Consider any job [j] of [tsk]. This guarantees that there exists at least one
      job of task [tsk]. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_task j = tsk.

  (** Then we prove that [task_rbf] at [ε] is greater than or equal to task cost. *)
  Lemma task_rbf_1_ge_task_cost:
    task_rbf ε >= task_cost tsk.
  Proof.
    have ALT: forall n, n = 0 \/ n > 0 by clear; intros n; destruct n; [left | right].
    specialize (ALT (task_cost tsk)); destruct ALT as [Z | POS]; first by rewrite Z.
    rewrite leqNgt; apply/negP; intros CONTR.
    move: H_is_arrival_curve => ARRB.
    specialize (ARRB (job_arrival j) (job_arrival j + ε)).
    feed ARRB; first by rewrite leq_addr.
    move: CONTR; rewrite /task_rbf /task_request_bound_function.
    rewrite -{2}[task_cost tsk]muln1 ltn_mul2l => /andP [_ CONTR].
    move: CONTR; rewrite -addn1 -[1]add0n leq_add2r leqn0 => /eqP CONTR.
    move: ARRB; rewrite addKn CONTR leqn0 eqn0Ngt => /negP T; apply: T.
    rewrite /number_of_task_arrivals -has_predT /task_arrivals_between.
    apply/hasP; exists j; last by done.
    rewrite /arrivals_between addn1 big_nat_recl; last by done.
    rewrite big_geq ?cats0 //= mem_filter.
    apply/andP; split; first by apply/eqP.
    move: H_j_arrives => [t ARR]; move: (ARR) => CONS.
    apply H_arrival_times_are_consistent in CONS.
    by rewrite CONS.
  Qed.

  (** Assume that [tsk] has a positive cost. *)
  Hypothesis H_positive_cost : 0 < task_cost tsk.
  
  (** Then, we prove that [task_rbf] at [ε] is greater than [0]. *)
  Lemma task_rbf_epsilon_gt_0 : 0 < task_rbf ε.
  Proof.
    apply leq_trans with (task_cost tsk); first by done.
    by eapply task_rbf_1_ge_task_cost; eauto. 
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
    move => t GE.
    destruct t; first by done.
    eapply leq_trans; first by apply task_rbf_1_ge_task_cost; eauto with basic_facts.
    rewrite /total_request_bound_function.
    erewrite big_rem; last by exact H_tsk_in_ts.
    apply leq_trans with (task_request_bound_function tsk t.+1); last by apply leq_addr.
    by apply task_rbf_monotone.
  Qed.

End RequestBoundFunctions.
