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

  (** Consider any arrival sequence with consistent, non-duplicate arrivals... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** ... and any ideal uni-processor schedule of this arrival sequence.*)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** Consider an FP policy that indicates a higher-or-equal priority relation. *)
  Context `{FP_policy Task}.
  Let jlfp_higher_eq_priority := FP_to_JLFP Job Task.

  (** Consider a task set ts... *)
  Variable ts : list Task.

  (** ...and let [tsk] be any task in ts. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let max_arrivals be any arrival bound for task-set [ts]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_is_arrival_bound : taskset_respects_max_arrivals arr_seq ts.

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let total_rbf := total_request_bound_function ts.
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

  (** Next, we consider any job [j] of [tsk]. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_task j = tsk.

  (** Next, we say that two jobs [j1] and [j2] are in relation
      [other_higher_eq_priority], iff [j1] has higher or equal priority than [j2] and
      is produced by a different task. *)
  Let other_higher_eq_priority j1 j2 := jlfp_higher_eq_priority j1 j2 && (~~ same_task j1 j2).

  (** Next, we recall the notions of total workload of jobs... *)
  Let total_workload t1 t2 := workload_of_jobs predT (arrivals_between arr_seq t1 t2).

  (** ...notions of workload of higher or equal priority jobs... *)
  Let total_hep_workload t1 t2 :=
    workload_of_jobs (fun j_other => jlfp_higher_eq_priority j_other j) (arrivals_between arr_seq t1 t2).

  (** ... workload of other higher or equal priority jobs... *)
  Let total_ohep_workload t1 t2 :=
    workload_of_jobs (fun j_other => other_higher_eq_priority j_other j) (arrivals_between arr_seq t1 t2).

  (** ... and the workload of jobs of the same task as job j. *)
  Let task_workload t1 t2 :=
    workload_of_jobs (job_of_task tsk) (arrivals_between arr_seq t1 t2).

  (** In this section we prove that the workload of any jobs is
       no larger than the request bound function. *)
  Section WorkloadIsBoundedByRBF.

    (** Consider any time t and any interval of length delta. *)
    Variable t : instant.
    Variable delta : instant.

    (** First, we show that workload of task [tsk] is bounded by the number of
        arrivals of the task times the cost of the task. *)
    Lemma task_workload_le_num_of_arrivals_times_cost:
      task_workload t (t + delta)
      <= task_cost tsk * number_of_task_arrivals arr_seq tsk t (t + delta).
    Proof.
      rewrite // /number_of_task_arrivals -sum1_size big_distrr /= big_filter.
      rewrite /task_workload_between /workload.task_workload_between /task_workload /workload_of_jobs.
      rewrite /same_task -H_job_of_tsk muln1.
      apply leq_sum_seq; move => j0 IN0 /eqP EQ.
      rewrite -EQ; apply in_arrivals_implies_arrived in IN0; auto.
        by apply H_valid_job_cost.
    Qed.

    (** As a corollary, we prove that workload of task is no larger the than
        task request bound function. *)
    Corollary task_workload_le_task_rbf:
      task_workload t (t + delta) <= task_rbf delta.
    Proof.
      apply leq_trans with
          (task_cost tsk *  number_of_task_arrivals arr_seq tsk t (t + delta));
        first by apply task_workload_le_num_of_arrivals_times_cost.
      rewrite leq_mul2l; apply/orP; right.
      rewrite -{2}[delta](addKn t).
        by apply H_is_arrival_bound; last rewrite leq_addr.
    Qed.

    (** Next, we prove that total workload of other tasks with higher-or-equal
        priority is no larger than the total request bound function. *)
    Lemma total_workload_le_total_rbf:
      total_ohep_workload t (t + delta) <= total_ohep_rbf delta.
    Proof.
      set l := arrivals_between arr_seq t (t + delta).
      apply leq_trans with
          (\sum_(tsk' <- ts | hep_task tsk' tsk && (tsk' != tsk))
            (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
      { intros.
        rewrite /total_ohep_workload /workload_of_jobs /other_higher_eq_priority.
        rewrite /jlfp_higher_eq_priority /FP_to_JLFP /same_task H_job_of_tsk.
        have EXCHANGE := exchange_big_dep (fun x => hep_task (job_task x) tsk && (job_task x != tsk)).
        rewrite EXCHANGE /=; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)) /=; first by rewrite HP0 andTb eq_refl; apply leq_addr.
          by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset.
      }
      apply leq_sum_seq; intros tsk0 INtsk0 HP0.
      apply leq_trans with
          (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + delta))).
      { rewrite -sum1_size big_distrr /= big_filter.
        rewrite /workload_of_jobs.
        rewrite  muln1 /l /arrivals_between /arrival_sequence.arrivals_between.
        apply leq_sum_seq; move => j0 IN0 /eqP EQ.
          by rewrite -EQ; apply H_valid_job_cost; apply in_arrivals_implies_arrived in IN0.
      }
      { rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[delta](addKn t).
          by apply H_is_arrival_bound; last rewrite leq_addr.
      }
    Qed.

    (** Next, we prove that total workload of tasks with higher-or-equal
        priority is no larger than the total request bound function. *)
    Lemma total_workload_le_total_rbf':
      total_hep_workload t (t + delta) <= total_hep_rbf delta.
    Proof.
      set l := arrivals_between arr_seq t (t + delta).
      apply leq_trans with
          (n := \sum_(tsk' <- ts | hep_task tsk' tsk)
                 (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
      { rewrite /total_hep_workload /jlfp_higher_eq_priority /FP_to_JLFP H_job_of_tsk.
        have EXCHANGE := exchange_big_dep (fun x => hep_task (job_task x) tsk).
        rewrite EXCHANGE /=; clear EXCHANGE; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)) /=; first by rewrite HP0 andTb eq_refl; apply leq_addr.
          by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset.
      }
      apply leq_sum_seq; intros tsk0 INtsk0 HP0.
      apply leq_trans with
          (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + delta))).
      { rewrite -sum1_size big_distrr /= big_filter.
        rewrite -/l /workload_of_jobs.
        rewrite muln1.
        apply leq_sum_seq; move => j0 IN0 /eqP EQ.
        rewrite -EQ.
        apply H_valid_job_cost.
          by apply in_arrivals_implies_arrived in IN0.
      }
      { rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[delta](addKn t).
          by apply H_is_arrival_bound; last rewrite leq_addr.
      }
    Qed.

    (** Next, we prove that total workload of tasks is no larger than the total
        request bound function. *)
    Lemma total_workload_le_total_rbf'':
      total_workload t (t + delta) <= total_rbf delta.
    Proof.
      set l := arrivals_between arr_seq t (t + delta).
      apply leq_trans with
          (n := \sum_(tsk' <- ts)
                 (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
      { rewrite /total_workload.
        have EXCHANGE := exchange_big_dep predT.
        rewrite EXCHANGE /=; clear EXCHANGE; last by done.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)) /=.
        rewrite eq_refl; apply leq_addr.
          by apply in_arrivals_implies_arrived in IN0;
            apply H_all_jobs_from_taskset.
      }
      apply leq_sum_seq; intros tsk0 INtsk0 HP0.
      apply leq_trans with
          (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + delta))).
      { rewrite -sum1_size big_distrr /= big_filter.
        rewrite -/l /workload_of_jobs.
        rewrite muln1.
        apply leq_sum_seq; move => j0 IN0 /eqP EQ.
        rewrite -EQ.
        apply H_valid_job_cost.
          by apply in_arrivals_implies_arrived in IN0.
      }
      { rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[delta](addKn t).
          by apply H_is_arrival_bound; last rewrite leq_addr.
      }
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

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in ts
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) it is a monotonic function
     that equals 0 for the empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_arrival_curve tsk (max_arrivals tsk).
  Hypothesis H_is_arrival_curve : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.

  (** We prove that [task_rbf 0] is equal to 0. *)
  Lemma task_rbf_0_zero:
    task_rbf 0 = 0.
  Proof.
    rewrite /task_rbf /task_request_bound_function.
    apply/eqP; rewrite muln_eq0; apply/orP; right; apply/eqP.
      by move: H_valid_arrival_curve => [T1 T2].
  Qed.

  (** We prove that [task_rbf] is monotone. *)
  Lemma task_rbf_monotone:
    monotone task_rbf leq.
  Proof.
    rewrite /monotone; intros ? ? LE.
    rewrite /task_rbf /task_request_bound_function leq_mul2l.
    apply/orP; right.
      by move: H_valid_arrival_curve => [_ T]; apply T.
  Qed.

  (** Consider any job j of [tsk]. This guarantees that there exists at least one
      job of task [tsk]. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_task j = tsk.

  (** Then we prove that [task_rbf 1] is greater than or equal to task cost. *)
  Lemma task_rbf_1_ge_task_cost:
    task_rbf 1 >= task_cost tsk.
  Proof.
    have ALT: forall n, n = 0 \/ n > 0
      by clear; intros n; destruct n; [left | right].
    specialize (ALT (task_cost tsk)); destruct ALT as [Z | POS]; first by rewrite Z.
    rewrite leqNgt; apply/negP; intros CONTR.
    move: H_is_arrival_curve => ARRB.
    specialize (ARRB (job_arrival j) (job_arrival j + 1)).
    feed ARRB; first by rewrite leq_addr.
    rewrite addKn in ARRB.
    move: CONTR; rewrite /task_rbf /task_request_bound_function; move => CONTR.
    move: CONTR; rewrite -{2}[task_cost tsk]muln1 ltn_mul2l; move => /andP [_ CONTR].
    move: CONTR; rewrite -addn1 -{3}[1]add0n leq_add2r leqn0; move => /eqP CONTR.
    move: ARRB; rewrite CONTR leqn0 eqn0Ngt; move => /negP T; apply: T.
    rewrite /number_of_task_arrivals -has_predT.
    rewrite /task_arrivals_between.
    apply/hasP; exists j; last by done.
    rewrite /arrivals_between addn1 big_nat_recl; last by done.
    rewrite big_geq ?cats0; last by done.
    rewrite mem_filter.
    apply/andP; split.
    - by apply/eqP.
    - move: H_j_arrives => [t ARR].
      move: (ARR) => CONS.
      apply H_arrival_times_are_consistent in CONS.
      by rewrite CONS.
  Qed.

End RequestBoundFunctions.
