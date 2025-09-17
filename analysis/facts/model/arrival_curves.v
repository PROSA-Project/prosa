Require Export prosa.util.epsilon.
Require Export prosa.model.priority.classes.
Require Export prosa.model.task.arrival.curves.
Require Export prosa.analysis.facts.model.task_arrivals.

(** * Facts About Arrival Curves *)

(** We observe that tasks that exhibit job arrivals must have non-pathological
    arrival curves. This allows excluding pathological cases in higher-level
    proofs. *)
Section NonPathologicalCurve.

  (** Consider any kind of tasks characterized by an upper-bounding arrival curve... *)
  Context {Task : TaskType} `{MaxArrivals Task}.
  (** ... and the corresponding type of jobs. *)
  Context {Job : JobType} `{JobTask Job Task}.

  (** Consider an arbitrary task ... *)
  Variable tsk : Task.

  (** ... and an arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... that is compliant with the upper-bounding arrival curve. *)
  Hypothesis H_curve_is_valid : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  (** If we have evidence that a job of the task [tsk] ... *)
  Variable j : Job.
  Hypothesis H_job_of_tsk : job_of_task tsk j.

  (** ... arrives at any point in time, ... *)
  Hypothesis H_arrives : arrives_in arr_seq j.

  (** ... then the maximum number of job arrivals in a non-empty interval cannot
      be zero. *)
  Lemma non_pathological_max_arrivals :
    max_arrivals tsk ε > 0.
  Proof.
    move: (H_arrives) => [t ARR].
    move: (H_curve_is_valid t t.+1 ltac:(by done)).
    rewrite -addn1 -addnBAC // addnBl_leq // => VALID.
    apply: (leq_trans _ VALID).
    rewrite /number_of_task_arrivals size_of_task_arrivals_between.
    rewrite big_ltn addn1 // big_geq // addn0.
    rewrite /task_arrivals_at size_filter //= -has_count.
    by apply /hasP; exists j.
  Qed.

End NonPathologicalCurve.

(** We add the above lemma to the global hints database. *)
Global Hint Resolve non_pathological_max_arrivals : basic_rt_facts.

(** In the following section, we prove a bound on the number of
    arrivals within a given interval under an arbitrary JLFP
    policy. *)
Section JLFPArrivalBounds.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{MaxArrivals Task}.

  (** ... and the corresponding type of jobs. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JLFP_policy Job}.

  (** Consider any kind of processor state model... *)
  Context {PState : ProcessorState Job}.

  (** ... and arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrival tsk] is an arrival bound of
      [tsk]. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** We prove that the number of jobs that arrive in the interval
      <<[t1, t1 + Δ)>> and have higher-or-equal priority than a given
      job [j] is bounded by the sum of arrival curves for all tasks in
      [ts]. *)
  Lemma jlfp_hep_arrivals_bounded_by_sum_max_arrivals :
    forall (j : Job) (t1 : instant) (Δ : duration),
      size [seq jhp <- arrivals_between arr_seq t1 (t1 + Δ) | hep_job jhp j]
      <= \sum_(tsk <- ts) max_arrivals tsk Δ.
  Proof.
    move=> j t1 Δ; rewrite -sum1_size big_filter.
    apply leq_trans with (\sum_(i <- arrivals_between arr_seq t1 (t1 + Δ)) 1).
    { by rewrite big_mkcond //=; apply leq_sum; move => i _ ; destruct hep_job. }
    apply: leq_trans.
    { apply sum_over_partitions_le with (x_to_y := job_task) (ys := ts) => s IN HEP.
      by eapply H_all_jobs_from_taskset, in_arrivals_implies_arrived => //. }
    { rewrite big_seq_cond [leqRHS]big_seq_cond; apply leq_sum => tsk /andP [IN _].
      rewrite -big_filter sum1_size -{2}[Δ](addKn t1).
      apply:leq_trans; last by apply H_is_arrival_curve => //; lia.
      by rewrite /number_of_task_arrivals /task_arrivals_between -sum1_size big_filter. }
  Qed.

End JLFPArrivalBounds.

(** In this section, we prove a bound on the number of arrivals within
    a given interval under an FP policy. *)
Section FPArrivalBounds.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{MaxArrivals Task}.

  (** ... and their associated jobs. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Allow for any fixed-priority policy. *)
  Context `{FP_policy Task}.

  (** Consider any kind of processor state model... *)
  Context {PState : ProcessorState Job}.

  (** ... and arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for
      any task [tsk] in [ts], [max_arrival tsk] is an arrival bound of
      [tsk]. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** We prove that the number of jobs that arrive in the interval
      <<[t1, t1 + Δ)>> and have higher-or-equal priority than a given
      job [j] is bounded by the sum of arrival curves of all tasks in
      [ts] whose priority is higher than or equal to that of [j]’s
      task. *)
  Lemma fp_hep_arrivals_bounded_by_sum_max_arrivals :
    forall (j : Job) (t1 : instant) (Δ : duration),
      size [seq jhp <- arrivals_between arr_seq t1 (t1 + Δ) | hep_job jhp j]
      <= \sum_(tsk <- ts | hep_task tsk (job_task j)) max_arrivals tsk Δ.
  Proof.
    move=> j t1 Δ; rewrite -sum1_size big_filter.
    apply leq_trans with (
        \sum_(i <- arrivals_between arr_seq t1 (t1 + Δ) | hep_task (job_task i) (job_task j)) 1
      ).
    { by rewrite big_mkcond //=; apply leq_sum; move => i _ ; destruct hep_job. }
    apply: leq_trans.
    { apply sum_over_partitions_le with (x_to_y := job_task) (ys := ts) => s IN HEP.
      by eapply H_all_jobs_from_taskset, in_arrivals_implies_arrived => //. }
    { rewrite big_seq_cond [leqRHS]big_seq_cond.
      rewrite big_mkcond [leqRHS]big_mkcond //=; apply leq_sum => tsk _.
      destruct (tsk \in ts) eqn:IN; last by done.
      rewrite //=; destruct (hep_task tsk (job_task j)) eqn:HEP.
      { rewrite -big_filter sum1_size -{2}[Δ](addKn t1).
        apply: leq_trans; last eapply H_is_arrival_curve.
        { rewrite /number_of_task_arrivals /task_arrivals_between -!sum1_size !big_filter.
          rewrite big_seq_cond [leqRHS]big_seq_cond.
          rewrite big_mkcond [leqRHS]big_mkcond //=.
          apply leq_sum => s _; rewrite /job_of_task.
          by destruct (_ == _), (s \in _ ), (hep_task _ _), (hep_task _ _) => //.
        }
        { by done. }
        { by lia. }
      }
      { rewrite big_seq_cond leqn0; apply/eqP; apply big1 => s /andP [INs /andP [HEPs /eqP EQs]].
        by subst tsk; rewrite HEP in HEPs.
      }
    }
  Qed.

End FPArrivalBounds.
