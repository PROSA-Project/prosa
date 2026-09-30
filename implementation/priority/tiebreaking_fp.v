Require Export prosa.model.priority.fp.
Require Export prosa.implementation.priority.tiebreaks_by_id.
Require Export prosa.analysis.facts.hyperperiod.

(** * Fixed-Priority Policy with Tie-Breaking *)

(** This implementation refines any task-level fixed-priority policy by
    favoring lower task IDs, and then lower job IDs, among equal priorities. *)
Section TiebreakingFP.

  (** Consider tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{TaskId Task}.

  (** ... and their jobs, also with numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobId Job}.

  (** The supplied task-level policy determines the primary priority order. *)
  Variable FP : FP_policy Task.

  (** We lift task priorities to jobs and resolve ties through the ID adapter. *)
  #[local] Instance tiebreaking_fp : JLFP_policy Job :=
    tiebreaks_by_id (fp_to_jlfp FP).

  (** We expose the comparison rule for use in proofs about this policy. *)
  Fact tiebreaking_fp_hep_job :
    forall j1 j2,
      @hep_job Job tiebreaking_fp j1 j2
      = (hep_task (job_task j1) (job_task j2)
         && (~~ hep_task (job_task j2) (job_task j1)
             || (task_id (job_task j1) < task_id (job_task j2))
             || ((task_id (job_task j1) == task_id (job_task j2))
                 && (job_id j1 <= job_id j2)))).
  Proof. by []. Qed.

  (** Valid job identifiers make the final tie-breaking step unambiguous for
      arriving jobs. *)
  Fact tiebreaking_fp_is_antisymmetric :
    forall arr_seq,
      valid_job_ids arr_seq ->
      antisymmetric_job_priorities tiebreaking_fp arr_seq.
  Proof. exact: tiebreaks_by_id_is_antisymmetric. Qed.

  (** Assume each task has at least its own priority. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.

  (** The refinement preserves reflexivity at the job level. *)
  Fact tiebreaking_fp_is_reflexive : reflexive_job_priorities tiebreaking_fp.
  Proof.
    apply: tiebreaks_by_id_is_reflexive.
    exact: reflexive_priorities_FP_implies_JLFP.
  Qed.

  (** Assume task comparisons remain consistent across chains of tasks. *)
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.

  (** The refinement preserves transitivity at the job level. *)
  Fact tiebreaking_fp_is_transitive : transitive_job_priorities tiebreaking_fp.
  Proof.
    apply: tiebreaks_by_id_is_transitive.
    exact: transitive_priorities_FP_implies_JLFP.
  Qed.

  (** Assume every pair of tasks can be compared. *)
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** The refinement lets the scheduler compare every pair of jobs. *)
  Fact tiebreaking_fp_is_total : total_job_priorities tiebreaking_fp.
  Proof.
    apply: tiebreaks_by_id_is_total.
    exact: total_priorities_FP_implies_JLFP.
  Qed.

  (** Preserving task priorities and their strict comparisons makes the refined
      job order an FP policy with respect to the supplied task order. *)
  Fact tiebreaking_fp_is_fp_policy : policy_is_FP FP tiebreaking_fp.
  Proof.
    repeat split.
    - exact: tiebreaks_by_id_respects_primary_priority.
    - move=> j1 j2 /andP [HEP STRICT].
      exact: tiebreaks_by_id_preserves_strict_priority.
    - exact: tiebreaking_fp_is_reflexive.
    - exact: tiebreaking_fp_is_transitive.
    - exact: tiebreaking_fp_is_total.
  Qed.

End TiebreakingFP.

(** Monotonic job IDs make tie-breaking repeat with the periodic workload. *)
Section HyperperiodPriorities.

  (** Consider periodic tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{TaskId Task}.

  (** ... and their jobs, with arrival times and numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobId Job}.

  (** The primary task-priority order is arbitrary. *)
  Variable FP : FP_policy Task.

  (** Consider a task set with valid periods and unique task identifiers ... *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.
  Hypothesis H_valid_task_ids : valid_task_ids ts.

  (** ... generating a valid arrival sequence of jobs of these tasks ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... with periodic releases continuing indefinitely. *)
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.

  (** Suppose that, w.r.t. each task, later arrivals have larger job IDs. *)
  Hypothesis H_monotonic_job_ids : monotonic_job_ids arr_seq.

  (** For jobs sharing a task ID, monotonic identifiers recover arrival order
      since periodic tasks release a single job at each release instant. *)
  Local Lemma job_id_order_matches_arrival_order :
    forall j1 j2,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      task_id (job_task j1) = task_id (job_task j2) ->
      (job_id j1 <= job_id j2) = (job_arrival j1 <= job_arrival j2).
  Proof.
    move=> j1 j2 ARR1 ARR2 IDS.
    case: (ltngtP (job_arrival j1) (job_arrival j2)) => [LT|LT|EQ].
    - by rewrite (ltnW (H_monotonic_job_ids j1 j2 ARR1 ARR2 IDS LT)).
    - by rewrite leqNgt (H_monotonic_job_ids j2 j1 ARR2 ARR1 (esym IDS) LT).
    - suff -> : j1 = j2 by rewrite !leqnn.
      apply/(same_jobs_iff_same_arr arr_seq H_valid_arrival_sequence (job_task j1)) => //.
      exact: periodic_task_respects_sporadic_task_model.
  Qed.

  (** A hyperperiod shift preserves task priorities, task IDs, and the arrival
      order used by the final job-ID tie-break. *)
  Fact tiebreaking_fp_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq (tiebreaking_fp FP).
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite !tiebreaking_fp_hep_job !next_hyperperiod_job_task.
    case IDS: (task_id (job_task j1) == task_id (job_task j2)); last by [].
    rewrite !job_id_order_matches_arrival_order ?next_hyperperiod_job_task //;
      try exact: eqP IDS.
    - by apply: (next_hyperperiod_job_arrives arr_seq _ ts (job_task j1)).
    - by apply: (next_hyperperiod_job_arrives arr_seq _ ts (job_task j2)).
    - rewrite (next_hyperperiod_job_arrival arr_seq _ ts (job_task j1)) //
        (next_hyperperiod_job_arrival arr_seq _ ts (job_task j2)) //.
      by rewrite leq_add2r.
  Qed.

End HyperperiodPriorities.

(** We register the policy facts so Rocq can apply them automatically. *)
Global Hint Resolve
  tiebreaking_fp_is_fp_policy
  tiebreaking_fp_is_reflexive
  tiebreaking_fp_is_transitive
  tiebreaking_fp_is_total
  tiebreaking_fp_is_antisymmetric
  tiebreaking_fp_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
