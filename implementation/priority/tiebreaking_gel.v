Require Import prosa.util.int.
Require Export prosa.implementation.priority.gel.
Require Export prosa.implementation.priority.tiebreaks_by_id.

(** * GEL Priority Policy with Tie-Breaking *)

(** This GEL implementation resolves equal absolute priority points by favoring
    lower task IDs, and then lower job IDs. *)
Section TiebreakingGEL.

  (** Consider tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{TaskId Task}.

  (** ... and their jobs, with absolute priority points and numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobPriorityPoint Job} `{JobId Job}.

  (** We apply identifier-based tie-breaking to GEL's priority-point order. *)
  #[local] Instance tiebreaking_gel : JLFP_policy Job :=
    tiebreaks_by_id (GEL Job).

  (** The following facts connect the implementation to the generic priority
      interface used by schedulers and analyses. *)

  (** We expose the comparison rule for use in proofs about this policy. *)
  Fact tiebreaking_gel_hep_job :
    forall j1 j2,
      @hep_job Job tiebreaking_gel j1 j2
      = ((job_priority_point j1 < job_priority_point j2)%R
         || ((job_priority_point j1 == job_priority_point j2)
             && ((task_id (job_task j1) < task_id (job_task j2))
                 || ((task_id (job_task j1) == task_id (job_task j2))
                     && (job_id j1 <= job_id j2))))).
  Proof.
    move=> j1 j2; rewrite /tiebreaking_gel tiebreaks_by_id_hep_job !GEL_hep_job.
    by case: (ltrgtP (job_priority_point j1) (job_priority_point j2)) => [LT|LT|EQ] //=.
  Qed.

  (** Every job has at least its own priority. *)
  Fact tiebreaking_gel_is_reflexive :
    reflexive_job_priorities tiebreaking_gel.
  Proof. apply: tiebreaks_by_id_is_reflexive; exact: GEL_is_reflexive. Qed.

  (** Priority comparisons remain consistent across chains of jobs. *)
  Fact tiebreaking_gel_is_transitive :
    transitive_job_priorities tiebreaking_gel.
  Proof. apply: tiebreaks_by_id_is_transitive; exact: GEL_is_transitive. Qed.

  (** The scheduler can compare every pair of jobs. *)
  Fact tiebreaking_gel_is_total :
    total_job_priorities tiebreaking_gel.
  Proof. apply: tiebreaks_by_id_is_total; exact: GEL_is_total. Qed.

  (** Valid job identifiers make the final tie-breaking step unambiguous for
      arriving jobs. *)
  Fact tiebreaking_gel_is_antisymmetric :
    forall arr_seq,
      valid_job_ids arr_seq ->
      antisymmetric_job_priorities tiebreaking_gel arr_seq.
  Proof. exact: tiebreaks_by_id_is_antisymmetric. Qed.

  (** The tie-breaking rule preserves GEL's priority-point order and satisfies
      the priority properties required by GEL analyses. *)
  Fact tiebreaking_gel_is_gel_policy :
    policy_is_GEL tiebreaking_gel.
  Proof.
    repeat split.
    - move=> j1 j2; rewrite -GEL_hep_job.
      exact: tiebreaks_by_id_respects_primary_priority.
    - exact: tiebreaking_gel_is_reflexive.
    - exact: tiebreaking_gel_is_transitive.
    - exact: tiebreaking_gel_is_total.
  Qed.

End TiebreakingGEL.

(** The identifier tie-breaks repeat together with GEL's priority-point order. *)
Section HyperperiodPriorities.

  (** Consider periodic tasks with relative priority points and numeric
      identifiers ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{PriorityPoint Task} `{TaskId Task}.

  (** ... and jobs with task-derived absolute priority points and numeric
      identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobId Job}.

  (** Consider a task set with valid periods and unique task identifiers ... *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.
  Hypothesis H_valid_task_ids : valid_task_ids ts.

  (** ... generating a valid arrival sequence of these tasks ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... with periodic releases continuing indefinitely. *)
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.

  (** Unique task IDs preserve ties between tasks. Within a task, equal priority
      points identify the same release, whose job-ID comparison is reflexive. *)
  Fact tiebreaking_gel_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq tiebreaking_gel.
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite /tiebreaking_gel !tiebreaks_by_id_hep_job
      !(GEL_priorities_consistent_across_hyperperiods ts H_valid_periods arr_seq) //
      !next_hyperperiod_job_task !GEL_hep_job.
    case IDS: (task_id (job_task j1) == task_id (job_task j2)); last by [].
    case: (ltrgtP (job_priority_point j1) (job_priority_point j2)) => [LT|LT|EQ] //=.
    have TSK : job_task j1 = job_task j2 by apply: H_valid_task_ids => //; exact: eqP.
    have -> : j1 = j2.
    { apply/(same_jobs_iff_same_arr arr_seq H_valid_arrival_sequence (job_task j1)) => //.
      - exact: periodic_task_respects_sporadic_task_model.
      - by move: EQ; rewrite /job_priority_point /jpp_from_tpp -TSK; lia. }
    by rewrite !leqnn !orbT.
  Qed.

End HyperperiodPriorities.

(** We register the policy facts so Rocq can apply them automatically. *)
Global Hint Resolve
  tiebreaking_gel_is_gel_policy
  tiebreaking_gel_is_reflexive
  tiebreaking_gel_is_transitive
  tiebreaking_gel_is_total
  tiebreaking_gel_is_antisymmetric
  tiebreaking_gel_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
