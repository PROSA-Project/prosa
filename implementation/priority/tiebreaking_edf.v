Require Export prosa.implementation.priority.edf.
Require Export prosa.implementation.priority.tiebreaks_by_id.

(** * EDF Priority Policy with Tie-Breaking *)

(** This EDF implementation resolves equal absolute deadlines by favoring lower
    task IDs, and then lower job IDs. *)
Section TiebreakingEDF.

  (** Consider tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{TaskId Task}.

  (** ... and their jobs, with absolute deadlines and numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobDeadline Job} `{JobId Job}.

  (** We apply identifier-based tie-breaking to EDF's deadline order. *)
  #[local] Instance tiebreaking_edf : JLFP_policy Job :=
    tiebreaks_by_id (EDF Job).

  (** The following facts connect the implementation to the generic priority
      interface used by schedulers and analyses. *)

  (** We expose the comparison rule for use in proofs about this policy. *)
  Fact tiebreaking_edf_hep_job :
    forall j1 j2,
      @hep_job Job tiebreaking_edf j1 j2
      = ((job_deadline j1 < job_deadline j2)
         || ((job_deadline j1 == job_deadline j2)
             && ((task_id (job_task j1) < task_id (job_task j2))
                 || ((task_id (job_task j1) == task_id (job_task j2))
                     && (job_id j1 <= job_id j2))))).
  Proof.
    move=> j1 j2; rewrite /tiebreaking_edf tiebreaks_by_id_hep_job !EDF_hep_job.
    by apply/idP/idP; move=> HEP; lia.
  Qed.

  (** Every job has at least its own priority. *)
  Fact tiebreaking_edf_is_reflexive :
    reflexive_job_priorities tiebreaking_edf.
  Proof. apply: tiebreaks_by_id_is_reflexive; exact: EDF_is_reflexive. Qed.

  (** Priority comparisons remain consistent across chains of jobs. *)
  Fact tiebreaking_edf_is_transitive :
    transitive_job_priorities tiebreaking_edf.
  Proof. apply: tiebreaks_by_id_is_transitive; exact: EDF_is_transitive. Qed.

  (** The scheduler can compare every pair of jobs. *)
  Fact tiebreaking_edf_is_total :
    total_job_priorities tiebreaking_edf.
  Proof. apply: tiebreaks_by_id_is_total; exact: EDF_is_total. Qed.

  (** Valid job identifiers make the final tie-breaking step unambiguous for
      arriving jobs. *)
  Fact tiebreaking_edf_is_antisymmetric :
    forall arr_seq,
      valid_job_ids arr_seq ->
      antisymmetric_job_priorities tiebreaking_edf arr_seq.
  Proof. exact: tiebreaks_by_id_is_antisymmetric. Qed.

  (** The tie-breaking rule preserves EDF's deadline order and satisfies the
      priority properties required by EDF analyses. *)
  Fact tiebreaking_edf_is_edf_policy :
    policy_is_EDF tiebreaking_edf.
  Proof.
    repeat split.
    - move=> j1 j2; rewrite -EDF_hep_job.
      exact: tiebreaks_by_id_respects_primary_priority.
    - exact: tiebreaking_edf_is_reflexive.
    - exact: tiebreaking_edf_is_transitive.
    - exact: tiebreaking_edf_is_total.
  Qed.

End TiebreakingEDF.

(** The identifier tie-breaks repeat together with EDF's deadline order. *)
Section HyperperiodPriorities.

  (** Consider periodic tasks with relative deadlines and numeric identifiers ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{TaskDeadline Task} `{TaskId Task}.

  (** ... and jobs with task-derived absolute deadlines and numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobId Job}.

  (** We name the task-derived absolute deadline for clarity. *)
  Let absolute_deadline (j : Job) := job_arrival j + task_deadline (job_task j).

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

  (** Unique task IDs preserve ties between tasks. Within a task, equal deadlines
      identify the same release, whose job-ID comparison is reflexive. *)
  Fact tiebreaking_edf_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq tiebreaking_edf.
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite /tiebreaking_edf !tiebreaks_by_id_hep_job
      !(EDF_priorities_consistent_across_hyperperiods ts H_valid_periods arr_seq) //
      !next_hyperperiod_job_task !EDF_hep_job
      /job_deadline /job_deadline_from_task_deadline.
    case IDS: (task_id (job_task j1) == task_id (job_task j2)); last by [].
    case DL: (absolute_deadline j1 == absolute_deadline j2).
    - have TSK : job_task j1 = job_task j2 by apply: H_valid_task_ids => //; exact: eqP.
      have -> : j1 = j2.
      { apply/(same_jobs_iff_same_arr arr_seq H_valid_arrival_sequence (job_task j1)) => //.
        - exact: periodic_task_respects_sporadic_task_model.
        - by move: DL; rewrite /absolute_deadline -TSK eqn_add2r => /eqP. }
      by rewrite !leqnn !orbT.
    - by apply/idP/idP; move=> HEP; move: DL; rewrite /absolute_deadline; lia.
  Qed.

End HyperperiodPriorities.

(** We register the policy facts so Rocq can apply them automatically. *)
Global Hint Resolve
  tiebreaking_edf_is_edf_policy
  tiebreaking_edf_is_reflexive
  tiebreaking_edf_is_transitive
  tiebreaking_edf_is_total
  tiebreaking_edf_is_antisymmetric
  tiebreaking_edf_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
