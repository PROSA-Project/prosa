Require Export prosa.implementation.priority.fifo.
Require Export prosa.implementation.priority.tiebreaks_by_id.

(** * FIFO Priority Policy with Tie-Breaking *)

(** This FIFO implementation resolves equal arrival times by favoring lower
    task IDs, and then lower job IDs. *)
Section TiebreakingFIFO.

  (** Consider tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{TaskId Task}.

  (** ... and their jobs, with arrival times and numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobId Job}.

  (** We apply identifier-based tie-breaking to FIFO's arrival order. *)
  #[local] Instance tiebreaking_fifo : JLFP_policy Job :=
    tiebreaks_by_id (FIFO Job).

  (** The following facts connect the implementation to the generic priority
      interface used by schedulers and analyses. *)

  (** We expose the comparison rule for use in proofs about this policy. *)
  Fact tiebreaking_fifo_hep_job :
    forall j1 j2,
      @hep_job Job tiebreaking_fifo j1 j2
      = ((job_arrival j1 < job_arrival j2)
         || ((job_arrival j1 == job_arrival j2)
             && ((task_id (job_task j1) < task_id (job_task j2))
                 || ((task_id (job_task j1) == task_id (job_task j2))
                     && (job_id j1 <= job_id j2))))).
  Proof.
    move=> j1 j2; rewrite /tiebreaking_fifo tiebreaks_by_id_hep_job !FIFO_hep_job.
    by apply/idP/idP; move=> HEP; lia.
  Qed.

  (** Every job has at least its own priority. *)
  Fact tiebreaking_fifo_is_reflexive :
    reflexive_job_priorities tiebreaking_fifo.
  Proof. apply: tiebreaks_by_id_is_reflexive; exact: FIFO_is_reflexive. Qed.

  (** Priority comparisons remain consistent across chains of jobs. *)
  Fact tiebreaking_fifo_is_transitive :
    transitive_job_priorities tiebreaking_fifo.
  Proof. apply: tiebreaks_by_id_is_transitive; exact: FIFO_is_transitive. Qed.

  (** The scheduler can compare every pair of jobs. *)
  Fact tiebreaking_fifo_is_total :
    total_job_priorities tiebreaking_fifo.
  Proof. apply: tiebreaks_by_id_is_total; exact: FIFO_is_total. Qed.

  (** Valid job identifiers make the final tie-breaking step unambiguous for
      arriving jobs. *)
  Fact tiebreaking_fifo_is_antisymmetric :
    forall arr_seq,
      valid_job_ids arr_seq ->
      antisymmetric_job_priorities tiebreaking_fifo arr_seq.
  Proof. exact: tiebreaks_by_id_is_antisymmetric. Qed.

  (** The tie-breaking rule preserves FIFO's arrival order and satisfies the
      priority properties required by FIFO analyses. *)
  Fact tiebreaking_fifo_is_fifo_policy :
    policy_is_FIFO tiebreaking_fifo.
  Proof.
    repeat split.
    - move=> j1 j2; rewrite -FIFO_hep_job.
      exact: tiebreaks_by_id_respects_primary_priority.
    - exact: tiebreaking_fifo_is_reflexive.
    - exact: tiebreaking_fifo_is_transitive.
    - exact: tiebreaking_fifo_is_total.
  Qed.

End TiebreakingFIFO.

(** The identifier tie-breaks repeat together with FIFO's arrival order. *)
Section HyperperiodPriorities.

  (** Consider periodic tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{TaskId Task}.

  (** ... and jobs with arrival times and numeric identifiers. *)
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

  (** Unique task IDs preserve ties between tasks. Within a task, equal arrival
      times identify the same release, whose job-ID comparison is reflexive. *)
  Fact tiebreaking_fifo_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq tiebreaking_fifo.
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite /tiebreaking_fifo !tiebreaks_by_id_hep_job
      !(FIFO_priorities_consistent_across_hyperperiods ts H_valid_periods arr_seq) //
      !next_hyperperiod_job_task !FIFO_hep_job.
    case IDS: (task_id (job_task j1) == task_id (job_task j2)); last by [].
    case: (ltngtP (job_arrival j1) (job_arrival j2)) => [LT|LT|EQ] //=.
    have -> : j1 = j2.
    { apply/(same_jobs_iff_same_arr arr_seq H_valid_arrival_sequence (job_task j1)) => //.
      - exact: periodic_task_respects_sporadic_task_model.
      - by apply: H_valid_task_ids => //; exact: eqP. }
    by rewrite !leqnn !orbT.
  Qed.

End HyperperiodPriorities.

(** We register the policy facts so Rocq can apply them automatically. *)
Global Hint Resolve
  tiebreaking_fifo_is_fifo_policy
  tiebreaking_fifo_is_reflexive
  tiebreaking_fifo_is_transitive
  tiebreaking_fifo_is_total
  tiebreaking_fifo_is_antisymmetric
  tiebreaking_fifo_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
