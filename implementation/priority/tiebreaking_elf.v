Require Export prosa.implementation.priority.elf.
Require Export prosa.implementation.priority.tiebreaks_by_id.
Require Export prosa.analysis.facts.priority.elf.

(** * ELF Priority Policy with Tie-Breaking *)

(** This implementation refines ELF over any task-level FP policy by favoring
    lower task IDs, and then lower job IDs, among equal priorities. *)
Section TiebreakingELF.

  (** Consider tasks with relative priority points and numeric identifiers ... *)
  Context {Task : TaskType} `{PriorityPoint Task} `{TaskId Task}.

  (** ... and their jobs, with arrival times and numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobId Job}.

  (** The supplied task-level policy determines the primary priority order. *)
  Variable FP : FP_policy Task.

  (** We resolve ties in ELF's task and priority-point orders by identifier. *)
  #[local] Instance tiebreaking_elf : JLFP_policy Job :=
    tiebreaks_by_id (ELF FP).

  (** We expose the comparison rule for use in proofs about this policy. *)
  Fact tiebreaking_elf_hep_job :
    forall j1 j2,
      @hep_job Job tiebreaking_elf j1 j2
      = (hp_task (job_task j1) (job_task j2)
         || (ep_task (job_task j1) (job_task j2)
             && ((job_priority_point j1 < job_priority_point j2)%R
                 || ((job_priority_point j1 == job_priority_point j2)
                     && ((task_id (job_task j1) < task_id (job_task j2))
                         || ((task_id (job_task j1) == task_id (job_task j2))
                             && (job_id j1 <= job_id j2))))))).
  Proof.
    move=> j1 j2; rewrite /tiebreaking_elf tiebreaks_by_id_hep_job !ELF_hep_job
      /hp_task /ep_task.
    case: (hep_task (job_task j1) (job_task j2));
      case: (hep_task (job_task j2) (job_task j1)) => //=.
    by apply/idP/idP; move=> HEP; lia.
  Qed.

  (** Valid job identifiers make the final tie-breaking step unambiguous for
      arriving jobs. *)
  Fact tiebreaking_elf_is_antisymmetric :
    forall arr_seq,
      valid_job_ids arr_seq ->
      antisymmetric_job_priorities tiebreaking_elf arr_seq.
  Proof. exact: tiebreaks_by_id_is_antisymmetric. Qed.

  (** Assume each task has at least its own priority. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.

  (** The refinement preserves reflexivity at the job level. *)
  Fact tiebreaking_elf_is_reflexive : reflexive_job_priorities tiebreaking_elf.
  Proof. apply: tiebreaks_by_id_is_reflexive; exact: ELF_is_reflexive. Qed.

  (** Assume task comparisons remain consistent across chains of tasks. *)
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.

  (** The refinement preserves transitivity at the job level. *)
  Fact tiebreaking_elf_is_transitive : transitive_job_priorities tiebreaking_elf.
  Proof. apply: tiebreaks_by_id_is_transitive; exact: ELF_is_transitive. Qed.

  (** Assume every pair of tasks can be compared. *)
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** The refinement lets the scheduler compare every pair of jobs. *)
  Fact tiebreaking_elf_is_total : total_job_priorities tiebreaking_elf.
  Proof. apply: tiebreaks_by_id_is_total; exact: ELF_is_total. Qed.

  (** Preserving task priorities and priority-point order makes the refinement
      an ELF policy with respect to the supplied task order. *)
  Fact tiebreaking_elf_is_elf_policy : policy_is_ELF FP tiebreaking_elf.
  Proof.
    repeat split.
    - move=> j1 j2 HEP.
      apply: (ELF_policy_task_priority_order (JLFP := ELF FP)) => //.
      exact: tiebreaks_by_id_respects_primary_priority.
    - move=> j1 j2 EP HEP.
      apply: (ELF_policy_priority_point_order (JLFP := ELF FP)) => //.
      exact: tiebreaks_by_id_respects_primary_priority.
    - exact: tiebreaking_elf_is_reflexive.
    - exact: tiebreaking_elf_is_transitive.
    - exact: tiebreaking_elf_is_total.
  Qed.

End TiebreakingELF.

(** The identifier tie-breaks repeat together with ELF's task and priority-point
    orders. *)
Section HyperperiodPriorities.

  (** Consider periodic tasks with relative priority points and numeric
      identifiers ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{PriorityPoint Task} `{TaskId Task}.

  (** ... and jobs with task-derived absolute priority points and numeric
      identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobId Job}.

  (** The primary task-priority order is arbitrary. *)
  Variable FP : FP_policy Task.

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
  Fact tiebreaking_elf_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq (tiebreaking_elf FP).
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite /tiebreaking_elf !tiebreaks_by_id_hep_job
      !(ELF_priorities_consistent_across_hyperperiods FP ts H_valid_periods arr_seq) //
      !next_hyperperiod_job_task !ELF_hep_job.
    case IDS: (task_id (job_task j1) == task_id (job_task j2)); last by [].
    have TSK : job_task j1 = job_task j2 by apply: H_valid_task_ids => //; exact: eqP.
    rewrite -TSK /hp_task !andbN /=.
    case: (hep_task (job_task j1) (job_task j1)) => //=.
    rewrite -TSK !lerD2r !ler_nat.
    case: (ltngtP (job_arrival j1) (job_arrival j2)) => [LT|LT|EQ] //=.
    have -> : j1 = j2.
    { apply/(same_jobs_iff_same_arr arr_seq H_valid_arrival_sequence (job_task j1)) => //.
      exact: periodic_task_respects_sporadic_task_model. }
    by rewrite !leqnn !orbT.
  Qed.

End HyperperiodPriorities.

(** We register the policy facts so Rocq can apply them automatically. *)
Global Hint Resolve
  tiebreaking_elf_is_elf_policy
  tiebreaking_elf_is_reflexive
  tiebreaking_elf_is_transitive
  tiebreaking_elf_is_total
  tiebreaking_elf_is_antisymmetric
  tiebreaking_elf_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
