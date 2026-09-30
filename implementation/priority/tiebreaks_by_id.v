Require Export prosa.model.priority.classes.
Require Export prosa.implementation.definitions.parameters.

(** * Breaking JLFP Priority Ties by Identifier *)

(** This adapter refines a given job-level fixed-priority policy by favoring
    lower task IDs, and then lower job IDs, among jobs of equal priority. *)
Section TiebreaksById.

  (** Consider tasks with numeric identifiers ... *)
  Context {Task : TaskType} `{TaskId Task}.

  (** ... and their jobs, also with numeric identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobId Job}.

  (** The supplied policy determines the primary priority order. *)
  Variable JLFP : JLFP_policy Job.

  (** We give its comparison rule a local name to distinguish primary priorities
      from those produced by the adapter. *)
  Let primary_hep_job := @hep_job Job JLFP.

  (** Strict primary priorities take precedence. When the primary policy grants
      priority in both directions, identifiers determine the order. *)
  #[local] Instance tiebreaks_by_id : JLFP_policy Job :=
  {
    hep_job (j1 j2 : Job) :=
      primary_hep_job j1 j2
      && (~~ primary_hep_job j2 j1
          || (task_id (job_task j1) < task_id (job_task j2))
          || ((task_id (job_task j1) == task_id (job_task j2))
              && (job_id j1 <= job_id j2)))
  }.

  (** We expose the adapter's comparison rule for use in scheduling proofs. *)
  Fact tiebreaks_by_id_hep_job :
    forall j1 j2,
      @hep_job Job tiebreaks_by_id j1 j2
      = (primary_hep_job j1 j2
         && (~~ primary_hep_job j2 j1
             || (task_id (job_task j1) < task_id (job_task j2))
             || ((task_id (job_task j1) == task_id (job_task j2))
                 && (job_id j1 <= job_id j2)))).
  Proof. by []. Qed.

  (** Every priority granted by the adapter respects the supplied policy. *)
  Fact tiebreaks_by_id_respects_primary_priority :
    forall j1 j2,
      @hep_job Job tiebreaks_by_id j1 j2 -> primary_hep_job j1 j2.
  Proof. by move=> j1 j2; rewrite tiebreaks_by_id_hep_job => /andP []. Qed.

  (** Strict priorities established by the supplied policy carry over. *)
  Fact tiebreaks_by_id_preserves_strict_priority :
    forall j1 j2,
      primary_hep_job j1 j2 ->
      ~~ primary_hep_job j2 j1 ->
      @hep_job Job tiebreaks_by_id j1 j2.
  Proof. by move=> j1 j2 HEP STRICT; rewrite tiebreaks_by_id_hep_job HEP STRICT. Qed.

  (** Valid job identifiers turn the adapter's priority order into an unambiguous
      choice among arriving jobs. *)
  Fact tiebreaks_by_id_is_antisymmetric :
    forall arr_seq,
      valid_job_ids arr_seq ->
      antisymmetric_job_priorities tiebreaks_by_id arr_seq.
  Proof.
    move=> arr_seq VALID j1 j2 ARR1 ARR2.
    rewrite !tiebreaks_by_id_hep_job => /andP [HEP12 TB12] /andP [HEP21 TB21].
    by apply: VALID => //; move: TB12 TB21; rewrite HEP12 HEP21 /=; lia.
  Qed.

  (** Assume the supplied policy gives every job at least its own priority. *)
  Hypothesis H_reflexive_priorities : reflexive_job_priorities JLFP.

  (** The adapter preserves reflexivity. *)
  Fact tiebreaks_by_id_is_reflexive : reflexive_job_priorities tiebreaks_by_id.
  Proof.
    move=> j; rewrite tiebreaks_by_id_hep_job ltnn eqxx leqnn !orbT andbT.
    exact: H_reflexive_priorities.
  Qed.

  (** Assume primary comparisons remain consistent across chains of jobs. *)
  Hypothesis H_transitive_priorities : transitive_job_priorities JLFP.

  (** The adapter preserves transitivity. *)
  Fact tiebreaks_by_id_is_transitive : transitive_job_priorities tiebreaks_by_id.
  Proof.
    move=> y x z; rewrite !tiebreaks_by_id_hep_job => /andP [XY TBXY] /andP [YZ TBYZ].
    apply/andP; split; first exact: (H_transitive_priorities y).
    case ZX: (primary_hep_job z x); last by rewrite /=.
    move: TBXY TBYZ.
    rewrite /primary_hep_job (H_transitive_priorities z y x YZ ZX)
            (H_transitive_priorities x z y ZX XY) /=.
    by lia.
  Qed.

  (** Assume the supplied policy can compare every pair of jobs. *)
  Hypothesis H_total_priorities : total_job_priorities JLFP.

  (** The adapter preserves totality. *)
  Fact tiebreaks_by_id_is_total : total_job_priorities tiebreaks_by_id.
  Proof.
    move=> x y; rewrite !tiebreaks_by_id_hep_job.
    case XY: (primary_hep_job x y); case YX: (primary_hep_job y x) => //=.
    - by lia.
    - rewrite /primary_hep_job in XY YX.
      by move: (H_total_priorities x y); rewrite XY YX.
  Qed.

End TiebreaksById.

(** We register the priority properties for automatic use in proofs. *)
Global Hint Resolve
  tiebreaks_by_id_is_reflexive
  tiebreaks_by_id_is_transitive
  tiebreaks_by_id_is_total
  tiebreaks_by_id_is_antisymmetric
  : basic_rt_facts.
